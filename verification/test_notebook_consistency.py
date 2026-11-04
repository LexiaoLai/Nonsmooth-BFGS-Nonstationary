#!/usr/bin/env python3
"""Check the self-contained notebook against the manuscript exact certificates.

Requires the optional requirements-notebook.txt dependencies. These checks run
outside the notebook; the notebook itself reads no companion source or data.
"""

import ast
import contextlib
import copy
from fractions import Fraction as F
import io
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import verify

try:
    import nbformat
    import check_notebook
    import IPython.display
    import sympy
    NOTEBOOK_AVAILABLE = True
except ModuleNotFoundError as error:
    if error.name == "check_notebook":
        raise
    NOTEBOOK_AVAILABLE = False


HERE = Path(__file__).resolve().parent


@unittest.skipUnless(NOTEBOOK_AVAILABLE, "install optional requirements-notebook.txt")
class NotebookConsistencyTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.notebook = nbformat.read(HERE / "verification.ipynb", as_version=4)
        check_notebook.validate_sources(cls.notebook)
        cls.code = [cell.source for cell in cls.notebook.cells
                    if cell.cell_type == "code"]
        cls.namespace = {"__name__": "notebook_consistency_check"}
        previous_directory = Path.cwd()
        with tempfile.TemporaryDirectory(prefix="bfgs-notebook-test-") as directory:
            try:
                os.chdir(directory)
                with contextlib.redirect_stdout(io.StringIO()), \
                        contextlib.redirect_stderr(io.StringIO()), \
                        patch("IPython.display.display"):
                    for source in cls.code:
                        exec(compile(source, "<self-contained notebook>", "exec"),
                             cls.namespace)
                if list(Path(directory).iterdir()):
                    raise AssertionError("Notebook wrote files in its empty working directory")
            finally:
                os.chdir(previous_directory)

        cls.certificate = verify.verify()

    def test_notebook_has_successful_latex_outputs_and_result_references(self):
        saved = self.notebook
        code_cells = [cell for cell in saved["cells"] if cell["cell_type"] == "code"]
        self.assertEqual(len(code_cells), 6)
        self.assertEqual([cell["execution_count"] for cell in code_cells], list(range(1, 7)))
        self.assertFalse(any(output["output_type"] == "error"
                             for cell in code_cells for output in cell["outputs"]))
        prose = "\n".join(cell.source for cell in self.notebook.cells
                          if cell.cell_type == "markdown")
        for reference in ["Lemma 2.4", "Lemma 2.5", "Propositions 2.7–2.9",
                          "Lemma 2.6", "Lemma 2.10", "Proposition A.1",
                          "(A.11)", "(A.12)"]:
            self.assertIn(reference, prose)
        self.assertNotRegex(prose, r"\b(?:lem|prop|eq|sec|app|tab):")
        native_latex = ["".join(output.get("data", {}).get("text/latex", []))
                        for cell in code_cells for output in cell["outputs"]
                        if "text/latex" in output.get("data", {})]
        self.assertTrue(native_latex, "Mathematical outputs must use native Jupyter LaTeX")
        rendered = "\n".join(native_latex)
        for expression in [r"\Gamma=", r"\|SAS^{-1}\|_\infty", r"\mathsf A^i", r"\begin{array}"]:
            self.assertIn(expression, rendered)
        self.assertFalse(any("text/html" in output.get("data", {})
                             for cell in code_cells for output in cell["outputs"]))

    def test_stale_saved_mathematical_output_is_rejected(self):
        changed = copy.deepcopy(self.notebook)
        for cell in changed.cells:
            for output in cell.get("outputs", []):
                if "text/latex" in output.get("data", {}):
                    output.data["text/latex"] += " incorrect output"
                    with self.assertRaisesRegex(ValueError, "stale"):
                        check_notebook.check_saved_outputs(changed, self.notebook)
                    return
        self.fail("Notebook contains no mathematical output to check")

    def test_root_certificate_uses_the_manuscript_interval(self):
        root = self.certificate["root"]
        a, c = root["narrow"]
        self.assertEqual([self.namespace["root_lo"], self.namespace["root_hi"]], [a, c])
        self.assertEqual(self.namespace["endpoint_values"], root["narrow_values"])
        self.assertLess(root["narrow_values"][0], 0)
        self.assertGreater(root["narrow_values"][1], 0)
        # The manuscript's a,c are the certified endpoints, not the search bracket.
        derivative_lower = 3111696*a**3 - 1729896*c**2 - 1175330*c + 352256
        self.assertEqual(root["derivative_lower"], derivative_lower)
        self.assertEqual(self.namespace["derivative_lower"], derivative_lower)
        self.assertGreater(derivative_lower, 200000)
        self.assertLess(root["coarse"][0], a)
        self.assertLess(a, c)
        self.assertLess(c, root["coarse"][1])

    def test_computed_gamma_matches_independent_verifier(self):
        gamma = self.namespace["Gamma"]
        rows = self.namespace["rows"]
        stability = self.certificate["stability"]
        self.assertEqual(gamma, stability["magnitude"])
        self.assertEqual(rows, stability["rows"])
        for interval_row, rounded_row in zip(self.namespace["transformed"], gamma):
            for interval, rounded in zip(interval_row, rounded_row):
                magnitude = max(abs(interval.lo), abs(interval.hi))
                self.assertLessEqual(magnitude, rounded)
                self.assertLess(rounded - F(1, 1000), magnitude)
        self.assertEqual(rows, [sum(row) for row in gamma])
        self.assertLess(max(rows), F("0.78"))
        self.assertEqual([self.namespace["root_lo"], self.namespace["root_hi"]],
                         self.certificate["root"]["narrow"])

    def test_computed_tables_match_independent_verifier(self):
        for variable, interval_variable, fields, certificate_key, shape in [
                ("node_bounds", "nodes", ("t", "eta", "d"), "nodes", (4, 3)),
                ("gap_bounds", "gaps", ("length", "secant"), "gaps", (5, 2))]:
            with self.subTest(table=variable):
                table = self.namespace[variable]
                intervals = self.namespace[interval_variable]
                independent = self.certificate["geometry"][certificate_key]
                self.assertEqual(len(table), shape[0])
                self.assertTrue(all(len(row) == shape[1] for row in table))
                for bounds, local_row, independent_row in zip(table, intervals, independent):
                    for (lower, upper), field in zip(bounds, fields):
                        value = local_row[field]
                        other = independent_row[field]
                        self.assertEqual((value.lo, value.hi), (other.lo, other.hi))
                        lower, upper = F(lower), F(upper)
                        # The nearest outward four-decimal endpoints, checked
                        # without calling the notebook's rounding routine.
                        self.assertLessEqual(lower, value.lo)
                        self.assertLess(value.lo, lower + F(1, 10000))
                        self.assertLess(upper - F(1, 10000), value.hi)
                        self.assertLessEqual(value.hi, upper)

    def test_single_interpolant_bridges_match_standalone_certificate(self):
        self.assertEqual(len(self.namespace["interpolation_points"]), 6)
        self.assertEqual(len(self.namespace["extended_points"]), 8)
        local = self.namespace["bridges"]
        independent = self.certificate["bridges"]["gaps"]
        self.assertEqual(len(local), 7)
        for left, right in zip(local, independent):
            self.assertEqual(left["gap"], right["gap"])
            self.assertEqual(left["n"], right["n"])
            self.assertEqual(len(left["rejected"]), left["n"])
            for key in ("L", "R", "remaining"):
                self.assertEqual((left[key].lo, left[key].hi),
                                 (right[key].lo, right[key].hi))
        self.assertTrue(all(value == 0 for value in self.namespace["bridge_residuals"]))

    def test_too_small_manuscript_gamma_is_rejected(self):
        # Corrupt the computed output while retaining the fresh interval data.
        tree = ast.parse(self.code[-1])
        changed = 0
        for statement in tree.body:
            if isinstance(statement, ast.Assign) and any(
                    isinstance(target, ast.Name) and target.id == "Gamma"
                    for target in statement.targets):
                statement.value = ast.parse("[[F(0) for _ in range(4)] for _ in range(4)]",
                                            mode="eval").body
                changed += 1
        self.assertEqual(changed, 1, "Expected one manuscript Gamma assignment")
        with contextlib.redirect_stdout(io.StringIO()), \
                contextlib.redirect_stderr(io.StringIO()), \
                patch("IPython.display.display"), \
                self.assertRaises(ArithmeticError):
            exec(compile(ast.fix_missing_locations(tree), "<invalid Gamma>", "exec"),
                 dict(self.namespace))

    def test_too_small_manuscript_interval_is_rejected(self):
        value = self.namespace["nodes"][0]["t"]
        midpoint = (value.lo + value.hi) / 2
        self.assertLess(value.lo, value.hi)
        with self.assertRaises(ArithmeticError):
            self.namespace["checked_enclosure"](value, str(midpoint), str(midpoint))


if __name__ == "__main__":
    unittest.main()
