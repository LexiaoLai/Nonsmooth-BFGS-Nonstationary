#!/usr/bin/env python3
"""Check the self-contained notebook against the published exact certificates.

Requires the optional requirements-notebook.txt dependencies. These checks run
outside the notebook; the notebook itself reads no companion source or data.
"""

import ast
import contextlib
from fractions import Fraction as F
import io
import json
import os
from pathlib import Path
import re
import tempfile
import unittest
from unittest.mock import patch

import verify

try:
    import build_notebook
    import IPython.display
    import sympy
    NOTEBOOK_AVAILABLE = True
except ModuleNotFoundError as error:
    if error.name == "build_notebook":
        raise
    NOTEBOOK_AVAILABLE = False


HERE = Path(__file__).resolve().parent


def macro_body(source, name):
    """Extract one generated macro, including any nested TeX braces."""
    start = source.index("\\newcommand{\\" + name + "}{")
    start += len("\\newcommand{\\" + name + "}{")
    depth = 1
    for end in range(start, len(source)):
        depth += (source[end] == "{") - (source[end] == "}")
        if depth == 0:
            return source[start:end]
    raise ValueError("Unclosed macro: " + name)


def interval_pairs(source):
    return [tuple(map(F, pair))
            for pair in re.findall(r"\[([^,\]]+),\s*([^\]]+)\]", source)]


@unittest.skipUnless(NOTEBOOK_AVAILABLE, "install optional requirements-notebook.txt")
class NotebookConsistencyTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.notebook = build_notebook.make_notebook()
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
        with tempfile.TemporaryDirectory(prefix="bfgs-generated-bounds-") as directory:
            verify.write_outputs(cls.certificate, directory)
            cls.fresh_tex = (Path(directory) / "certified_bounds.tex").read_text()
        cls.saved_tex = (HERE / "certified_bounds.tex").read_text()

    def test_saved_notebook_has_current_sources_and_successful_outputs(self):
        saved = json.loads((HERE / "verification.ipynb").read_text())
        self.assertEqual(
            [(cell["cell_type"], "".join(cell["source"])) for cell in saved["cells"]],
            [(cell.cell_type, cell.source) for cell in self.notebook.cells])
        code_cells = [cell for cell in saved["cells"] if cell["cell_type"] == "code"]
        self.assertEqual(len(code_cells), 6)
        self.assertEqual([cell["execution_count"] for cell in code_cells], list(range(1, 7)))
        self.assertFalse(any(output["output_type"] == "error"
                             for cell in code_cells for output in cell["outputs"]))
        self.assertTrue(all(cell["id"].startswith("bfgs-verification-")
                            for cell in saved["cells"]))
        prose = "\n".join(cell.source for cell in self.notebook.cells
                          if cell.cell_type == "markdown")
        for reference in ["Lemma 2.3", "Lemma 2.5", "Propositions 2.7–2.9",
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

    def test_computed_gamma_matches_standalone_certificate_and_manuscript(self):
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
        for name in ["BFGSMagnitudeMatrix", "BFGSRowBounds"]:
            self.assertEqual(macro_body(self.saved_tex, name),
                             macro_body(self.fresh_tex, name))
        matrix_numbers = list(map(F, re.findall(
            r"\d+\.\d+", macro_body(self.saved_tex, "BFGSMagnitudeMatrix"))))
        row_numbers = list(map(F, re.findall(
            r"\d+\.\d+", macro_body(self.saved_tex, "BFGSRowBounds"))))
        self.assertEqual(matrix_numbers, [value for row in gamma for value in row])
        self.assertEqual(row_numbers, rows)

    def test_computed_tables_match_generated_manuscript_enclosures(self):
        for variable, interval_variable, fields, certificate_key, macro, shape in [
                ("node_bounds", "coarse_nodes", ("t", "eta", "d"), "nodes", "BFGSNodeRows", (4, 3)),
                ("gap_bounds", "coarse_gaps", ("length", "secant"), "gaps", "BFGSGapRows", (6, 2))]:
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
                expected = [tuple(map(F, pair)) for row in table for pair in row]
                self.assertEqual(expected, interval_pairs(macro_body(self.fresh_tex, macro)))
                self.assertEqual(macro_body(self.saved_tex, macro),
                                 macro_body(self.fresh_tex, macro))
        # The displayed table is generated from the interval input: narrowing
        # that input changes its computed enclosures rather than reusing a table.
        coarse_lo, coarse_hi = self.namespace["coarse_lo"], self.namespace["coarse_hi"]
        narrower = self.namespace["IV"](coarse_lo, (coarse_lo + coarse_hi) / 2)
        nodes, _ = self.namespace["coarse_interpolation_data"](narrower)
        narrowed = self.namespace["rounded_bounds"](nodes[0]["t"])
        self.assertNotEqual(narrowed, self.namespace["node_bounds"][0][0])

    def test_too_small_published_gamma_is_rejected(self):
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
        self.assertEqual(changed, 1, "Expected one published Gamma assignment")
        with contextlib.redirect_stdout(io.StringIO()), \
                contextlib.redirect_stderr(io.StringIO()), \
                patch("IPython.display.display"), \
                self.assertRaises(ArithmeticError):
            exec(compile(ast.fix_missing_locations(tree), "<invalid Gamma>", "exec"),
                 dict(self.namespace))

    def test_too_small_published_interval_is_rejected(self):
        value = self.namespace["nodes"][0]["t"]
        midpoint = (value.lo + value.hi) / 2
        self.assertLess(value.lo, value.hi)
        with self.assertRaises(ArithmeticError):
            self.namespace["checked_enclosure"](value, str(midpoint), str(midpoint))


if __name__ == "__main__":
    unittest.main()
