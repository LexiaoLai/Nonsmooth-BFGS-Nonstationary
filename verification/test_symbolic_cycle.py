#!/usr/bin/env python3
"""Regression tests that require optional requirements-symbolic.txt."""

from pathlib import Path
import json
import subprocess
import sys
import tempfile
import unittest

try:
    from sympy import Float, cancel
    from symbolic_cycle import P, SymbolicChecks, b, build_data, verify_cycle
    SYMBOLIC_AVAILABLE = True
except ModuleNotFoundError as error:
    if error.name != "sympy":
        raise
    SYMBOLIC_AVAILABLE = False


@unittest.skipUnless(SYMBOLIC_AVAILABLE, "install optional requirements-symbolic.txt")
class SymbolicCycleTests(unittest.TestCase):
    def test_changed_H1_is_rejected(self):
        data = build_data()
        data.H[1][0, 0] += 1
        with self.assertRaisesRegex(ArithmeticError, "cycle.update.0"):
            verify_cycle(data)

    def test_changed_position_is_rejected(self):
        data = build_data()
        data.x[1][0] += 1
        with self.assertRaisesRegex(ArithmeticError, "cycle.position.0"):
            verify_cycle(data)

    def test_zero_curvature_is_rejected_before_update_division(self):
        data = build_data()
        data.H[0][0, 1] = data.H[0][1, 0] = 1
        with self.assertRaisesRegex(ArithmeticError, "curvature.0"):
            verify_cycle(data)

    def test_original_divisor_rejects_a_hidden_cancelled_pole(self):
        checks = SymbolicChecks()
        original_divisor = P.as_expr()
        # Cancellation alone would accept this residual at the roots of P.
        checks.equal("cancelled_residual", cancel(b*original_divisor/original_divisor)-b)
        with self.assertRaisesRegex(ArithmeticError, "original_divisor"):
            checks.nonzero("original_divisor", original_divisor)

    def test_uncancelled_pole_and_float_are_rejected(self):
        with self.assertRaisesRegex(ArithmeticError, "undefined"):
            SymbolicChecks().equal("pole", 1/P.as_expr())
        with self.assertRaises(TypeError):
            SymbolicChecks().equal("approximate", Float("0.1"))

    def test_cli_certifies_named_identities_without_writing_files(self):
        script = Path(__file__).with_name("symbolic_cycle.py")
        with tempfile.TemporaryDirectory() as directory:
            result = subprocess.run([sys.executable, str(script), "--json"], cwd=directory,
                                    capture_output=True, text=True, check=False)
            self.assertEqual(result.returncode, 0, msg=result.stderr)
            self.assertEqual(list(Path(directory).iterdir()), [])
            certificate = json.loads(result.stdout)
        identities = {
            f"cycle.{kind}.{i}"
            for kind in ("position", "update", "curvature") for i in range(4)
        } | {"cycle.return_metric", "cycle.return_position"}
        divisors = {"b", "2b-1", "1-r"} | {f"curvature.{i}" for i in range(4)}
        self.assertEqual(certificate["status"], "passed")
        self.assertEqual(set(certificate["residuals"]), identities)
        self.assertEqual(set(certificate["nonzero_checks"]), divisors)
        self.assertEqual(set(certificate["checks"]),
                         identities | {"nonzero." + name for name in divisors})
        for record in certificate["residuals"].values():
            self.assertTrue(all(value == "0" for row in record["numerator_remainders"] for value in row))
            self.assertTrue(all(value == "1" for row in record["denominator_gcds"] for value in row))
        for record in certificate["nonzero_checks"].values():
            self.assertEqual(record["numerator_gcd"], "1")
            self.assertEqual(record["denominator_gcd"], "1")


if __name__ == "__main__":
    unittest.main()
