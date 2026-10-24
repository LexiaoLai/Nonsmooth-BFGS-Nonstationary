#!/usr/bin/env python3
"""Independent SymPy checks of Lemma 2.5, equations (2.11)--(2.12).

Every residual is a rational function in the indeterminate b. Its numerator
is reduced modulo the quartic P over QQ; its denominator must be coprime to P.
Original divisors are checked separately, before cancellations can hide them.
Thus the identities hold at every root of P, without selecting an approximate
root. Positivity, root isolation, norm bounds, and attraction are certified by
the separate standard-library interval verifier, verify.py.

Run this file from any working directory. It prints to stdout and writes no
certificate files. Install the optional requirements-symbolic.txt first.
"""

from argparse import ArgumentParser
from dataclasses import dataclass
import json

from sympy import Float, Matrix, Poly, QQ, Rational, Symbol, cancel, eye, sympify
from sympy.matrices import MatrixBase


b = Symbol("b")
P = Poly(777924*b**4 - 576632*b**3 - 587665*b**2 + 352256*b + 65536,
         b, domain=QQ)


def rational_matrix(matrix):
    """Cancel rational functions entrywise, without reducing modulo P."""
    return matrix.applyfunc(cancel)


def scalar(left, right):
    return (left.T * right)[0]


@dataclass
class CycleData:
    """Explicit data from the manuscript, also accepted from the notebook."""

    rho: object
    r: object
    p: object
    t: object
    q: object
    J: MatrixBase
    g: list
    H: list
    x: list


def build_data():
    """Construct the data independently of verify.py and polynomial.py."""
    rho = Rational(8, 9)
    r = rho**2
    p = -9*(882*b**2 - 463*b - 256)/(640*(2*b - 1))
    t = -(3087*b**2 - 2233*b - 256)/(320*(2*b - 1))
    q = (15876*b**3 - 4316*b**2 - 6815*b - 2304)/(1280*b*(2*b - 1))
    J = Matrix([[p, t], [q, -p]])
    e1, e2 = Matrix([1, 0]), Matrix([0, 1])
    g = [e1, e2, J*e1, J*e2, e1]
    H0 = Matrix([[1, Rational(1, 2)],
                 [Rational(1, 2), b/4 + Rational(1, 8)]])
    H1 = Matrix([[b + Rational(3, 2), b + Rational(1, 2)],
                 [b + Rational(1, 2), b]])
    H = [H0, H1, rational_matrix(rho*J.T*H0*J),
         rational_matrix(rho*J.T*H1*J), r*H0]
    v0 = Matrix([b + Rational(3, 2), b + Rational(1, 2)])
    x0 = rational_matrix((eye(2) + rho*J.T)*v0/(1-r))
    x1 = x0 - Matrix([1, Rational(1, 2)])
    x = [x0, x1, rational_matrix(rho*J.T*x0),
         rational_matrix(rho*J.T*x1), r*x0]
    return CycleData(rho=rho, r=r, p=p, t=t, q=q, J=J, g=g, H=H, x=x)


class SymbolicChecks:
    """Exact zero and nonzero certificates over QQ[b], with explicit failures."""

    def __init__(self, modulus=P):
        self.modulus = Poly(modulus, b, domain=QQ)
        if self.modulus.degree() < 1:
            raise ValueError("The modulus must be a nonconstant polynomial in b.")
        self.residuals = {}
        self.nonzero_checks = {}
        self.checks = []

    def parts(self, expression):
        expression = sympify(expression)
        if expression.has(Float):
            raise TypeError("Symbolic certificates require exact rational input, not Float.")
        numerator, denominator = cancel(expression).as_numer_denom()
        return (Poly(numerator, b, domain=QQ), Poly(denominator, b, domain=QQ))

    def nonzero(self, name, expression):
        """Check a divisor itself, including its own denominator, at all roots."""
        numerator, denominator = self.parts(expression)
        numerator_gcd = numerator.gcd(self.modulus).monic()
        denominator_gcd = denominator.gcd(self.modulus).monic()
        if numerator_gcd.degree() != 0 or denominator_gcd.degree() != 0:
            raise ArithmeticError(f"{name}: divisor is zero or undefined at a root of P")
        self.nonzero_checks[name] = {
            "expression": str(expression),
            "numerator_gcd": str(numerator_gcd.as_expr()),
            "denominator_gcd": str(denominator_gcd.as_expr()),
            "nonzero": True,
        }
        self.checks.append("nonzero." + name)

    def equal(self, name, residual, rational_identity=False):
        """Certify an entrywise equality, optionally even before imposing P=0."""
        matrix = residual if isinstance(residual, MatrixBase) else Matrix([residual])
        remainders, denominator_gcds = [], []
        for row in range(matrix.rows):
            remainder_row, gcd_row = [], []
            for column in range(matrix.cols):
                numerator, denominator = self.parts(matrix[row, column])
                denominator_gcd = denominator.gcd(self.modulus).monic()
                if denominator_gcd.degree() != 0:
                    raise ArithmeticError(f"{name}[{row},{column}]: undefined at a root of P")
                remainder = numerator.rem(self.modulus)
                if not remainder.is_zero:
                    raise ArithmeticError(
                        f"{name}[{row},{column}]: nonzero residual; "
                        f"numerator remainder = {remainder.as_expr()}")
                if rational_identity and not numerator.is_zero:
                    raise ArithmeticError(
                        f"{name}[{row},{column}]: expected an identity before imposing P=0; "
                        f"numerator = {numerator.as_expr()}")
                remainder_row.append(str(remainder.as_expr()))
                gcd_row.append(str(denominator_gcd.as_expr()))
            remainders.append(remainder_row)
            denominator_gcds.append(gcd_row)
        self.residuals[name] = {
            "shape": [matrix.rows, matrix.cols],
            "numerator_remainders": remainders,
            "denominator_gcds": denominator_gcds,
            "rational_identity": rational_identity,
        }
        self.checks.append(name)

    def result(self):
        return {
            "status": "passed",
            "arithmetic": "SymPy Matrix/Rational and polynomial arithmetic over QQ",
            "method": "Numerator remainders modulo P; polynomial gcd checks for divisors",
            "polynomial": str(self.modulus.as_expr()),
            "scope": ("Algebraic cycle identities only. Root isolation, positivity, norm "
                      "bounds, and attraction are checked separately by verify.py."),
            "checks": list(self.checks),
            "residuals": self.residuals,
            "nonzero_checks": self.nonzero_checks,
        }


def bfgs(H, s, y):
    """The manuscript's factorized inverse-BFGS formula, as a rational matrix.

    The caller must certify s.T*y nonzero before calling this function.
    """
    curvature = cancel(scalar(s, y))
    V = rational_matrix(eye(2) - s*y.T/curvature)
    return rational_matrix(V*H*V.T + s*s.T/curvature)


def verify_cycle(data=None, modulus=P):
    """Check the 14 displayed conclusions and their seven necessary divisors.

    Passing CycleData allows a notebook to spell out every definition visibly
    and submit those very matrices for checking. No numerical root is used.
    """
    data = build_data() if data is None else data
    r, g, H, x = data.r, data.g, data.H, data.x
    if not (len(g) == len(H) == len(x) == 5):
        raise ValueError("Exactly five gradients, metrics, and positions are required.")
    checks = SymbolicChecks(modulus)

    # All nonconstant factors of the ORIGINAL definition denominators occur
    # here. Checking only simplified zero residuals could hide cancelled poles.
    for name, divisor in {"b": b, "2b-1": 2*b-1, "1-r": 1-r}.items():
        checks.nonzero(name, divisor)
    s = [rational_matrix(-H[i]*g[i]) for i in range(4)]
    y = [rational_matrix(g[i+1]-g[i]) for i in range(4)]
    curvatures = [cancel(scalar(s[i], y[i])) for i in range(4)]
    for i, curvature in enumerate(curvatures):
        checks.nonzero(f"curvature.{i}", curvature)

    expected_curvatures = [Rational(1, 2), Rational(81, 32)*b,
                           Rational(4, 9), Rational(9, 4)*b]
    for i in range(4):
        checks.equal(f"cycle.position.{i}", x[i]+s[i]-x[i+1])
        checks.equal(f"cycle.update.{i}", bfgs(H[i], s[i], y[i])-H[i+1])
        checks.equal(f"cycle.curvature.{i}", curvatures[i]-expected_curvatures[i])
    checks.equal("cycle.return_metric", H[4]-r*H[0])
    checks.equal("cycle.return_position", x[4]-r*x[0])
    return checks.result()


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true", help="print all exact certificate records")
    args = parser.parse_args()
    result = verify_cycle()
    if args.json:
        print(json.dumps(result, indent=2))
    else:
        print(f"All {len(result['checks'])} symbolic checks passed.")
        print(f"{len(result['residuals'])} scalar/matrix identities have zero numerator remainders modulo P.")
        print(f"{len(result['nonzero_checks'])} original divisors are coprime to P.")
        print(result["scope"])


if __name__ == "__main__":
    main()
