# Python and notebook verification

This directory contains the exact arithmetic verifier, an independent symbolic
cycle check, and a self-contained executed Jupyter notebook for the BFGS
counterexample. The [repository README](../README.md) describes the mathematical
result and the accompanying Lean verification.

## Quick checks

From the repository root, run:

```sh
python3 verification/verify.py
python3 verification/test_verifier.py
```

These commands require only Python's standard library. The verifier performs
137 named exact checks and writes `certificate.json`, `bounds.txt`, and
`certified_bounds.tex` beside its source. The TeX macros contain the published
interpolation tables and contraction certificate as reference output; the
manuscript contains these values directly and does not input this file.
The ten regression tests
check interval containment, unsafe inputs, exact algebraic arithmetic, altered
root and stability data, polynomial bridge selection, and the full certificate.
Do not run the verifier with Python's `-O` option; it explicitly rejects
optimized execution.

The scripts also work from another working directory when their paths are
specified correctly. From this directory, for example, use `python3 verify.py`.
The calculations require no figures, simulation scripts, or files outside
this directory. The [manuscript](../BFGS%20can%20converge%20to%20non-Clarke-stationary%20points%20with%20positive%20probability.pdf) is included for reference.

## Notebook and all regression tests

The notebook and its builder have optional dependencies. The direct dependency
versions in `requirements-notebook.txt` were tested together with Python 3.12.14.
From the repository root:

```sh
python3 -m venv .venv
.venv/bin/python -m pip install -r verification/requirements-notebook.txt
.venv/bin/python -m unittest discover -s verification -p 'test_*.py' -v
.venv/bin/python verification/build_notebook.py
```

With these dependencies installed, the regression suite contains 22 tests.
Without the optional packages, the corresponding symbolic and notebook tests
are skipped. `requirements-symbolic.txt` installs only the dependency needed
for the independent symbolic cycle checker.

`verification.ipynb` is self-contained: copy it elsewhere and execute its cells
in order after installing the dependencies. Its cells import only the standard
library and installed third-party packages; they neither import companion
project modules nor read project files or saved results. The builder starts a
fresh Jupyter kernel with its own interpreter and an empty working directory,
executes all six code cells, rejects execution errors, and updates the notebook
and `verification.html`. Jupyter kernel startup needs permission to bind local
loopback ports. The mathematical calculations need no network access.

The notebook stores mathematical outputs in native Jupyter LaTeX format:
`Math` for formulas and matrices, and `Latex` for tables. Jupyter and GitHub can
therefore render the mathematics directly. The HTML exporter converts those
same saved LaTeX outputs to offline native MathML, without remote scripts or
assets. The data definitions and symbolic
checks are expanded by default. Tables and formulas use the manuscript's
notation, including superscripts for iterations, `A` and `W` in sans serif for
the line-search margins, and `Gamma` for the published entry bounds. Each
section identifies the corresponding manuscript result by its number and
the relevant equation numbers. Neither the notebook nor the standalone
verifier uses a saved certificate as numerical input.

The notebook sections correspond to the manuscript as follows:

| Notebook section | Manuscript reference |
| --- | --- |
| 1. Data and isolated root | Section 2.1; Lemma 2.3; equation (A.3) |
| 2. Exact cycle identities | Lemma 2.5, equations (2.11)–(2.12) |
| 3. Geometry, interpolation data and line-search margins | Propositions 2.7–2.9; Tables 1–2 in Appendix A.1 |
| 4. A concrete polynomial realization | A realization satisfying Lemmas 2.6 and 2.10 |
| 5. Contraction toward the fixed ray | Proposition A.1, equations (A.4)–(A.12); used in Lemma 2.12 |

## What is certified

The scalar parameter is the root of

```text
777924 b^4 - 576632 b^3 - 587665 b^2 + 352256 b + 65536 = 0
```

in `(0.9178, 0.9179)`. Exact bisection computes the refined interval used for
the contraction and polynomial bridge checks; the notebook displays its endpoints.

The verifier performs five groups of checks (see also the
[manuscript correspondence](../docs/manuscript-map.md)):

1. Exact endpoint signs and a derivative bound isolate the scalar root.
2. Arithmetic modulo the quartic verifies the four position recurrences,
   four BFGS updates, four curvature formulas, and two return identities.
   Algebraic inverses are checked exactly; numerical residual tolerances are
   not used.
3. Outward intervals on `[0.9178, 0.9179]` bound the position norms, signs,
   interpolation data, and line-search margins. Strict comparisons use exact
   rational endpoints, and all displayed decimal endpoints are rounded outward.
4. The polynomial bridge construction in notebook Section 4 specifies one
   concrete interpolant satisfying the manuscript's existence lemma. With
   `m=0.01`, it computes the least index for every gap in the positive and
   negative branches. Extra identity data at `-2` and `7` surround
   the anchors at `-1` and `6`. The verifier certifies every selected index and
   excludes every smaller one by a failed inequality. This construction is an
   explicit alternative to the manuscript's interpolation existence argument;
   its extra checks identify the realization used in the numerical illustrations
   and Lean proof.
5. Differentiation of the five-dimensional BFGS update, four-step composition,
   and transverse projection give an interval matrix enclosure. The published
   absolute-entry bounds and their row sums are computed, proving the
   stated contraction bound `0.78`. The expanded and factorized differentiation
   formulas are also compared exactly modulo the quartic.

The realization permits arbitrary real Hessian coefficients. These certificates
use `(1.9, 1.6, -4.1, 0.2)`, the choice made for transverse contraction. Position,
value, first-derivative, and line-search data do not depend on that choice.
The final coercive objective is
`f(x)=f_tilde(x)+max(0,||x||^2-100)` and is locally Lipschitz; no numerical global
Lipschitz constant for this extension is asserted.

## Agreement between the notebook and published bounds

The notebook computes both interpolation tables directly on the coarse interval
`[0.9178, 0.9179]`. It evaluates the defining expressions and rounds each lower
endpoint down and each upper endpoint up to four decimal places. No stored
table entries are inputs to this calculation. The regression tests compare the
computed intervals with the independent standalone verifier, check the nearest
outward four-decimal rounding, and compare the resulting tables with the
generated manuscript values.

For the subsequent calculations, the notebook computes the refined root
interval by exact bisection on an eleven-decimal grid. It evaluates the rational
formulas of Appendix A.2 directly on that interval, computes each matrix-entry
magnitude, and rounds upward to three decimal places to form `Gamma`. Row sums
and the determinant of `S` are also computed. No root endpoints, output matrix,
row sums or determinant are supplied as results to be reproduced; only the
problem data, precision settings and mathematical comparison targets are inputs.
The calculated maximum row sum is checked against the theorem's threshold `0.78`.

`test_notebook_consistency.py` checks that the saved notebook matches its builder,
executes the generated cells in an empty directory, compares the computed
notebook tables and matrix with freshly generated standalone certificates, and
rejects altered bounds that are too small. These external regression tests may
read repository files; the notebook itself remains self-contained.

## Independent symbolic cycle check

With the optional SymPy dependency installed, run from the repository root:

```sh
.venv/bin/python verification/symbolic_cycle.py
.venv/bin/python verification/test_symbolic_cycle.py
```

The symbolic checker independently reconstructs the cycle. It proves the
fourteen displayed identities by exact polynomial division: each residual
numerator has zero remainder modulo the quartic, and denominator gcds establish
nonvanishing at its roots. Seven original divisor checks are performed before
cancellation. Use `--json` to inspect the entrywise remainders and divisor checks.

These symbolic checks establish identities and nonvanishing, not inequalities.
The interval calculations provide the finite inequality certificates. The
manuscript supplies the analytical arguments, and the Lean development supplies
separate kernel-checked verification; see the repository README for its scope
and build instructions.

## Files and computational assumptions

- `verify.py`, `intervals.py`, `polynomial.py`: standard-library exact verifier.
- `symbolic_cycle.py`: independent SymPy cycle check.
- `build_notebook.py`: constructs, executes, and exports the notebook.
- `verification.ipynb`, `verification.html`: executed, readable verification.
- `certificate.json`, `bounds.txt`, `certified_bounds.tex`: generated certificates.
- `test_*.py`: the 22 regression tests.
- `requirements*.txt`: optional direct dependency versions.

For the Python calculations, the interpreter, exact-arithmetic implementation,
and transcription of the mathematical expressions are part of the computational
trust boundary. The checks use exact fractions and outward dyadic intervals
with denominator `2^256`; no binary floating-point comparison decides a
mathematical certificate. Lean verification is complementary and is not replaced
by a successful Python run.
