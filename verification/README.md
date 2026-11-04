# Verification

The executed [`verification.ipynb`](verification.ipynb) is the source notebook.
It defines its data and calculations directly, imports no companion files, and
reads no saved certificates. Open it in Jupyter and run the cells in order.
Mathematical outputs use the manuscript's notation and native Jupyter LaTeX.

## Run the checks

From the repository root:

```sh
python3 verification/verify.py
python3 -m venv .venv
.venv/bin/python -m pip install -r verification/requirements-notebook.txt
BFGS_PYTHON=.venv/bin/python ./scripts/check.sh --python-only
```

`verify.py` independently checks the finite inequalities with exact rational
arithmetic and outward interval bounds, using only the Python standard library.
`symbolic_cycle.py` independently verifies the exact cycle identities with
SymPy, checking the original divisors before cancelling rational expressions.
Neither verifier writes generated output files. Do not use Python's `-O` option.

The complete check executes the existing notebook in a fresh kernel and empty
working directory, compares its saved mathematical outputs with the fresh
outputs, and runs the arithmetic, failure-mode, and cross-verifier tests.
Environment/version strings and execution timings are excluded from output
comparison. Kernel startup uses local loopback ports; the calculations require
no network access.

After editing the notebook, refresh its outputs with
`.venv/bin/python verification/check_notebook.py --write`, then rerun the complete
check. This small runner executes the notebook; it does not generate its cells.

## Correspondence with the manuscript

| Notebook section | Manuscript |
|---|---|
| 1. Data and isolated root | Section 2.1; Lemma 2.4; root enclosure (A.2) |
| 2. Exact cycle identities | Lemma 2.5, equations (2.17)–(2.18) |
| 3. Geometry, interpolation data and line-search margins | Propositions 2.7–2.9; Tables 1–2 |
| 4. A concrete polynomial realization | Lemmas 2.6 and 2.10 |
| 5. Contraction toward the fixed ray | Proposition A.1; Lemma 2.12 |

Root endpoint signs and a positive derivative bound on the same interval certify
Lemma 2.4 directly. Interval calculations use rational endpoints rounded outward
to the grid `2^-256`. The interpolation tables, bridge indices, matrix Γ, and
row sums are computed from the defining data; saved outputs are never inputs.

The supplement explicitly constructs a piecewise-polynomial interpolant for the
single function `h`. Its seven bridges match the prescribed values and first two
derivatives and satisfy `h' >= 0.01`. The manuscript instead invokes the existence
result in C. Manni, *On shape preserving C² Hermite interpolation*, BIT Numerical
Mathematics 41(1), 127–148 (2001). The explicit construction realizes the same
cycle and supports the accompanying numerical figures.

The Python checks certify finite inequalities and verify symbolic identities;
they do not replace the manuscript's analytical arguments. The
[Lean proof guide](../docs/lean.md) and [correspondence guide](../docs/manuscript-map.md)
explain how the formalization proves the main theorem, including the connection
between its arithmetic certificates and the actual BFGS dynamics.
