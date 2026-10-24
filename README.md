# BFGS can converge to non-Clarke-stationary points with positive probability

Verification supplement for:

> Lexiao Lai. [*BFGS can converge to non-Clarke-stationary points with positive probability*](BFGS%20can%20converge%20to%20non-Clarke-stationary%20points%20with%20positive%20probability.pdf). Manuscript, 2026.

This repository contains the manuscript, the Lean proof, and the self-contained Python notebook
for a coercive, locally Lipschitz, semialgebraic objective on R² for which BFGS
converges to a non-Clarke-stationary point from an open set of initial states.
The result covers every Armijo–Wolfe parameter pair
`0 < c₁ ≤ 0.03` and `0.6 ≤ c₂ < 1` on the same open set, and gives positive
failure probability under the Gaussian/Wishart initialization law.

## Start here

- [Manuscript PDF](BFGS%20can%20converge%20to%20non-Clarke-stationary%20points%20with%20positive%20probability.pdf).
- [Executed notebook](verification/verification.ipynb): exact cycle identities,
  interval bounds, and the published tables and contraction certificate.
- [Offline HTML notebook](verification/verification.html): download and open
  locally to read the executed cells without Jupyter.
- [Lean main theorem](BFGS/MainTheorem.lean): the statement corresponding to Theorem 1.1.
- [Manuscript correspondence](docs/manuscript-map.md): section, result, and equation
  numbers linked to the Python checks and Lean declarations.
- [Lean proof guide](docs/lean.md): definitions, proof organization, and trust boundary.
- [Figure reproduction](experiments/README.md): numerical objective and scripts for Figures 1–2.

The notebook uses exact rational arithmetic and outward interval bounds. The
Lean proof independently checks the arithmetic and its connection to the
actual BFGS dynamics. Its final theorems have no unproved hypotheses. The
axiom audit permits only `propext`, `Classical.choice`, and `Quot.sound`.

## Python verification

The standalone verifier needs only Python 3.12 and its standard library:

```sh
python3 verification/verify.py
python3 verification/test_verifier.py
```

For the notebook, symbolic checks, and the complete regression suite:

```sh
python3 -m venv .venv
.venv/bin/python -m pip install -r verification/requirements-notebook.txt
BFGS_PYTHON=.venv/bin/python ./scripts/check.sh --python-only
```

This executes all six notebook cells in a fresh Jupyter kernel with an empty
working directory, exports the offline HTML, and runs the tests. The notebook
can also be copied elsewhere and executed by itself: it reads no companion
source files or saved certificates. See [verification details](verification/README.md).

## Lean verification

Install [elan](https://github.com/leanprover/elan#installation), then run from
this directory:

```sh
lake exe cache get
./scripts/check.sh --lean-only
```

`lean-toolchain` pins Lean 4.33.1. `lake-manifest.json` pins mathlib and all
transitive packages; do not run `lake update` unless deliberately changing
those dependencies. The first command retrieves the corresponding package
cache. The check script builds the local library with warnings treated as
errors and audits the transitive axioms of all local declarations. It needs
Python 3.10 or newer for the audit script.

To use the theorem in another Lean file:

```lean
import BFGS

#check BFGS.Counterexample.main_theorem
#check BFGS.Counterexample.concrete_counterexample
```

After installing both sets of dependencies, run all checks with
`BFGS_PYTHON=.venv/bin/python ./scripts/check.sh`.

## Contents

```text
BFGS.lean                     Public import
BFGS/MainTheorem.lean          Theorem 1.1 and its concrete witness
BFGS/Counterexample/           Construction and its certified inequalities
BFGS/Analysis/                 Supporting analysis and BFGS dynamics
BFGS/Arithmetic/               Exact arithmetic and interval lemmas
verification/                 Executed notebook, Python checks and certificates
experiments/                  Figure-generation scripts and reproduction instructions
docs/manuscript-map.md         Correspondence with manuscript results
scripts/check.sh               Combined Python and Lean checks
lean-toolchain                Pinned Lean version
lakefile.toml                  Standalone Lake project
lake-manifest.json             Pinned dependency revisions
.github/workflows/verify.yml   GitHub Actions checks
```

Only modules in the public theorem's import closure are retained. Generated
certificates are committed for inspection; the verifiers recompute their
contents instead of trusting saved outputs. Build caches and virtual
environments are ignored. The offline HTML is a readable export of the same
executed notebook, not an additional proof source.

The notebook computes the refined root interval, interpolation tables,
determinant, Γ, row sums and polynomial bridge indices from the problem data.
Displayed endpoints are rounded outward and checked against the manuscript.
Its computed maximum row sum is `0.776 < 0.78`. The explicit polynomial interpolation in
the supplement is one realization of Lemmas 2.6 and 2.10. Lean uses the manuscript's fixed normalization by the exact cycle
factor and proves attraction to its positive fixed ray.

See [validation](docs/validation.md) for the checks performed on this bundle.

## License and citation

The original code, notebooks, and accompanying software documentation are
licensed under the [MIT License](LICENSE). This license does not apply to
the [manuscript PDF](BFGS%20can%20converge%20to%20non-Clarke-stationary%20points%20with%20positive%20probability.pdf), whose rights remain with the author.
Third-party dependencies retain their respective licenses.
Citation metadata for the verification supplement is in [CITATION.cff](CITATION.cff).
