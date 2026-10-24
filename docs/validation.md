# Validation of this bundle

Validated on 24 October 2026 with Lean 4.33.1 and Python 3.12.14.
The included [manuscript](../manuscript/main.pdf) and
[manuscript map](manuscript-map.md) provide the numbered result correspondence.

## Lean build and axiom audit

The full `lake build BFGS --wfail` completed successfully (8,792 build jobs).
The bundle contains 87 local Lean modules: 63 construction/public modules and
24 reusable modules. Every source is in the public theorem's import closure;
obsolete numerical certificates and the former chart-basin proof were removed.
The final proof uses the manuscript's fixed normalization by r and establishes
convergence of normalized states to a positive point on the fixed ray.

The following `verification/check_lean.py --incremental` audit also passed:

- 17,604 declarations checked, including 147 private names.
- Only `propext`, `Classical.choice`, and `Quot.sound` as transitive axioms.
- Both `BFGS.Counterexample.concrete_counterexample` and
  `BFGS.Counterexample.main_theorem` pass the statement and axiom checks.
- The freshness check reused all 87 compiled modules before rerunning the axiom audit.

All nine dependency revisions were checked against `lake-manifest.json`.
Their local caches are independent physical copies, with no shared dependency
symlinks. No Lean source changed after the final audit. The actual, unfiltered
[Lean transcript](lean-validation.txt) includes informational tactic suggestions
but no build errors or warnings.

## Python and notebook

The complete Python workflow executes the six self-contained notebook code
cells in a fresh kernel with an empty working directory and runs the 22-test
regression suite. The exact verifier passes 137 named checks. Formula, matrix, and table
outputs use native LaTeX; the HTML export renders these saved outputs offline.
See the [Python transcript](python-validation.txt) for the executed tests.

All displayed numerical results are computed from the problem data. This
includes decimal-grid root isolation, the interpolation tables, the determinant
of S, the matrix Γ and its row sums, and the least admissible polynomial bridge
indices. Bounds are rounded outward. The code contains the construction data,
precision choices, and mathematical claims being checked, rather than supplied
numerical outputs to reproduce.

The notebook and standalone verifier agree on both interpolation tables,
the refined root interval, Γ, and the row sums. These computed bounds agree
with the included manuscript.

## Regeneration and packaging

In a disposable directory, the optional generators independently recreated
3,216 arithmetic nodes in 36 trace modules, the interval-bound module, and its
metadata: all 38 generated files are byte-identical to the bundled files.
This remains true after replacing preset bridge indices and output bounds
with computations. Generated certificates and logs are review artifacts, not
assumptions of the Lean proof.

The SHA-256 digest of the sorted concatenation of each Lean file's relative
path, a NUL byte, its hexadecimal SHA-256 digest, and a newline is:

```text
fc041630e8c1559d4adf7da897cfd57e24e62c7a6df895e189b1ffdb3a5cfe8b
```

Documentation file links, shell syntax, source hygiene, and the public import
closure were checked. Build caches, virtual environments, compiled binaries,
and notebook checkpoints are excluded by `.gitignore`. The executed notebook,
its offline HTML export, and generated certificates are retained for readers.

GitHub Actions is configured to repeat the Python and Lean checks. The
transcripts above record the local validation runs.
