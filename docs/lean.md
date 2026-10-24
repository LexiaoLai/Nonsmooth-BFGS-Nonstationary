# Lean verification

Start with `import BFGS` and [BFGS/MainTheorem.lean](../BFGS/MainTheorem.lean).
The two public statements are:

- `BFGS.Counterexample.concrete_counterexample`: Theorem 1.1
  for the constructed objective `f`;
- `BFGS.Counterexample.main_theorem`: its existential formulation, including
  the positive-probability conclusion of the following remark.

Both are unconditional theorems. The main file explains the objective, the
state coordinates and the failure predicates before presenting these statements.
The [manuscript map](manuscript-map.md) relates the other modules to the paper.

## Reproduce the proof

Install Lean's `elan` toolchain manager and Python 3.10 or later, then run from
the repository root:

```sh
lake exe cache get
lake build BFGS --wfail
python3 verification/check_lean.py --incremental
```

The committed toolchain selects Lean 4.33.1. The manifest pins mathlib to
`0df444a360eaa60ab8c11dca51a86af692955474` and its transitive packages.
Preserve the manifest; `lake update` is for an intentional dependency change.

The checker validates the local import closure, rejects unimported source
files, compiles stale modules, checks rejection of a false interval bound,
and audits the transitive axioms of every local declaration. It also checks
the exact conjunction of the concrete theorem. Its wrapper uses this
repository's own build and dependency directories and never changes the
manifest or downloads packages.

Omit `--incremental` to rebuild all construction-specific modules. A reusable
module is reused only when its compiled file is newer than its source and
imports. Failed compilations do not replace successful outputs, and source
changes during the audit are rejected. Use `--static-only` for source hygiene
and import closure without compilation or an axiom audit.

## What is proved

The concrete objective is semialgebraic, continuous, locally Lipschitz and
coercive, with compact sublevel sets. Its origin is not Clarke stationary.
One nonempty open set of positive definite initial states has positive mass
under independent standard Gaussian point coordinates and a Wishart inverse-
Hessian estimate. From every state in this set, an infinite BFGS orbit
converges to the origin for every pair `0 < c₁ ≤ 0.03`, `0.6 ≤ c₂ < 1`.
The theorem proves existence of the classical gradients, positive definite
inverse-Hessian estimates, nonzero gradients and positive curvature products.

The algorithm has a positive finite line-search budget. The constructed
runs accept their first trial, so every positive budget produces the same
infinite orbit. The implemented Wolfe test uses the gradient at the trial
point. On the certified runs every trial is smooth, so the chain rule makes
this the line-derivative test in Algorithm 1. The formalization
does not assert equivalence for nonsmooth trial points of arbitrary runs.

The coercive extension in Section 2.4 is exactly
`f(x) = f̃(x) + max(0, x₁² + x₂² - 100)`. Lean's product of real lines carries
the maximum norm; the extension explicitly uses the displayed squared
Euclidean radius. The open basin allows both the point and the positive
definite inverse-Hessian estimate to vary.

## Module organization

- `BFGS/MainTheorem.lean`: the public main theorem.
- `BFGS/Counterexample/`: the scalar root, exact cycle, objective, derivative,
  stability, linear state coordinates, and assembly of the open failure basin.
- `BFGS/Counterexample/Certificates/`: arithmetic traces, certified bounds,
  and algebraic derivative traces for this construction.
- `BFGS/Analysis/`: reusable interpolation, calculus, BFGS, topology and
  probability results.
- `BFGS/Arithmetic/`: sound rational interval arithmetic.

Every included Lean source is in the import closure of `BFGS.lean`. The old
construction's numerical certificates and their unused concrete lemmas have
been removed by narrowing overly broad imports.

## Proof map and differences in presentation

- Lemma 2.3: `Counterexample/Root.lean` proves root
  existence and uniqueness, including the interval
  `(0.91781039164, 0.91781039165)` used in Appendix A.
- Lemma 2.5: `Counterexample/Algebra.lean` and `Cycle.lean`
  prove the exact updates, positive curvature and return factor `64/81`.
- Propositions 2.7–2.9:
  the interval traces and `TraceBridge.lean` certify the numerical data;
  `PhaseDynamics.lean` proves the actual search and update statements.
- Lemma 2.10: `Analysis.lean` and `Realization.lean`
  construct the homogeneous objective with the prescribed values,
  gradients and Hessians, and establish nonstationarity.
- Proposition A.1: the derivative modules connect
  the arithmetic traces to the actual BFGS derivative. `Stability.lean`
  proves the row-sum bound and an invariant neighborhood.
- Theorem 1.1: `Completion.lean` and `FailureBasin.lean`
  transfer the homogeneous dynamics to the coercive objective and prove
  convergence and positive probability; `MainTheorem.lean` assembles them.

The manuscript invokes a classical interpolation theorem. Lean instead
constructs a polynomial interpolant explicitly with the same prescribed
values and derivatives and the required positive derivative bound. This
supplies a concrete witness for the manuscript's existence result; it does
not formalize the cited interpolation theorem. Section 4 of the self-contained
[notebook](../verification/verification.ipynb) presents the explicit witness.

The realization proves the needed instance with Hessian coefficients
`(1.9,1.6,-4.1,0.2)`. It does not separately package every arbitrary-coefficient
instance of Lemma 2.10. The monotone interpolation construction is proved
analytically; its use here is specialized to the certified data.

Lean defines the Clarke subdifferential through the standard generalized
directional derivative, as a set of continuous linear functionals. The paper
uses the equivalent limiting-gradient description for locally Lipschitz
functions on Euclidean space. That general equivalence is not formalized
here; Lean proves nonstationarity directly from the directional lower bound.

The probability conclusion is proved for independent standard Gaussian
coordinates and the stated Wishart law. The manuscript's more general remark
about a nondegenerate Gaussian initial point is not separately packaged as a
theorem for arbitrary correlated covariance matrices.

Lean uses the manuscript's fixed normalization: `F = r⁻¹ T⁴` and
`ξʲ = r⁻ʲ ω⁴ʲ`, with `r = 64/81`. The linear coordinates
`(ξ₃, S R(ξ − ξ₃ω_*))` express axial drift and transverse contraction without
dividing by a state coordinate. `Analysis/RayAttraction.lean` and
`Analysis/RayBounds.lean` prove arbitrarily small invariant neighborhoods and
convergence to the positive fixed ray (Lemma 2.12).
`Analysis/FixedScale.lean` proves the block identities and the transfer to
physical BFGS iterates in Section 2.4.

## Computational trust and axioms

Lean never treats Python results or saved notebook output as hypotheses.
Its kernel checks the rational interval proofs and their connection to the
BFGS derivative. The Python verifier and notebook reproduce these finite
bounds independently. Regenerate the interval traces with:

```sh
python3 verification/generate_lean.py
python3 verification/generate_lean_bounds.py
```

The generators are untrusted: their output is ordinary Lean proof source.
The generated trace metadata is needed by the bounds generator. Algebraic
bridge and derivative proofs are checked-in Lean sources, not additional
assumptions or external arithmetic results.

The source checker rejects `sorry`, `admit`, added `axiom` declarations,
`native_decide`, `sorryAx`, and options disabling kernel or native type
checking. It excludes comments and strings from that scan. The declaration
audit includes private and generated names and permits only the usual
mathlib foundations `propext`, `Classical.choice` and `Quot.sound` as transitive
axioms. Its generated source is saved as
`.lake/build/lib/lean/CounterexampleAxiomAudit.lean`.

The negative check proves that `[0,1]` contains `1`, then changes only the
upper endpoint to `0`. The second proof must fail with the numerical goal
`False`; an import or syntax error does not count as rejection.

The published entry bounds have row sums `(357,440,776,715)/1000`, all below
`0.78`. The notebook displays the same matrix and checks it while retaining
sharper internal enclosures.
