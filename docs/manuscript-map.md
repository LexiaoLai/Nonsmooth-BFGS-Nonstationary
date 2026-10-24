# Correspondence with the manuscript

This guide uses the numbering in the included
[manuscript](../BFGS%20can%20converge%20to%20non-Clarke-stationary%20points%20with%20positive%20probability.pdf), *BFGS can converge to non-Clarke-stationary
points with positive probability*.

The organization separates the final theorem, supporting analysis, and generated
certificates. Each row describes what is actually checked; it does not assert
that every intermediate lemma is formalized verbatim.

## Main result and analytical construction

All Lean declaration names below beginning with `Counterexample` are in the
`BFGS` namespace. The public entry point is `import BFGS`.

| Manuscript result | Lean source and declarations | Content and scope |
|---|---|---|
| **Theorem 1.1**; Section 2.4 | [MainTheorem.lean](../BFGS/MainTheorem.lean): `Counterexample.main_theorem`, `Counterexample.concrete_counterexample` | Coercive, locally Lipschitz, semialgebraic objective; nonstationary origin; one nonempty open set of positive definite initial states giving infinite BFGS runs converging to the origin for every parameter pair in (1.4). All premises are discharged. |
| Probability remark following Theorem 1.1 | [Initialization.lean](../BFGS/Counterexample/Initialization.lean), [Probability.lean](../BFGS/Analysis/Probability.lean) | The final theorem includes positive probability for the standard independent Gaussian/Wishart law. The initialization module also treats independent Gaussian coordinates with arbitrary means and positive variances. The generic full-support argument is separate; a correlated Gaussian covariance matrix is not packaged as a final theorem. |
| **Lemma 2.3**; (2.3), (A.3) | [Root.lean](../BFGS/Counterexample/Root.lean): `existsUnique_root_broad`, `root_quartic`, `root_mem_broad`, `root_mem_narrow` | The scalar root is uniquely located in the stated coarse interval and lies in the refined interval used for contraction. |
| **Lemma 2.5**; (2.11)–(2.12) | [Cycle.lean](../BFGS/Counterexample/Cycle.lean): `exact_cycle`, `metrics_positive`, `curvature_positive`; [PhaseDynamics.lean](../BFGS/Counterexample/PhaseDynamics.lean): `phaseNormSquared_bounds` | Exact BFGS updates, position recurrence, four-step return, positive definite matrices, positive curvature products, and position bounds. |
| **Lemma 2.6** | [PolynomialBridge.lean](../BFGS/Analysis/PolynomialBridge.lean), [FiniteInterpolation.lean](../BFGS/Analysis/FiniteInterpolation.lean), [CanonicalProfile.lean](../BFGS/Analysis/CanonicalProfile.lean) | An independent explicit polynomial interpolation construction supplies the function needed for the counterexample. The external interpolation theorem cited in the manuscript is not itself formalized. |
| **Lemma 2.10**; Section 2.2 | [Realization.lean](../BFGS/Counterexample/Realization.lean): `f_lipschitz`, `f_contDiffAt`, `f_pos_homogeneous`, `f_nonstationary`, `f_semialgebraic`, `f_phase_all`, `g_phase_all`, `hessian_phase_all` | The concrete homogeneous objective has the prescribed values, gradients, and Hessians. The final realization uses the coefficients in (2.28); the arbitrary-coefficient version of the lemma is not exposed as one theorem. |
| **Lemma 2.11**; Section 2.3 | [Iteration.lean](../BFGS/Analysis/Iteration.lean), [PhaseDynamics.lean](../BFGS/Counterexample/PhaseDynamics.lean), [Neighborhood.lean](../BFGS/Counterexample/Neighborhood.lean) | Differentiable BFGS dynamics and positive scaling near the cycle; identification with the actual algorithm. |
| **Lemma 2.12**; (2.26)–(2.31) | [RayAttraction.lean](../BFGS/Analysis/RayAttraction.lean), [RayBounds.lean](../BFGS/Analysis/RayBounds.lean); [Stability.lean](../BFGS/Counterexample/Stability.lean): `fixed_ray_neighborhood`, `invariant_basin` | The same full-dimensional fixed return map F = r⁻¹T⁴ as in the manuscript. Arbitrarily small open invariant neighborhoods; every normalized orbit converges to a positive multiple of the cycle state. The weighted-neighborhood and summable-drift argument follows the paper. |
| Section 2.4; (2.27), (2.34)–(2.35) | [FixedScale.lean](../BFGS/Analysis/FixedScale.lean): `normalized_iterate`, `iterate_phases`; [Extension.lean](../BFGS/Counterexample/Extension.lean), [Completion.lean](../BFGS/Counterexample/Completion.lean), [FailureBasin.lean](../BFGS/Counterexample/FailureBasin.lean) | The correction max(0, ‖x‖² − 100), local agreement with the homogeneous objective, coercivity, open initial set, and actual line-search runs. |

Proposition 2.1, Lemma 2.2, and
Lemma 2.4 are analytical tools in the manuscript. Lean uses
the corresponding scaling facts and direct update calculations needed by the
concrete construction; it does not duplicate every general statement verbatim.

## Finite certificates and symbolic checks

The self-contained [notebook](../verification/verification.ipynb) displays the
paper's notation and numbered results. Python symbolic checks
confirm identities already proved analytically in Section 2.1. Interval
checks certify the finite inequalities in Appendix A. These have different
roles in the paper's argument.

| Manuscript item | Python / notebook | Lean certificate and connection to the construction |
|---|---|---|
| Lemma 2.3; root interval (A.3) | `verify.root_certificate`; notebook root certificate | [Root.lean](../BFGS/Counterexample/Root.lean) and [IntervalBounds.lean](../BFGS/Counterexample/Certificates/IntervalBounds.lean): `root_mem_interval` |
| Lemma 2.5, (2.11)–(2.12) | `verify.cycle_certificate`; independent [symbolic_cycle.py](../verification/symbolic_cycle.py); notebook exact-cycle checks | [Algebra.lean](../BFGS/Counterexample/Algebra.lean), [Cycle.lean](../BFGS/Counterexample/Cycle.lean) |
| Proposition 2.7 | `verify.geometry_certificate`; notebook signs and slope order | `coordinate_sign_i`, `slope_lower_i`, `slope_upper_i`, and `gap_positive_*` in `IntervalBounds`; [TraceBridge.lean](../BFGS/Counterexample/TraceBridge.lean) identifies the expressions |
| Proposition 2.8; Appendix A.1; Tables 1–2 | `verify.geometry_certificate`; notebook interpolation tables | Derivative and secant bounds in `IntervalBounds`, connected by `TraceBridge` |
| Proposition 2.9; (2.19)–(2.20) | `verify.cycle_certificate`, `verify.geometry_certificate`; notebook Armijo–Wolfe margins | `armijo_positive_i`, `wolfe_positive_i`; `PhaseDynamics.phaseArmijo_positive`, `phaseWolfe_positive`; `Completion.stepAccepted_parameters` extends to (1.4) |
| Explicit realization used in Lemma 2.10 | `verify.bridge_certificate`; notebook polynomial interpolation certificate | [CanonicalProfile.lean](../BFGS/Analysis/CanonicalProfile.lean), `Realization.profile_spec` and `IntervalBounds` |
| Proposition A.1; Appendix A.2; (A.5)–(A.12) | `verify.diff_step`, `verify.calculate`, `verify.stability_certificate`; notebook derivative and contraction certificate | [Derivative.lean](../BFGS/Counterexample/Derivative.lean): `four_cycleSteps_hasFDerivAt_trace`; [Stability.lean](../BFGS/Counterexample/Stability.lean): `fixedReturn_hasFDerivAt`, `projected_derivative`, `transverse_slice_hasFDerivAt`, `contractionDerivative_norm`; `IntervalBounds.conjugated_entry_bound`, `conjugated_row_bound`, `root_conjugated_mulVec_bound` |

The notebook, verifier, and Lean bounds use the manuscript's matrix Γ and
row sums (0.357, 0.440, 0.776, 0.715), whose maximum is less than 0.78.
The displayed bounds are computed by outward rounding of the interval
results; they are not supplied as numerical output targets. The auxiliary polynomial bridge indices concern the explicit
realization in the supplement; they are not additional claims in the paper.

For Lemma 2.12, Lean obtains the local transverse and longitudinal estimates
from differentiability at the base point and positive homogeneity. This is a
shorter justification of the same estimates than the paper's integral proof.
The normalization, invariant neighborhood, positive-ray limit, and block
recursion are the same. The linear change of coordinates used to measure
transverse displacements does not divide a state by one of its coordinates.

## Definitions and trust boundary

- Lean represents a state by the five coordinates (x₁, x₂, H₁₁, H₁₂, H₂₂).
  Its finite indices start at zero, so `ω 2` is the manuscript's third coordinate.
- The formal Clarke subdifferential uses the standard generalized directional
  derivative and continuous linear functionals. The manuscript gives the
  equivalent limiting-gradient definition for locally Lipschitz functions
  in finite dimension. This equivalence is not reproved in the supplement;
  Lean directly proves a strictly negative generalized directional derivative
  in a fixed direction, excluding the zero subgradient.
- Lean's product-space norm and the paper's Euclidean norm give the same
  topology. Explicit position estimates use the Euclidean squared norm.
- The final result is proved with Lean's kernel. The audit rejects unfinished
  proofs, project-defined axioms, and unchecked numerical proof shortcuts.
  Only `propext`, `Classical.choice`, and `Quot.sound` are permitted as
  transitive axioms. Python outputs are not assumed by Lean: the generated
  rational inequalities are proved there and connected to the dynamics.
- Python checks, rendered notebook outputs, and validation logs are
  reproducibility aids. They are not premises of the Lean theorem.
