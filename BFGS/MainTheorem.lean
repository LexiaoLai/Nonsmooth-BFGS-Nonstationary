import BFGS.Counterexample.FailureBasin

/-!
# Failure of Clarke stationarity on an open set

Paper: Lexiao Lai, *BFGS can converge to non-Clarke-stationary points with
positive probability*, [arXiv:2610.34087](https://arxiv.org/abs/2610.34087), 2026.

This file assembles Theorem 1.1 and the probability remark that
follows it. All hypotheses are discharged by the imported construction.

* `f` is the constructed homogeneous objective plus the coercive modification
  `max 0 (x₁² + x₂² - 100)` from Section 2.4.
* `UniformFailureRun f ω` means that one infinite orbit is the actual BFGS run
  from `ω` for every `0 < c₁ ≤ 0.03` and `0.6 ≤ c₂ < 1`. The gradients exist,
  the inverse-Hessian matrices remain positive definite, and the points tend
  to the origin. The definition also records the accepted line-search tests.
* `HasOpenUniformFailureBasin f` supplies a nonempty open set of such states
  with positive Gaussian/Wishart probability. The state is the five-tuple
  `(x₁, x₂, H₁₁, H₁₂, H₂₂)`; its inverse-Hessian matrix is not prescribed.

The definitions and the analytic assembly are in
`BFGS.Counterexample.FailureBasin`. The interval certificate is checked by
Lean's kernel and is linked to the actual derivative in `Stability`.
-/
namespace BFGS.Counterexample
noncomputable section
open Algorithm Filter Topology

/-- Theorem 1.1 for the explicitly constructed objective.
Every analytic, numerical and dynamical premise is proved. -/
theorem concrete_counterexample :
    Semialgebraic.IsSemialgebraicFunction f ∧ LocallyLipschitz f ∧ Continuous f ∧
    Tendsto f (cocompact Vec) atTop ∧ (∀ a : ℝ, IsCompact {x | f x ≤ a}) ∧
    (0 : Vec →L[ℝ] ℝ) ∉ clarkeSubdifferential f 0 ∧ HasOpenUniformFailureBasin f :=
  counterexample_of_invariant_basin Stability.invariant_basin

/-- Theorem 1.1 and its following probability remark,
in existential form. This theorem has no unproved hypotheses. -/
theorem main_theorem :
    ∃ objective : Vec → ℝ,
      Semialgebraic.IsSemialgebraicFunction objective ∧ LocallyLipschitz objective ∧
      Continuous objective ∧ Tendsto objective (cocompact Vec) atTop ∧
      (∀ a : ℝ, IsCompact {x | objective x ≤ a}) ∧
      (0 : Vec →L[ℝ] ℝ) ∉ clarkeSubdifferential objective 0 ∧
      ∃ B : Set State, IsOpen B ∧ B.Nonempty ∧
        (∀ z ∈ B, (metric z).Positive ∧ UniformFailureRun objective z) ∧
        0 < standardInitializationLaw B :=
  ⟨f,concrete_counterexample⟩

end
end BFGS.Counterexample
