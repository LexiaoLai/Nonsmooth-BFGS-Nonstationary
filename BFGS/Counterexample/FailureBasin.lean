import BFGS.Counterexample.Completion
import BFGS.Counterexample.PhaseDynamics
import BFGS.Counterexample.Initialization
import BFGS.Counterexample.Stability

/-!
# Open-set failure of Clarke stationarity

The objective is the actual canonical polynomial-profile realization followed
by the displayed squared-radius coercive extension. Runs use its actual
classical derivative, and one open basin works for the whole parameter rectangle.
-/
namespace BFGS.Counterexample
noncomputable section
open Algorithm CycleDynamics BFGS.StateSpace Filter Topology MeasureTheory ProbabilityTheory

/-- The coercive objective in Section 2.4. -/
def f : Vec → ℝ := radialExtension Realization.f

theorem f_formula (x : Vec) :
    f x = Realization.f x+max 0 (x.1^2+x.2^2-100) := rfl

theorem f_semialgebraic : Semialgebraic.IsSemialgebraicFunction f :=
  radialExtension_semialgebraic Realization.f Realization.f_piecewiseRational

theorem f_locallyLipschitz : LocallyLipschitz f := by
  obtain ⟨K,hK⟩ := Realization.f_lipschitz
  exact radialExtension_locallyLipschitz Realization.f hK.locallyLipschitz

theorem f_continuous : Continuous f :=
  radialExtension_continuous Realization.f Realization.f_continuous

theorem f_compact_sublevels (a : ℝ) : IsCompact {x | f x ≤ a} := by
  obtain ⟨K,hK⟩ := Realization.f_lipschitz
  exact radialExtension_compact_sublevels Realization.f K hK Realization.f_zero a

theorem f_coercive : Tendsto f (cocompact Vec) atTop := by
  obtain ⟨K,hK⟩ := Realization.f_lipschitz
  exact radialExtension_coercive Realization.f K hK Realization.f_zero

theorem f_nonstationary_zero : (0 : Vec →L[ℝ] ℝ) ∉ clarkeSubdifferential f 0 := by
  rw [f,radialExtension_clarke]
  exact Realization.f_nonstationary 0

/-! ## Initialization law and failure statement -/

/-- Independent standard Gaussian point and square-matrix entries, with
inverse metric initialized by the exact Gram map `XᵀX`. -/
def standardInitializationLaw : Measure State :=
  Measure.map gaussianBFGSInit (Measure.pi fun _ : Fin 6 => gaussianReal 0 1)

instance : IsProbabilityMeasure standardInitializationLaw :=
  gaussian_wishart_law_isProbabilityMeasure (fun _ => 0) (fun _ => 1)

/-- A single infinite orbit is the literal BFGS run for every admissible
parameter pair and every positive line-search budget. Every iterate has a
positive inverse metric and an actual classical gradient. -/
def UniformFailureRun (objective : Vec → ℝ) (z : State) : Prop :=
  ∃ orbit : ℕ → State,
    (∀ c₁ c₂, Parameters c₁ c₂ → ∀ fuel n,
      bfgsRun objective (actualGradient objective) c₁ c₂ (fuel+1) z n = some (orbit n)) ∧
    (∀ n, (metric (orbit n)).Positive) ∧
    (∀ n, IsGradientAt objective (actualGradient objective (point (orbit n))) (point (orbit n))) ∧
    (∀ n, actualGradient objective (point (orbit n)) ≠ 0 ∧
      0 < curvature (actualGradient objective) 1 (orbit n)) ∧
    (∀ c₁ c₂, Parameters c₁ c₂ → ∀ n fuel,
      lineSearch objective (actualGradient objective) (point (orbit n))
        (direction (actualGradient objective) (orbit n)) c₁ c₂ (fuel+1) 0 none 1 = some 1) ∧
    Tendsto (fun n => point (orbit n)) atTop (𝓝 0)

/-- The nonempty open failure set is contained in the positive metric state
space and has positive mass under standard Gaussian/Wishart initialization. -/
def HasOpenUniformFailureBasin (objective : Vec → ℝ) : Prop :=
  ∃ B : Set State, IsOpen B ∧ B.Nonempty ∧
    (∀ z ∈ B, (metric z).Positive ∧ UniformFailureRun objective z) ∧
    0 < standardInitializationLaw B

/-! ## Certified invariant basin and transfer to BFGS -/

/-- The fixed-normalization basin conclusion furnished by the numerical
stability certificate. This interface contains no objective or cycle freedom. -/
def InvariantBasin : Prop :=
  ∃ U : Set State, IsOpen U ∧ Stability.baseState ∈ U ∧
    Set.MapsTo Stability.fixedReturn U U ∧
    (∀ w ∈ U, ∀ i : Fin 4,
      PhaseSafe Realization.f Realization.g (3/100) (3/5) PhaseDynamics.smoothSet 4
        ((cycleStep Realization.g)^[i.val] w)) ∧
    ∃ M : ℝ, 0 ≤ M ∧ ∀ w ∈ U, ∀ i : Fin 4,
      ‖(cycleStep Realization.g)^[i.val] w‖ ≤ M

private theorem smoothSet_scale (t : ℝ) (ht : 0 < t) (x : Vec)
    (hx : x ∈ PhaseDynamics.smoothSet) : t • x ∈ PhaseDynamics.smoothSet := by
  change x.1-x.2/20 ≠ 0 at hx
  change t*x.1-t*x.2/20 ≠ 0
  rw [show t*x.1-t*x.2/20 = t*(x.1-x.2/20) by ring]
  exact mul_ne_zero ht.ne' hx

/-- Assembly from the concrete normalized basin to the full-dimensional,
positive-probability, uniform-parameter failure statement. -/
theorem open_failure_of_invariant_basin (hbasin : InvariantBasin) :
    HasOpenUniformFailureBasin f := by
  obtain ⟨U,hUo,hUc,hmap,hphase,M,_,hbound⟩ := hbasin
  obtain ⟨B,hBo,hBne,hrun⟩ := open_failure_of_cycle_basin
    Realization.f Realization.g PhaseDynamics.smoothSet U hUo ⟨Stability.baseState,hUc⟩
    smoothSet_scale Realization.f_pos_homogeneous Realization.g_scale
    PhaseDynamics.actual_gradient r M r_pos (by norm_num [r]) hmap hphase hbound
  have hpositive : ∀ z ∈ B, (metric z).Positive := by
    intro z hz
    obtain ⟨orbit,hsteps,hpos,_,_,_⟩ := hrun z hz
    have h0 := hsteps (1/100) (9/10) (by norm_num [Parameters]) 0 0
    have heq : z = orbit 0 := Option.some.inj h0
    rw [heq]
    exact hpos 0
  refine ⟨B,hBo,hBne,?_,?_⟩
  · intro z hz
    obtain ⟨orbit,hsteps,hpos,hgrad,haccepted,hconv⟩ := hrun z hz
    refine ⟨hpositive z hz,orbit,hsteps,hpos,hgrad,?_,?_,hconv⟩
    · intro n
      have haccept := haccepted (1/100) (9/10) (by norm_num [Parameters]) n
      exact ⟨stepAccepted_gradient_ne f (actualGradient f) _ _ _ haccept,
        stepAccepted_curvature_pos f (actualGradient f) _ _ _ haccept (hpos n) (by norm_num)⟩
    · intro c₁ c₂ hc n fuel
      exact lineSearch_accepts_first f (actualGradient f) c₁ c₂ (orbit n) fuel
        (haccepted c₁ c₂ hc n)
  · exact standard_gaussian_wishart_open_positive B hBo hBne hpositive

/-- The analytic and algorithmic conclusions of the current manuscript,
assembled with its concrete normalized-basin theorem. -/
theorem counterexample_of_invariant_basin (hbasin : InvariantBasin) :
    Semialgebraic.IsSemialgebraicFunction f ∧ LocallyLipschitz f ∧ Continuous f ∧
    Tendsto f (cocompact Vec) atTop ∧ (∀ a : ℝ, IsCompact {x | f x ≤ a}) ∧
    (0 : Vec →L[ℝ] ℝ) ∉ clarkeSubdifferential f 0 ∧ HasOpenUniformFailureBasin f :=
  ⟨f_semialgebraic,f_locallyLipschitz,f_continuous,f_coercive,f_compact_sublevels,
    f_nonstationary_zero,open_failure_of_invariant_basin hbasin⟩

/-- Theorem 1.1, open-basin component.
The explicitly constructed objective has an open basin of infinite,
BFGS runs converging to its nonstationary origin. -/
theorem open_failure : HasOpenUniformFailureBasin f :=
  open_failure_of_invariant_basin Stability.invariant_basin

end
end BFGS.Counterexample
