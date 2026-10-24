import Mathlib

/-!
# Positive probability of an open failure basin

The general lemmas use an explicit full-support hypothesis.  The final
section supplies that hypothesis for independent nondegenerate Gaussians and
the concrete two-dimensional initialization `(x, X) ↦ (x, Xᵀ X)`.
No assertion here identifies the particular BFGS failure basin.
-/

namespace BFGS

open MeasureTheory

variable {Ω S : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
  [TopologicalSpace S] [MeasurableSpace S]

/-- Explicit full-support hypothesis, stated in the form used by the proof.
It is independent of any particular Gaussian or Wishart implementation. -/
def PositiveOnNonemptyOpens (μ : Measure Ω) : Prop :=
  ∀ U : Set Ω, IsOpen U → U.Nonempty → 0 < μ U

/-- Compatibility with mathlib's standard full-support measure class. -/
theorem positiveOnNonemptyOpens_of_isOpenPosMeasure
    (μ : Measure Ω) [μ.IsOpenPosMeasure] : PositiveOnNonemptyOpens μ := by
  intro U hU hne
  exact hU.measure_pos μ hne

/-- An open set of bad initializations has positive probability under any
full-support probability law.  The conclusion exhibits a measurable subset,
so no measurability of an abstract infinite-time failure predicate is needed. -/
theorem open_failure_basin_positive
    [OpensMeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hμ : PositiveOnNonemptyOpens μ)
    (failure : Ω → Prop) (U : Set Ω)
    (hU : IsOpen U) (hne : U.Nonempty) (hfail : ∀ ω ∈ U, failure ω) :
    ∃ A : Set Ω, MeasurableSet A ∧ 0 < μ A ∧ ∀ ω ∈ A, failure ω := by
  exact ⟨U, hU.measurableSet, hμ U hU hne, hfail⟩

omit [TopologicalSpace Ω] in
/-- A positive-measure subset of failures rules out almost-sure success,
without assuming that the whole failure predicate is measurable. -/
theorem not_ae_success_of_positive_failure_set
    (μ : Measure Ω) (failure : Ω → Prop) (U : Set Ω)
    (hpos : 0 < μ U) (hfail : ∀ ω ∈ U, failure ω) :
    ¬ (∀ᵐ ω ∂μ, ¬ failure ω) := by
  intro hae
  have hnull : μ {ω | failure ω} = 0 := by
    simpa only [not_not] using (ae_iff.mp hae)
  have hUzero : μ U = 0 := measure_mono_null hfail hnull
  exact (ne_of_gt hpos) hUzero

omit [MeasurableSpace S] in
/-- A continuous initialization map pulls a nonempty open target basin back
to a positive-probability set whenever the basin contains an image point. -/
theorem initialization_preimage_positive
    (μ : Measure Ω) (hμ : PositiveOnNonemptyOpens μ)
    (T : Ω → S) (hT : Continuous T)
    (U : Set S) (hU : IsOpen U)
    (hex : ∃ ω, T ω ∈ U) :
    0 < μ (T ⁻¹' U) := by
  apply hμ (T ⁻¹' U) (hU.preimage hT)
  rcases hex with ⟨ω, hω⟩
  exact ⟨ω, hω⟩

omit [MeasurableSpace S] in
/-- In particular, a continuous surjective parameterization transfers the
open-basin positive-probability argument to the parameter distribution. -/
theorem surjective_initialization_preimage_positive
    (μ : Measure Ω) (hμ : PositiveOnNonemptyOpens μ)
    (T : Ω → S) (hT : Continuous T) (hsurj : Function.Surjective T)
    (U : Set S) (hU : IsOpen U) (hne : U.Nonempty) :
    0 < μ (T ⁻¹' U) := by
  apply initialization_preimage_positive μ hμ T hT U hU
  rcases hne with ⟨s, hs⟩
  rcases hsurj s with ⟨ω, rfl⟩
  exact ⟨ω, hs⟩

section Gaussian

open ProbabilityTheory

/-- A real Gaussian of positive variance gives positive mass to every
nonempty open set. -/
theorem gaussianReal_isOpenPosMeasure (m : ℝ) (v : NNReal) (hv : v ≠ 0) :
    (gaussianReal m v).IsOpenPosMeasure :=
  (gaussianReal_absolutelyContinuous' m hv).isOpenPosMeasure

/-- Finite independent nondegenerate Gaussian coordinates have full support.
Independence is represented by the product measure itself. -/
theorem independent_gaussians_positiveOnNonemptyOpens
    {ι : Type*} [Fintype ι] (m : ι → ℝ) (v : ι → NNReal)
    (hv : ∀ i, v i ≠ 0) :
    PositiveOnNonemptyOpens (Measure.pi fun i => gaussianReal (m i) (v i)) := by
  have : ∀ i, (gaussianReal (m i) (v i)).IsOpenPosMeasure :=
    fun i => gaussianReal_isOpenPosMeasure (m i) (v i) (hv i)
  exact positiveOnNonemptyOpens_of_isOpenPosMeasure _

/-- The coordinate random variables under this product law are jointly
independent; independence is a theorem about the actual chosen measure. -/
theorem independent_gaussian_coordinates
    {ι : Type*} [Fintype ι] (m : ι → ℝ) (v : ι → NNReal) :
    iIndepFun (fun i (ω : ι → ℝ) => ω i)
      (Measure.pi fun i => gaussianReal (m i) (v i)) := by
  exact iIndepFun_pi (fun _ => measurable_id.aemeasurable)

/-- The five coordinates are `(x₁,x₂,H₁₁,H₁₂,H₂₂)`, where `H = XᵀX`
and the four entries of `X` follow the first two point coordinates. -/
def gaussianBFGSInit (ω : Fin 6 → ℝ) : Fin 5 → ℝ :=
  ![ω 0, ω 1, ω 2 ^ 2 + ω 4 ^ 2,
    ω 2 * ω 3 + ω 4 * ω 5, ω 3 ^ 2 + ω 5 ^ 2]

theorem continuous_gaussianBFGSInit : Continuous gaussianBFGSInit := by
  unfold gaussianBFGSInit
  fun_prop

/-- The three stored Hessian coordinates are exactly `XᵀX`, with the
advertised ordering of the four Gaussian matrix entries. -/
theorem gaussianBFGSInit_gram_matrix (ω : Fin 6 → ℝ) :
    (!![gaussianBFGSInit ω 2, gaussianBFGSInit ω 3;
        gaussianBFGSInit ω 3, gaussianBFGSInit ω 4] : Matrix (Fin 2) (Fin 2) ℝ) =
      (!![ω 2, ω 3; ω 4, ω 5]).transpose * !![ω 2, ω 3; ω 4, ω 5] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, gaussianBFGSInit, pow_two, mul_comm]

/-- The point coordinates and the three Gram-matrix coordinates are
independent under the exact six-coordinate law used for initialization.
This follows from independence of the disjoint coordinate blocks before
applying the polynomial Gram map. -/
theorem gaussian_point_indep_gram
    (m : Fin 6 → ℝ) (v : Fin 6 → NNReal) :
    IndepFun
      (fun ω : Fin 6 → ℝ => (![ω 0, ω 1] : Fin 2 → ℝ))
      (fun ω : Fin 6 → ℝ =>
        (![ω 2 ^ 2 + ω 4 ^ 2, ω 2 * ω 3 + ω 4 * ω 5,
          ω 3 ^ 2 + ω 5 ^ 2] : Fin 3 → ℝ))
      (Measure.pi fun i => gaussianReal (m i) (v i)) := by
  let S : Finset (Fin 6) := {0, 1}
  let R : Finset (Fin 6) := {2, 3, 4, 5}
  have hSR : Disjoint S R := by decide
  have hind := iIndepFun.indepFun_finset S R hSR
    (independent_gaussian_coordinates m v) (fun i => measurable_pi_apply i)
  let φ : (S → ℝ) → (Fin 2 → ℝ) := fun u =>
    ![u ⟨0, by decide⟩, u ⟨1, by decide⟩]
  let ψ : (R → ℝ) → (Fin 3 → ℝ) := fun u =>
    ![u ⟨2, by decide⟩ ^ 2 + u ⟨4, by decide⟩ ^ 2,
      u ⟨2, by decide⟩ * u ⟨3, by decide⟩ + u ⟨4, by decide⟩ * u ⟨5, by decide⟩,
      u ⟨3, by decide⟩ ^ 2 + u ⟨5, by decide⟩ ^ 2]
  have hφ : Measurable φ := by unfold φ; fun_prop
  have hψ : Measurable ψ := by unfold ψ; fun_prop
  simpa only [Function.comp_def, φ, ψ] using hind.comp hφ hψ

theorem gaussian_wishart_law_isProbabilityMeasure
    (m : Fin 6 → ℝ) (v : Fin 6 → NNReal) :
    IsProbabilityMeasure (Measure.map gaussianBFGSInit
      (Measure.pi fun i => gaussianReal (m i) (v i))) := by
  exact Measure.isProbabilityMeasure_map continuous_gaussianBFGSInit.measurable.aemeasurable

/-- An explicit Gaussian-parameter point maps to any state with `H = τI`.
Only this elementary preimage is needed for the constructed basin. -/
theorem gaussianBFGSInit_sqrt_diagonal (x₁ x₂ τ : ℝ) (hτ : 0 ≤ τ) :
    gaussianBFGSInit ![x₁, x₂, Real.sqrt τ, 0, 0, Real.sqrt τ] =
      ![x₁, x₂, τ, 0, τ] := by
  ext i
  fin_cases i <;> simp [gaussianBFGSInit, Real.sq_sqrt hτ]

/-- Every open basin containing a positive scalar identity state has positive
probability under independent Gaussian point/Gram-matrix initialization.
Equal standard-normal matrix-entry laws give the usual Wishart law.
The conclusion is about its preimage, so it does not presuppose a separate
Wishart-distribution API. -/
theorem gaussian_wishart_basin_positive
    (m : Fin 6 → ℝ) (v : Fin 6 → NNReal) (hv : ∀ i, v i ≠ 0)
    (U : Set (Fin 5 → ℝ)) (hU : IsOpen U)
    (x₁ x₂ τ : ℝ) (hτ : 0 < τ) (hbase : ![x₁, x₂, τ, 0, τ] ∈ U) :
    0 < (Measure.pi fun i => gaussianReal (m i) (v i))
      (gaussianBFGSInit ⁻¹' U) := by
  apply initialization_preimage_positive _
    (independent_gaussians_positiveOnNonemptyOpens m v hv)
    gaussianBFGSInit continuous_gaussianBFGSInit U hU
  refine ⟨![x₁, x₂, Real.sqrt τ, 0, 0, Real.sqrt τ], ?_⟩
  simpa only [gaussianBFGSInit_sqrt_diagonal x₁ x₂ τ hτ.le] using hbase

/-- The same positivity conclusion stated directly for the pushed-forward
Gaussian/Wishart initialization law on full states. -/
theorem gaussian_wishart_law_basin_positive
    (m : Fin 6 → ℝ) (v : Fin 6 → NNReal) (hv : ∀ i, v i ≠ 0)
    (U : Set (Fin 5 → ℝ)) (hU : IsOpen U)
    (x₁ x₂ τ : ℝ) (hτ : 0 < τ) (hbase : ![x₁, x₂, τ, 0, τ] ∈ U) :
    0 < (Measure.map gaussianBFGSInit
      (Measure.pi fun i => gaussianReal (m i) (v i))) U := by
  rw [Measure.map_apply continuous_gaussianBFGSInit.measurable hU.measurableSet]
  exact gaussian_wishart_basin_positive m v hv U hU x₁ x₂ τ hτ hbase

/-- The law used here is exactly the image of six independent standard
normal coordinates: two for the point and four for a square Gaussian matrix.
Consequently the point and the Wishart matrix use disjoint independent
coordinates, as in the initialization in Challenge 7.1. -/
theorem standard_gaussian_wishart_basin_positive
    (U : Set (Fin 5 → ℝ)) (hU : IsOpen U)
    (x₁ x₂ τ : ℝ) (hτ : 0 < τ) (hbase : ![x₁, x₂, τ, 0, τ] ∈ U) :
    0 < (Measure.map gaussianBFGSInit
      (Measure.pi fun _ : Fin 6 => gaussianReal 0 1)) U := by
  exact gaussian_wishart_law_basin_positive (fun _ => 0) (fun _ => 1)
    (fun _ => one_ne_zero) U hU x₁ x₂ τ hτ hbase

end Gaussian

end BFGS
