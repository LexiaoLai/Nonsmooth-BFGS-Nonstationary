import BFGS.Analysis.Probability
import BFGS.Analysis.LocalCycleNeighborhood

/-! Full support of Gaussian/Wishart initialization on every open positive
metric basin. -/
namespace BFGS.Counterexample
noncomputable section
open Algorithm MeasureTheory ProbabilityTheory

/-- An explicit upper-triangular square root parameterizing the metric. -/
def choleskyParameters (z : State) : Fin 6 → ℝ :=
  ![z 0, z 1, Real.sqrt (z 2), z 3 / Real.sqrt (z 2), 0,
    Real.sqrt (z 4-(z 3)^2/z 2)]

/-- Every positive definite planar metric is an exact Gram-matrix image. -/
theorem gaussianBFGSInit_cholesky (z : State) (hz : (metric z).Positive) :
    gaussianBFGSInit (choleskyParameters z) = z := by
  obtain ⟨ha,hdet⟩ := (LocalCycle.positive_metric_iff (metric z)).mp hz
  change 0 < z 2 at ha
  change 0 < z 2*z 4-(z 3)^2 at hdet
  have hres : 0 < z 4-(z 3)^2/z 2 := by
    have hb : (z 3)^2/z 2 < z 4 := (div_lt_iff₀ ha).mpr (by nlinarith)
    exact sub_pos.mpr hb
  have hsqrt : Real.sqrt (z 2) ≠ 0 := (Real.sqrt_pos.2 ha).ne'
  have hdiag : (z 3/Real.sqrt (z 2))^2 = (z 3)^2/z 2 := by
    rw [div_pow, Real.sq_sqrt ha.le]
  ext i
  fin_cases i
  · rfl
  · rfl
  · simpa [gaussianBFGSInit,choleskyParameters] using Real.sq_sqrt ha.le
  · simpa [gaussianBFGSInit,choleskyParameters] using mul_div_cancel₀ (z 3) hsqrt
  · simp [gaussianBFGSInit,choleskyParameters,hdiag,Real.sq_sqrt hres.le]

theorem gaussianBFGSInit_surjective_on_positive (z : State) (hz : (metric z).Positive) :
    ∃ ω : Fin 6 → ℝ, gaussianBFGSInit ω = z :=
  ⟨choleskyParameters z, gaussianBFGSInit_cholesky z hz⟩

/-- A positive metric point anywhere in an open basin gives positive mass
under arbitrary independent nondegenerate Gaussian parameters. -/
theorem gaussian_wishart_open_basin_positive
    (m : Fin 6 → ℝ) (v : Fin 6 → NNReal) (hv : ∀ i, v i ≠ 0)
    (B : Set State) (hB : IsOpen B)
    (hne : ∃ z ∈ B, (metric z).Positive) :
    0 < (Measure.pi fun i => gaussianReal (m i) (v i)) (gaussianBFGSInit ⁻¹' B) := by
  apply initialization_preimage_positive _
    (independent_gaussians_positiveOnNonemptyOpens m v hv)
    gaussianBFGSInit continuous_gaussianBFGSInit B hB
  obtain ⟨z,hz,hpos⟩ := hne
  exact ⟨choleskyParameters z, by simpa only [gaussianBFGSInit_cholesky z hpos] using hz⟩

theorem gaussian_wishart_law_open_basin_positive
    (m : Fin 6 → ℝ) (v : Fin 6 → NNReal) (hv : ∀ i, v i ≠ 0)
    (B : Set State) (hB : IsOpen B)
    (hne : ∃ z ∈ B, (metric z).Positive) :
    0 < (Measure.map gaussianBFGSInit (Measure.pi fun i => gaussianReal (m i) (v i))) B := by
  rw [Measure.map_apply continuous_gaussianBFGSInit.measurable hB.measurableSet]
  exact gaussian_wishart_open_basin_positive m v hv B hB hne

/-- The challenge's standard Gaussian/Wishart law gives positive mass to
any nonempty open state set whose stored inverse metrics are positive. -/
theorem standard_gaussian_wishart_open_positive
    (B : Set State) (hB : IsOpen B) (hne : B.Nonempty)
    (hpos : ∀ z ∈ B, (metric z).Positive) :
    0 < (Measure.map gaussianBFGSInit (Measure.pi fun _ : Fin 6 => gaussianReal 0 1)) B := by
  obtain ⟨z,hz⟩ := hne
  exact gaussian_wishart_law_open_basin_positive (fun _ => 0) (fun _ => 1)
    (fun _ => one_ne_zero) B hB ⟨z,hz,hpos z hz⟩

end
end BFGS.Counterexample
