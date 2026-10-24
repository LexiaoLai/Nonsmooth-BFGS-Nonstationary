import BFGS.Analysis.Dynamics
import BFGS.Analysis.RayBounds

/-!
# Attraction to a fixed ray: local estimates

Lemma 2.12 uses the fixed return map F = r⁻¹ T⁴.
Positive homogeneity transfers the derivative estimate at (1,0) to nearby
points of its fixed ray. The two components below are the longitudinal
coordinate and the transverse coordinates used in the manuscript.
-/
namespace BFGS.Analysis
noncomputable section
open Filter Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- First-order control of a scalar function at the origin. -/
theorem scalar_radial_bound (g : E → ℝ) (hg : DifferentiableAt ℝ g 0) :
    ∃ ρ > 0, ∃ C > 0, ∀ u : E, ‖u‖ < ρ → |g u - g 0| ≤ C * ‖u‖ := by
  let A := fderiv ℝ g 0
  have hd : HasFDerivAt g A 0 := hg.hasFDerivAt
  obtain ⟨ρ,hρ,hrem⟩ := Metric.eventually_nhds_iff.mp
    (hd.isLittleO.bound (show (0:ℝ) < 1 by norm_num))
  refine ⟨ρ,hρ,1+‖A‖,by positivity,?_⟩
  intro u hu
  have hh := hrem (show dist u 0 < ρ by simpa using hu)
  simp only [sub_zero,one_mul] at hh
  rw [← Real.norm_eq_abs]
  calc
    ‖g u-g 0‖ = ‖(g u-g 0-A u)+A u‖ := by rw [sub_add_cancel]
    _ ≤ ‖g u-g 0-A u‖+‖A u‖ := norm_add_le _ _
    _ ≤ ‖u‖+‖A‖*‖u‖ := add_le_add hh (A.le_opNorm _)
    _ = (1+‖A‖)*‖u‖ := by ring

/-- The transverse and longitudinal estimates (2.31) for a homogeneous
return map. Only the derivative at the base point is needed. -/
theorem fixed_ray_local_bounds
    (F : ℝ × E → ℝ × E) (A : E →L[ℝ] E)
    (hfixed : F (1,0) = (1,0))
    (hhom : ∀ t : ℝ, 0 < t → ∀ z, F (t • z) = t • F z)
    (htrans : HasFDerivAt (fun u : E => (F (1,u)).2) A 0)
    (hscalar : DifferentiableAt ℝ (fun u : E => (F (1,u)).1) 0)
    (hA : ‖A‖ < 1) :
    ∃ δ > 0, ∃ γ : ℝ, 0 ≤ γ ∧ γ < 1 ∧ ∃ C > 0,
      ∀ z : ℝ × E, |z.1-1| ≤ (1:ℝ)/2 → ‖z.2‖ ≤ δ →
        ‖(F z).2‖ ≤ γ*‖z.2‖ ∧ |(F z).1-z.1| ≤ C*‖z.2‖ := by
  obtain ⟨ρ,hρ,γ,hγ0,hγ1,hcontract⟩ :=
    BFGS.radial_contraction_of_derivative (fun u : E => (F (1,u)).2) A 0
      htrans (by simpa using congrArg Prod.snd hfixed) hA
  obtain ⟨σ,hσ,C,hC,hscalarBound⟩ := scalar_radial_bound _ hscalar
  let δ := min ρ σ / 4
  have hδ : 0 < δ := div_pos (lt_min hρ hσ) (by norm_num)
  refine ⟨δ,hδ,γ,hγ0,hγ1,C,hC,?_⟩
  rintro ⟨a,u⟩ ha hu
  have haLower : (1:ℝ)/2 ≤ a := by
    have hh := (abs_le.mp ha).1
    dsimp at hh
    linarith
  have haPos : 0 < a := lt_of_lt_of_le (by norm_num) haLower
  let v := a⁻¹ • u
  have hav : a • v = u := by simp [v,smul_smul,haPos.ne']
  have hnorm : a*‖v‖ = ‖u‖ := by
    calc
      a*‖v‖ = ‖a • v‖ := by
        conv_rhs => rw [norm_smul,Real.norm_eq_abs,abs_of_pos haPos]
      _ = ‖u‖ := by rw [hav]
  have hvsmall : ‖v‖ ≤ 2*δ := by
    have hn : 0 ≤ ‖v‖ := norm_nonneg _
    change ‖u‖ ≤ δ at hu
    nlinarith
  have hvρ : ‖v‖ < ρ := by
    have hm := min_le_left ρ σ
    dsimp [δ] at hvsmall
    linarith
  have hvσ : ‖v‖ < σ := by
    have hm := min_le_right ρ σ
    dsimp [δ] at hvsmall
    linarith
  have hF : F (a,u) = a • F (1,v) := by
    have heq : (a,u) = a • (1,v) := by
      apply Prod.ext
      · simp
      · exact hav.symm
    rw [heq,hhom a haPos]
  constructor
  · have ht := hcontract v (show v ∈ Metric.ball 0 ρ by simpa using hvρ)
    simp only [dist_zero_right] at ht
    calc
      ‖(F (a,u)).2‖ = a*‖(F (1,v)).2‖ := by
        rw [hF]; simp [norm_smul,Real.norm_eq_abs,abs_of_pos haPos]
      _ ≤ a*(γ*‖v‖) := mul_le_mul_of_nonneg_left ht haPos.le
      _ = γ*‖u‖ := by rw [← hnorm]; ring
  · have hs := hscalarBound v hvσ
    have hzero : (F (1,(0:E))).1 = 1 := congrArg Prod.fst hfixed
    simp only [hzero] at hs
    calc
      |(F (a,u)).1-a| = a*|(F (1,v)).1-1| := by
        rw [hF]
        change |a*(F (1,v)).1-a| = a*|(F (1,v)).1-1|
        rw [show a*(F (1,v)).1-a = a*((F (1,v)).1-1) by ring,
          abs_mul,abs_of_pos haPos]
      _ ≤ a*(C*‖v‖) := mul_le_mul_of_nonneg_left hs haPos.le
      _ = C*‖u‖ := by rw [← hnorm]; ring

/-- Lemma 2.12: arbitrarily small open invariant neighborhoods for the
fixed return map, with convergence to a positive point of its fixed ray. -/
theorem exists_open_fixed_ray_neighborhood
    (F : ℝ × E → ℝ × E) (A : E →L[ℝ] E)
    (hfixed : F (1,0) = (1,0))
    (hhom : ∀ t : ℝ, 0 < t → ∀ z, F (t • z) = t • F z)
    (htrans : HasFDerivAt (fun u : E => (F (1,u)).2) A 0)
    (hscalar : DifferentiableAt ℝ (fun u : E => (F (1,u)).1) 0)
    (hA : ‖A‖ < 1) (O : Set (ℝ × E)) (hO : O ∈ 𝓝 (1,(0:E))) :
    ∃ U : Set (ℝ × E), IsOpen U ∧ (1,(0:E)) ∈ U ∧ U ⊆ O ∧
      Set.MapsTo F U U ∧ ∀ z ∈ U, ∃ a : ℝ, 0 < a ∧
        Tendsto (fun n : ℕ => F^[n] z) atTop (𝓝 (a,(0:E))) := by
  obtain ⟨δ,hδ,γ,hγ0,hγ1,C,hC,hstep⟩ :=
    fixed_ray_local_bounds F A hfixed hhom htrans hscalar hA
  obtain ⟨R,hR,hRO⟩ := Metric.mem_nhds_iff.mp hO
  let ε := min ((1:ℝ)/4) (R/2)
  let δ' := min δ (R/2)
  have hε : 0 < ε := lt_min (by norm_num) (half_pos hR)
  have hεhalf : ε ≤ (1:ℝ)/2 := (min_le_left _ _).trans (by norm_num)
  have hε1 : ε < 1 := lt_of_le_of_lt hεhalf (by norm_num)
  have hδ' : 0 < δ' := lt_min hδ (half_pos hR)
  obtain ⟨U,hUo,hUb,hUsub,hUmap,hUlim⟩ :=
    exists_ray_attraction_neighborhood F ε δ' γ C hε hε1 hδ' hγ0 hγ1 hC.le
      (fun z ha hu => hstep z (ha.trans hεhalf) (hu.trans (min_le_left _ _)))
  refine ⟨U,hUo,hUb,?_,hUmap,hUlim⟩
  intro z hz
  apply hRO
  have hz' := hUsub hz
  have ha : |z.1-1| < R := lt_of_le_of_lt
    (hz'.1.trans (min_le_right _ _)) (half_lt_self hR)
  have hu : ‖z.2‖ < R := lt_of_le_of_lt
    (hz'.2.trans (min_le_right _ _)) (half_lt_self hR)
  simpa only [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, dist_zero_right,
    max_lt_iff] using And.intro ha hu

end
end BFGS.Analysis
