import BFGS.Analysis.Coercive
import BFGS.Analysis.Algorithm

/-! The manuscript's Euclidean-radius modification. The product space used
for coordinates carries the maximum norm; the radius below is explicitly
Euclidean, so the modification is exactly the one in the manuscript. -/
namespace BFGS.Euclidean
noncomputable section
open Algorithm Filter Topology

def radius (x : Vec) : ℝ := ‖Complex.equivRealProdCLM.symm x‖

theorem radius_formula (x : Vec) : radius x = Real.sqrt (x.1^2+x.2^2) := by
  simp [radius, Complex.norm_def, Complex.equivRealProdCLM_symm_apply,
    Complex.normSq_apply, pow_two]

theorem radius_nonneg (x : Vec) : 0 ≤ radius x := norm_nonneg _
@[simp] theorem radius_zero : radius 0 = 0 := by simp [radius]

theorem radius_lipschitz : ∃ K : NNReal, LipschitzWith K radius := by
  exact ⟨_, lipschitzWith_one_norm.comp Complex.equivRealProdCLM.symm.lipschitz⟩

theorem radius_continuous : Continuous radius := by
  obtain ⟨_, h⟩ := radius_lipschitz
  exact h.continuous

theorem norm_le_radius (x : Vec) : ‖x‖ ≤ radius x := by
  simpa [radius] using Complex.equivRealProd_apply_le (Complex.equivRealProdCLM.symm x)

theorem radius_le_two_norm (x : Vec) : radius x ≤ 2*‖x‖ := by
  have ha : |x.1| ≤ ‖x‖ := by simp [Prod.norm_def]
  have hb : |x.2| ≤ ‖x‖ := by simp [Prod.norm_def]
  have hr : radius x ≤ |x.1|+|x.2| := by
    simpa [radius,Complex.equivRealProdCLM_symm_apply] using
      Complex.norm_le_abs_re_add_abs_im (Complex.equivRealProdCLM.symm x)
  linarith

theorem radius_smul (t : ℝ) (x : Vec) : radius (t • x) = |t| *radius x := by
  simp [radius,Real.norm_eq_abs]

def extension (f : Vec → ℝ) (x : Vec) : ℝ := f x+(max 0 (radius x-1))^2

theorem extension_eq (f : Vec → ℝ) {x : Vec} (hx : radius x ≤ 1) :
    extension f x = f x := by
  simp [extension,max_eq_left (sub_nonpos.mpr hx)]

theorem extension_eventuallyEq (f : Vec → ℝ) {x : Vec} (hx : radius x < 1) :
    extension f =ᶠ[𝓝 x] f := by
  filter_upwards [radius_continuous.continuousAt.eventually_lt_const hx] with y hy
  exact extension_eq f hy.le

theorem extension_gradient (f : Vec → ℝ) (g : Vec) {x : Vec}
    (hx : radius x < 1) (hg : IsGradientAt f g x) :
    IsGradientAt (extension f) g x :=
  hg.congr_of_eventuallyEq (extension_eventuallyEq f hx)

theorem extension_clarke (f : Vec → ℝ) :
    clarkeSubdifferential (extension f) 0 = clarkeSubdifferential f 0 :=
  clarkeSubdifferential_congr_of_eventuallyEq
    (extension_eventuallyEq f (by simp))

theorem extension_continuous (f : Vec → ℝ) (hf : Continuous f) :
    Continuous (extension f) := by
  exact hf.add (((continuous_const.max (radius_continuous.sub continuous_const))).pow 2)

theorem extension_locallyLipschitz (f : Vec → ℝ) (hf : LocallyLipschitz f) :
    LocallyLipschitz (extension f) := by
  obtain ⟨K,hK⟩ := radius_lipschitz
  have hsub : LipschitzWith K (fun x => radius x-1) := by
    simpa using hK.sub (LipschitzWith.const (1 : ℝ))
  have hm := (hsub.const_max 0).locallyLipschitz
  have hs : LocallyLipschitz (fun t : ℝ => t^2) :=
    (show ContDiff ℝ 1 (fun t : ℝ => t^2) by fun_prop).locallyLipschitz
  exact hf.add (hs.comp hm)

theorem extension_sublevel_radius_bound (f : Vec → ℝ) (L M : ℝ)
    (hL : 0 ≤ L) (hf : ∀ x, -L*radius x ≤ f x) {x : Vec}
    (hsub : extension f x ≤ M) : radius x ≤ L+|M|+3 := by
  by_contra hn
  have ht : L+|M|+3 < radius x := lt_of_not_ge hn
  have ht₁ : 1 < radius x := by have := abs_nonneg M; linarith
  have ht₀ : 0 < radius x := lt_trans zero_lt_one ht₁
  rw [extension,max_eq_right (sub_nonneg.mpr ht₁.le)] at hsub
  have hlow := hf x
  have hprod := mul_lt_mul_of_pos_right ht ht₀
  have hprod₂ : 0 ≤ |M| *(radius x-1) := mul_nonneg (abs_nonneg M) (by linarith)
  have hM := le_abs_self M
  nlinarith

theorem extension_bounded_sublevels (f : Vec → ℝ) (L : ℝ)
    (hL : 0 ≤ L) (hf : ∀ x, -L*radius x ≤ f x) (M : ℝ) :
    Bornology.IsBounded {x | extension f x ≤ M} := by
  apply isBounded_iff_forall_norm_le.2
  exact ⟨L+|M|+3,fun x hx => (norm_le_radius x).trans
    (extension_sublevel_radius_bound f L M hL hf hx)⟩

theorem lipschitz_lower_bound (f : Vec → ℝ) (K : NNReal)
    (hf : LipschitzWith K f) (hzero : f 0 = 0) (x : Vec) :
    -(K : ℝ)*radius x ≤ f x := by
  have h := hf.norm_sub_le x 0
  simp only [hzero,sub_zero,Real.norm_eq_abs] at h
  have hnorm := norm_le_radius x
  have hK : 0 ≤ (K : ℝ) := K.coe_nonneg
  have hneg : -|f x| ≤ f x := neg_abs_le _
  nlinarith

end
end BFGS.Euclidean
