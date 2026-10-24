import BFGS.Analysis.Clarke

/-! The explicit coercive modification and its bounded sublevel sets. -/
namespace BFGS
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def coerciveExtension (f : E → ℝ) (x : E) : ℝ :=
  f x + (max 0 (‖x‖-1))^2

omit [NormedSpace ℝ E] in
theorem coerciveExtension_eq_of_norm_le_one (f : E → ℝ) {x : E}
    (hx : ‖x‖ ≤ 1) : coerciveExtension f x = f x := by
  simp [coerciveExtension, max_eq_left (sub_nonpos.mpr hx)]

omit [NormedSpace ℝ E] in
theorem coerciveExtension_eventuallyEq (f : E → ℝ) :
    coerciveExtension f =ᶠ[nhds 0] f := by
  filter_upwards [Metric.ball_mem_nhds (0 : E) (by norm_num : (0:ℝ)<1)] with x hx
  apply coerciveExtension_eq_of_norm_le_one
  exact (show ‖x‖ < 1 by simpa using hx).le

theorem coerciveExtension_clarke (f : E → ℝ) :
    clarkeSubdifferential (coerciveExtension f) 0 = clarkeSubdifferential f 0 :=
  clarkeSubdifferential_congr_of_eventuallyEq (coerciveExtension_eventuallyEq f)

omit [NormedSpace ℝ E] in
theorem coerciveExtension_continuous (f : E → ℝ) (hf : Continuous f) :
    Continuous (coerciveExtension f) := by
  unfold coerciveExtension
  fun_prop

omit [NormedSpace ℝ E] in
/-- A quantitative bound for every sublevel of the actual modification. -/
theorem coerciveExtension_sublevel_norm_bound (f : E → ℝ) (L M : ℝ)
    (hL : 0 ≤ L) (hf : ∀ x, -L*‖x‖ ≤ f x) {x : E}
    (hsub : coerciveExtension f x ≤ M) : ‖x‖ ≤ L + |M| + 3 := by
  by_contra hn
  have ht : L + |M| + 3 < ‖x‖ := lt_of_not_ge hn
  have ht₁ : 1 < ‖x‖ := by have := abs_nonneg M; linarith
  have ht₀ : 0 < ‖x‖ := lt_trans zero_lt_one ht₁
  rw [coerciveExtension, max_eq_right (sub_nonneg.mpr ht₁.le)] at hsub
  have hlow := hf x
  have hprod := mul_lt_mul_of_pos_right ht ht₀
  have hprod₂ : 0 ≤ |M| *(‖x‖-1) := mul_nonneg (abs_nonneg M) (by linarith)
  have hM := le_abs_self M
  nlinarith

omit [NormedSpace ℝ E] in
theorem coerciveExtension_bounded_sublevels (f : E → ℝ) (L : ℝ)
    (hL : 0 ≤ L) (hf : ∀ x, -L*‖x‖ ≤ f x) (M : ℝ) :
    Bornology.IsBounded {x | coerciveExtension f x ≤ M} := by
  apply isBounded_iff_forall_norm_le.2
  exact ⟨L+|M|+3,fun x hx => coerciveExtension_sublevel_norm_bound f L M hL hf hx⟩

end
end BFGS
