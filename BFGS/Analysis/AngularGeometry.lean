import BFGS.Analysis.FiniteInterpolation

/-!
# Calculus and Lipschitz bounds for the homogeneous angular lift
-/

namespace BFGS

noncomputable section

open Set

def perspective (h : ℝ → ℝ) (u w : ℝ) : ℝ := u * h (w / u)

theorem hasDerivAt_perspective_horizontal (h : C2Profile) (u w : ℝ) (hu : u ≠ 0) :
    HasDerivAt (fun a ↦ perspective h.value a w)
      (h.value (w / u) - (w / u) * h.slope (w / u)) u := by
  have hq : HasDerivAt (fun a : ℝ ↦ w / a) (-w / u ^ 2) u := by
    convert (hasDerivAt_const u w).div (hasDerivAt_id u) hu using 1 <;>
      first | rfl | simp
  have hc := (h.value_hasDerivAt (w / u)).comp u hq
  have hd := (hasDerivAt_id u).mul hc
  convert hd using 1 <;> try rfl
  simp only [id_eq, Function.comp_apply]
  field_simp
  ring

theorem hasDerivAt_perspective_vertical (h : C2Profile) (u w : ℝ) (hu : u ≠ 0) :
    HasDerivAt (fun b ↦ perspective h.value u b) (h.slope (w / u)) w := by
  have hq : HasDerivAt (fun b : ℝ ↦ b / u) (1 / u) w :=
    (hasDerivAt_id w).div_const u
  have hd := ((h.value_hasDerivAt (w / u)).comp w hq).const_smul u
  convert hd using 1 <;> try rfl
  · simp only [smul_eq_mul]
    field_simp

theorem perspective_horizontal_bound (h : C2Profile) {K u v w : ℝ}
    (hK : ∀ t, ‖h.value t - t * h.slope t‖ ≤ K) (hu : 0 < u) (hv : 0 < v) :
    ‖perspective h.value u w - perspective h.value v w‖ ≤ K * ‖u - v‖ := by
  apply Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun a ↦ perspective h.value a w) (x := v) (y := u) (C := K)
    (f' := fun a ↦ h.value (w / a) - (w / a) * h.slope (w / a))
    (s := Ioi 0)
  · intro a ha
    exact (hasDerivAt_perspective_horizontal h a w (ne_of_gt ha)).hasDerivWithinAt
  · intro a _
    exact hK (w / a)
  · exact convex_Ioi 0
  · exact hv
  · exact hu

theorem perspective_residual_bound (h : ℝ → ℝ) {K u w : ℝ}
    (hK : ∀ t, ‖h t - t‖ ≤ K) (hu : 0 < u) :
    ‖perspective h u w - w‖ ≤ K * u := by
  have hid : perspective h u w - w = u * (h (w / u) - w / u) := by
    unfold perspective
    field_simp
  rw [hid, norm_mul, Real.norm_of_nonneg hu.le]
  calc
    u * ‖h (w / u) - w / u‖ ≤ u * K := mul_le_mul_of_nonneg_left (hK _) hu.le
    _ = K * u := mul_comm _ _

theorem angularLift_residual_bound (hMinus hPlus : ℝ → ℝ) {K : ℝ}
    (hMinusBound : ∀ t, ‖hMinus t - t‖ ≤ K)
    (hPlusBound : ∀ t, ‖hPlus t - t‖ ≤ K) (u w : ℝ) :
    ‖angularLift hMinus hPlus (u, w) - w‖ ≤ K * |u| := by
  by_cases hu : u = 0
  · simp [hu]
  · have habs : 0 < |u| := abs_pos.mpr hu
    by_cases hneg : u < 0
    · simpa [angularLift, hu, hneg, perspective] using
        perspective_residual_bound hMinus hMinusBound (w := w) habs
    · simpa [angularLift, hu, hneg, perspective] using
        perspective_residual_bound hPlus hPlusBound (w := w) habs

def angularVerticalSlope (hMinus hPlus : C2Profile) (u w : ℝ) : ℝ :=
  if u = 0 then 1 else (if u < 0 then hMinus else hPlus).slope (w / |u|)

theorem hasDerivAt_angularLift_vertical (hMinus hPlus : C2Profile) (u w : ℝ) :
    HasDerivAt (fun b ↦ angularLift hMinus.value hPlus.value (u, b))
      (angularVerticalSlope hMinus hPlus u w) w := by
  by_cases hu : u = 0
  · convert hasDerivAt_id w using 1 <;> try rfl
    · funext b
      simp [angularLift, hu]
    · simp [angularVerticalSlope, hu]
  · by_cases hneg : u < 0
    · simpa [angularLift, angularVerticalSlope, hu, hneg, perspective] using
        hasDerivAt_perspective_vertical hMinus |u| w (abs_ne_zero.mpr hu)
    · simpa [angularLift, angularVerticalSlope, hu, hneg, perspective] using
        hasDerivAt_perspective_vertical hPlus |u| w (abs_ne_zero.mpr hu)

theorem angularLift_vertical_bound (hMinus hPlus : C2Profile) {L : ℝ}
    (hL : 1 ≤ L) (hMinusBound : ∀ t, ‖hMinus.slope t‖ ≤ L)
    (hPlusBound : ∀ t, ‖hPlus.slope t‖ ≤ L) (u a b : ℝ) :
    ‖angularLift hMinus.value hPlus.value (u, a) -
      angularLift hMinus.value hPlus.value (u, b)‖ ≤ L * ‖a - b‖ := by
  apply Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun w ↦ angularLift hMinus.value hPlus.value (u, w))
    (f' := angularVerticalSlope hMinus hPlus u) (s := Set.univ) (x := b) (y := a) (C := L)
  · intro w _
    exact (hasDerivAt_angularLift_vertical hMinus hPlus u w).hasDerivWithinAt
  · intro w _
    by_cases hu : u = 0
    · simpa [angularVerticalSlope, hu] using hL
    · by_cases hneg : u < 0
      · simpa [angularVerticalSlope, hu, hneg] using hMinusBound (w / |u|)
      · simpa [angularVerticalSlope, hu, hneg] using hPlusBound (w / |u|)
  · exact convex_univ
  · exact mem_univ _
  · exact mem_univ _

theorem angularLift_horizontal_bound (hMinus hPlus : C2Profile) {K : ℝ}
    (hK : 0 ≤ K)
    (hMinusResidual : ∀ t, ‖hMinus.value t - t‖ ≤ K)
    (hPlusResidual : ∀ t, ‖hPlus.value t - t‖ ≤ K)
    (hMinusHorizontal : ∀ t, ‖hMinus.value t - t * hMinus.slope t‖ ≤ K)
    (hPlusHorizontal : ∀ t, ‖hPlus.value t - t * hPlus.slope t‖ ≤ K)
    (u v w : ℝ) :
    ‖angularLift hMinus.value hPlus.value (u, w) -
      angularLift hMinus.value hPlus.value (v, w)‖ ≤ K * ‖u - v‖ := by
  by_cases hu : u = 0
  · subst u
    rw [angularLift_axis, norm_sub_rev]
    simpa [Real.norm_eq_abs] using
      angularLift_residual_bound hMinus.value hPlus.value hMinusResidual hPlusResidual v w
  by_cases hv : v = 0
  · subst v
    simpa [Real.norm_eq_abs] using
      angularLift_residual_bound hMinus.value hPlus.value hMinusResidual hPlusResidual u w
  have hau : 0 < |u| := abs_pos.mpr hu
  have hav : 0 < |v| := abs_pos.mpr hv
  by_cases hsign : (u < 0 ↔ v < 0)
  · have hb : ‖angularLift hMinus.value hPlus.value (u, w) -
        angularLift hMinus.value hPlus.value (v, w)‖ ≤ K * ‖|u| - |v|‖ := by
      by_cases huneg : u < 0
      · simpa [angularLift, hu, hv, huneg, hsign.mp huneg, perspective] using
          perspective_horizontal_bound hMinus hMinusHorizontal (w := w) hau hav
      · have hvneg : ¬v < 0 := fun h ↦ huneg (hsign.mpr h)
        simpa [angularLift, hu, hv, huneg, hvneg, perspective] using
          perspective_horizontal_bound hPlus hPlusHorizontal (w := w) hau hav
    exact hb.trans (mul_le_mul_of_nonneg_left (norm_abs_sub_abs u v) hK)
  · have habs : |u| + |v| = ‖u - v‖ := by
      rw [Real.norm_eq_abs]
      by_cases huneg : u < 0
      · have hvpos : 0 < v := by
          by_contra h
          have hvneg : v < 0 := lt_of_le_of_ne (not_lt.mp h) hv
          exact hsign ⟨fun _ ↦ hvneg, fun _ ↦ huneg⟩
        rw [abs_of_neg huneg, abs_of_pos hvpos, abs_of_neg (by linarith : u - v < 0)]
        ring
      · have hup : 0 < u := lt_of_le_of_ne (not_lt.mp huneg) (Ne.symm hu)
        have hvneg : v < 0 := by
          by_contra h
          exact hsign ⟨fun hh ↦ (huneg hh).elim, fun hh ↦ (h hh).elim⟩
        rw [abs_of_pos hup, abs_of_neg hvneg, abs_of_pos (by linarith : 0 < u - v)]
        ring
    calc
      ‖angularLift hMinus.value hPlus.value (u, w) -
          angularLift hMinus.value hPlus.value (v, w)‖ ≤
          ‖angularLift hMinus.value hPlus.value (u, w) - w‖ +
          ‖w - angularLift hMinus.value hPlus.value (v, w)‖ := by
            simpa only [sub_add_sub_cancel] using norm_add_le
              (angularLift hMinus.value hPlus.value (u, w) - w)
              (w - angularLift hMinus.value hPlus.value (v, w))
      _ ≤ K * |u| + K * |v| := by
        rw [norm_sub_rev w]
        exact add_le_add
          (angularLift_residual_bound _ _ hMinusResidual hPlusResidual u w)
          (angularLift_residual_bound _ _ hMinusResidual hPlusResidual v w)
      _ = K * ‖u - v‖ := by rw [← mul_add, habs]

/-- Uniform angular derivative and residual bounds give a global Lipschitz
constant, including across the axis where the two profiles may have different
affine-tail intercepts. -/
theorem angularLift_lipschitz (hMinus hPlus : C2Profile) {K L : ℝ}
    (hK : 0 ≤ K) (hL : 1 ≤ L)
    (hMinusResidual : ∀ t, ‖hMinus.value t - t‖ ≤ K)
    (hPlusResidual : ∀ t, ‖hPlus.value t - t‖ ≤ K)
    (hMinusHorizontal : ∀ t, ‖hMinus.value t - t * hMinus.slope t‖ ≤ K)
    (hPlusHorizontal : ∀ t, ‖hPlus.value t - t * hPlus.slope t‖ ≤ K)
    (hMinusSlope : ∀ t, ‖hMinus.slope t‖ ≤ L)
    (hPlusSlope : ∀ t, ‖hPlus.slope t‖ ≤ L) :
    LipschitzWith (NNReal.mk (K + L) (add_nonneg hK (by linarith)))
      (angularLift hMinus.value hPlus.value) := by
  rw [lipschitzWith_iff_norm_sub_le]
  rintro ⟨u, w⟩ ⟨v, y⟩
  let f := angularLift hMinus.value hPlus.value
  change ‖f (u, w) - f (v, y)‖ ≤ (K + L) * ‖(u, w) - (v, y)‖
  calc
    ‖f (u, w) - f (v, y)‖ ≤ ‖f (u, w) - f (v, w)‖ + ‖f (v, w) - f (v, y)‖ := by
      simpa only [sub_add_sub_cancel] using norm_add_le
        (f (u, w) - f (v, w)) (f (v, w) - f (v, y))
    _ ≤ K * ‖u - v‖ + L * ‖w - y‖ := add_le_add
      (angularLift_horizontal_bound hMinus hPlus hK hMinusResidual hPlusResidual
        hMinusHorizontal hPlusHorizontal u v w)
      (angularLift_vertical_bound hMinus hPlus hL hMinusSlope hPlusSlope v w y)
    _ ≤ K * ‖(u, w) - (v, y)‖ + L * ‖(u, w) - (v, y)‖ := add_le_add
      (mul_le_mul_of_nonneg_left (norm_fst_le ((u, w) - (v, y))) hK)
      (mul_le_mul_of_nonneg_left (norm_snd_le ((u, w) - (v, y))) (by linarith))
    _ = (K + L) * ‖(u, w) - (v, y)‖ := by ring

namespace C2Profile

theorem slope_eq_one_of_left_tail (h : C2Profile) {a b x : ℝ}
    (htail : ∀ t ≤ a, h.value t = t + b) (hx : x < a) : h.slope x = 1 := by
  have heq : h.value =ᶠ[nhds x] (fun t ↦ t + b) := by
    filter_upwards [Iio_mem_nhds hx] with t ht
    exact htail t (show t < a from ht).le
  have hd : HasDerivAt (fun t : ℝ ↦ t + b) 1 x := by
    convert (hasDerivAt_id x).add_const b using 1 <;> rfl
  exact (h.value_hasDerivAt x).unique (hd.congr_of_eventuallyEq heq)

theorem slope_eq_one_of_right_tail (h : C2Profile) {a b x : ℝ}
    (htail : ∀ t, a ≤ t → h.value t = t + b) (hx : a < x) : h.slope x = 1 := by
  have heq : h.value =ᶠ[nhds x] (fun t ↦ t + b) := by
    filter_upwards [Ioi_mem_nhds hx] with t ht
    exact htail t (show a < t from ht).le
  have hd : HasDerivAt (fun t : ℝ ↦ t + b) 1 x := by
    convert (hasDerivAt_id x).add_const b using 1 <;> rfl
  exact (h.value_hasDerivAt x).unique (hd.congr_of_eventuallyEq heq)

/-- Affine tails of slope one supply all angular bounds required by the
global Lipschitz theorem. -/
theorem exists_angular_bounds (h : C2Profile) {a b bLeft bRight : ℝ}
    (hleft : ∀ t ≤ a, h.value t = t + bLeft)
    (hright : ∀ t, b ≤ t → h.value t = t + bRight) :
    ∃ K : ℝ, 1 ≤ K ∧ (∀ t, ‖h.value t - t‖ ≤ K) ∧
      (∀ t, ‖h.slope t‖ ≤ K) ∧ (∀ t, ‖h.value t - t * h.slope t‖ ≤ K) := by
  obtain ⟨C1, hC1⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (h.continuous_value.sub continuous_id).continuousOn (s := Icc a b)
  obtain ⟨C2, hC2⟩ := isCompact_Icc.exists_bound_of_continuousOn
    h.continuous_slope.continuousOn (s := Icc a b)
  obtain ⟨C3, hC3⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (h.continuous_value.sub (continuous_id.mul h.continuous_slope)).continuousOn (s := Icc a b)
  let K := 1 + |C1| + |C2| + |C3| + |bLeft| + |bRight|
  have hK1 : 1 ≤ K := by
    dsimp [K]
    linarith [abs_nonneg C1, abs_nonneg C2, abs_nonneg C3, abs_nonneg bLeft, abs_nonneg bRight]
  have hKL : |bLeft| ≤ K := by
    dsimp [K]
    linarith [abs_nonneg C1, abs_nonneg C2, abs_nonneg C3, abs_nonneg bLeft, abs_nonneg bRight]
  have hKR : |bRight| ≤ K := by
    dsimp [K]
    linarith [abs_nonneg C1, abs_nonneg C2, abs_nonneg C3, abs_nonneg bLeft, abs_nonneg bRight]
  have hKC1 : C1 ≤ K := by
    dsimp [K]
    linarith [le_abs_self C1, abs_nonneg C2, abs_nonneg C3, abs_nonneg bLeft, abs_nonneg bRight]
  have hKC2 : C2 ≤ K := by
    dsimp [K]
    linarith [abs_nonneg C1, le_abs_self C2, abs_nonneg C3, abs_nonneg bLeft, abs_nonneg bRight]
  have hKC3 : C3 ≤ K := by
    dsimp [K]
    linarith [abs_nonneg C1, abs_nonneg C2, le_abs_self C3, abs_nonneg bLeft, abs_nonneg bRight]
  have hall (t : ℝ) : ‖h.value t - t‖ ≤ K ∧ ‖h.slope t‖ ≤ K ∧
      ‖h.value t - t * h.slope t‖ ≤ K := by
    by_cases ht : t < a
    · rw [hleft t ht.le, h.slope_eq_one_of_left_tail hleft ht]
      simpa [Real.norm_eq_abs] using And.intro hKL (And.intro hK1 hKL)
    by_cases ht' : b < t
    · rw [hright t ht'.le, h.slope_eq_one_of_right_tail hright ht']
      simpa [Real.norm_eq_abs] using And.intro hKR (And.intro hK1 hKR)
    have hmem : t ∈ Icc a b := ⟨le_of_not_gt ht, le_of_not_gt ht'⟩
    exact ⟨(hC1 t hmem).trans hKC1, (hC2 t hmem).trans hKC2, (hC3 t hmem).trans hKC3⟩
  exact ⟨K, hK1, fun t ↦ (hall t).1, fun t ↦ (hall t).2.1, fun t ↦ (hall t).2.2⟩

end C2Profile

/-- The affine tails supplied by finite interpolation suffice for global
Lipschitz continuity of the actual homogeneous lift. -/
theorem angularLift_lipschitz_of_affine_tails (hMinus hPlus : C2Profile)
    {aMinus bMinus leftMinus rightMinus aPlus bPlus leftPlus rightPlus : ℝ}
    (hMinusLeft : ∀ t ≤ aMinus, hMinus.value t = t + leftMinus)
    (hMinusRight : ∀ t, bMinus ≤ t → hMinus.value t = t + rightMinus)
    (hPlusLeft : ∀ t ≤ aPlus, hPlus.value t = t + leftPlus)
    (hPlusRight : ∀ t, bPlus ≤ t → hPlus.value t = t + rightPlus) :
    ∃ K : NNReal, LipschitzWith K (angularLift hMinus.value hPlus.value) := by
  obtain ⟨KM, hKM, hMR, hMS, hMH⟩ := hMinus.exists_angular_bounds hMinusLeft hMinusRight
  obtain ⟨KP, hKP, hPR, hPS, hPH⟩ := hPlus.exists_angular_bounds hPlusLeft hPlusRight
  have hK : 1 ≤ max KM KP := hKM.trans (le_max_left _ _)
  exact ⟨_, angularLift_lipschitz hMinus hPlus (K := max KM KP) (L := max KM KP)
    (by linarith) hK
    (fun t ↦ (hMR t).trans (le_max_left _ _))
    (fun t ↦ (hPR t).trans (le_max_right _ _))
    (fun t ↦ (hMH t).trans (le_max_left _ _))
    (fun t ↦ (hPH t).trans (le_max_right _ _))
    (fun t ↦ (hMS t).trans (le_max_left _ _))
    (fun t ↦ (hPS t).trans (le_max_right _ _))⟩

end

end BFGS
