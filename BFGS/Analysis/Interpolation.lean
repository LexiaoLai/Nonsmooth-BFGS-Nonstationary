import BFGS.Analysis.Clarke

/-!
# The homogeneous angular lift and its separating direction

The construction takes two one-dimensional angular profiles. This module
proves positive homogeneity and the directional increment inequality for
their actual two-dimensional lift, hence separation of its genuine Clarke
subdifferential. It does not assume or claim the existence of profiles
matching the finite BFGS two-jets. The finite two-jet interpolation theorem,
global Lipschitz bound, and semialgebraicity remain separate obligations.
-/

namespace BFGS

noncomputable section

/-- A quantitative one-dimensional monotonicity inequality. -/
def HasLowerSlope (h : ℝ → ℝ) (m : ℝ) : Prop :=
  ∀ a b, a ≤ b → m * (b - a) ≤ h b - h a

/-- The mean-value theorem turns a derivative lower bound into the finite
increment inequality used by the two-dimensional construction. -/
theorem hasLowerSlope_of_hasDerivAt {h h' : ℝ → ℝ} {m : ℝ}
    (hh : ∀ x, HasDerivAt h (h' x) x) (hm : ∀ x, m ≤ h' x) :
    HasLowerSlope h m := by
  have hd (x : ℝ) : HasDerivAt (fun t ↦ h t - m * t) (h' x - m) x := by
    exact (hh x).fun_sub (hasDerivAt_const_mul m)
  have hmono : Monotone (fun t ↦ h t - m * t) := by
    apply monotone_of_deriv_nonneg
    · intro x
      exact (hd x).differentiableAt
    · intro x
      rw [(hd x).deriv]
      exact sub_nonneg.mpr (hm x)
  intro a b hab
  have h := hmono hab
  dsimp at h
  linarith

/-- The cubic cutoff used in the endpoint layers of the interpolation proof. -/
def endpointCutoff (t : ℝ) : ℝ := 1 - 3 * t ^ 2 + 2 * t ^ 3

theorem endpointCutoff_nonneg {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ endpointCutoff t := by
  have hfactor : endpointCutoff t = (1 - t) ^ 2 * (1 + 2 * t) := by
    unfold endpointCutoff
    ring
  rw [hfactor]
  positivity

theorem endpointCutoff_le_one {t : ℝ} (ht : t ≤ 1) :
    endpointCutoff t ≤ 1 := by
  have hfactor : 1 - endpointCutoff t = t ^ 2 * (3 - 2 * t) := by
    unfold endpointCutoff
    ring
  have hp : 0 ≤ t ^ 2 * (3 - 2 * t) := mul_nonneg (sq_nonneg t) (by linarith)
  linarith

theorem hasDerivAt_endpointCutoff (t : ℝ) :
    HasDerivAt endpointCutoff (-6 * t + 6 * t ^ 2) t := by
  have h2 : HasDerivAt (fun x : ℝ ↦ x ^ 2) (2 * t) t := by
    convert hasDerivAt_pow 2 t using 1 <;> first | rfl | norm_num
  have h3 : HasDerivAt (fun x : ℝ ↦ x ^ 3) (3 * t ^ 2) t := by
    convert hasDerivAt_pow 3 t using 1 <;> rfl
  have hp := ((hasDerivAt_const t (1 : ℝ)).fun_sub
    (h2.const_smul (3 : ℝ))).fun_add (h3.const_smul (2 : ℝ))
  convert hp using 1 <;> first | rfl | (simp only [smul_eq_mul]; ring)

@[simp] theorem endpointCutoff_zero : endpointCutoff 0 = 1 := by
  norm_num [endpointCutoff]

@[simp] theorem endpointCutoff_one : endpointCutoff 1 = 0 := by
  norm_num [endpointCutoff]

@[simp] theorem deriv_endpointCutoff_zero : deriv endpointCutoff 0 = 0 := by
  rw [(hasDerivAt_endpointCutoff 0).deriv]
  norm_num

@[simp] theorem deriv_endpointCutoff_one : deriv endpointCutoff 1 = 0 := by
  rw [(hasDerivAt_endpointCutoff 1).deriv]
  norm_num

/-- The angular profile on the negative and positive horizontal half-planes;
the vertical axis is assigned its common continuous affine-tail value. -/
def angularLift (hMinus hPlus : ℝ → ℝ) (z : ℝ × ℝ) : ℝ :=
  if z.1 = 0 then z.2 else
    |z.1| * (if z.1 < 0 then hMinus else hPlus) (z.2 / |z.1|)

@[simp] theorem angularLift_axis (hMinus hPlus : ℝ → ℝ) (w : ℝ) :
    angularLift hMinus hPlus (0, w) = w := by
  simp [angularLift]

/-- The lift is positively homogeneous for any angular profiles. -/
theorem angularLift_pos_homogeneous (hMinus hPlus : ℝ → ℝ)
    (z : ℝ × ℝ) {τ : ℝ} (hτ : 0 < τ) :
    angularLift hMinus hPlus (τ • z) = τ * angularLift hMinus hPlus z := by
  have hsign : τ * z.1 < 0 ↔ z.1 < 0 := by
    constructor <;> intro h <;> nlinarith
  have habs : |τ * z.1| = τ * |z.1| := by rw [abs_mul, abs_of_pos hτ]
  by_cases hu : z.1 = 0
  · simp [angularLift, hu]
  · have hτu : τ * z.1 ≠ 0 := mul_ne_zero hτ.ne' hu
    have hratio : (τ * z.2) / (τ * |z.1|) = z.2 / |z.1| := by
      field_simp [hτ.ne', abs_ne_zero.mpr hu]
    change angularLift hMinus hPlus (τ * z.1, τ * z.2) =
      τ * angularLift hMinus hPlus z
    simp only [angularLift,
      hu, hτu, if_false, habs, hsign, hratio]
    ring

/-- Angular lower slopes imply a uniform positive vertical increment. The
axis case explains the harmless upper bound `m ≤ 1`. -/
theorem angularLift_vertical_increment
    {hMinus hPlus : ℝ → ℝ} {m : ℝ}
    (hMinusSlope : HasLowerSlope hMinus m)
    (hPlusSlope : HasLowerSlope hPlus m) (hm : m ≤ 1)
    (u w t : ℝ) (ht : 0 ≤ t) :
    angularLift hMinus hPlus (u, w) + m * t ≤
      angularLift hMinus hPlus (u, w + t) := by
  by_cases hu : u = 0
  · subst u
    simp only [angularLift_axis]
    nlinarith
  · let h : ℝ → ℝ := if u < 0 then hMinus else hPlus
    have hs : HasLowerSlope h m := by
      dsimp [h]
      split_ifs <;> assumption
    have habs : 0 < |u| := abs_pos.mpr hu
    have hab : w / |u| ≤ (w + t) / |u| :=
      (div_le_div_iff_of_pos_right habs).2 (by linarith)
    have hstep : m * (t / |u|) ≤ h ((w + t) / |u|) - h (w / |u|) := by
      have hh := hs (w / |u|) ((w + t) / |u|) hab
      convert hh using 1
      ring
    have hmul := mul_le_mul_of_nonneg_left hstep habs.le
    have hcancel : |u| * (m * (t / |u|)) = m * t := by
      field_simp [habs.ne']
    rw [hcancel] at hmul
    simp only [angularLift, hu, if_false]
    change |u| * h (w / |u|) + m * t ≤ |u| * h ((w + t) / |u|)
    nlinarith

theorem angularLift_hasDirectionalLowerBound
    {hMinus hPlus : ℝ → ℝ} {m : ℝ}
    (hMinusSlope : HasLowerSlope hMinus m)
    (hPlusSlope : HasLowerSlope hPlus m) (hm : m ≤ 1) :
    HasDirectionalLowerBound (angularLift hMinus hPlus) (0, 1) m := by
  intro z t ht
  change angularLift hMinus hPlus z + m * t ≤
    angularLift hMinus hPlus (z.1 + t * 0, z.2 + t * 1)
  simpa using angularLift_vertical_increment hMinusSlope hPlusSlope hm z.1 z.2 t ht

/-- The actual homogeneous lift has no zero Clarke subgradient whenever its
profiles have a strictly positive lower slope. -/
theorem angularLift_zero_not_mem_clarkeSubdifferential
    {hMinus hPlus : ℝ → ℝ} {m : ℝ}
    (hMinusSlope : HasLowerSlope hMinus m)
    (hPlusSlope : HasLowerSlope hPlus m) (hm : 0 < m) (hm1 : m ≤ 1)
    (x : ℝ × ℝ) :
    (0 : (ℝ × ℝ) →L[ℝ] ℝ) ∉ clarkeSubdifferential (angularLift hMinus hPlus) x :=
  zero_not_mem_clarkeSubdifferential
    (angularLift_hasDirectionalLowerBound hMinusSlope hPlusSlope hm1) hm x

end

end BFGS
