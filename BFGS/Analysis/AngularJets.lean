import BFGS.Analysis.AngularGeometry
import BFGS.Analysis.Algorithm

/-! The actual Fréchet derivatives of the angular objective on each open
half-plane. Coordinates are arbitrary linear functionals, allowing the
orthogonal physical coordinates to be substituted without a chain-rule gap. -/
namespace BFGS
noncomputable section
open Algorithm

@[simp] theorem gradientFunctional_apply (g x : Vec) :
    gradientFunctional g x = dot g x := by rfl

theorem gradientFunctional_smul (c : ℝ) (g : Vec) :
    gradientFunctional (c • g) = c • gradientFunctional g := by
  apply ContinuousLinearMap.ext
  intro x
  simp [gradientFunctional]
  ring

theorem gradientFunctional_add (g h : Vec) :
    gradientFunctional (g+h) = gradientFunctional g+gradientFunctional h := by
  apply ContinuousLinearMap.ext
  intro x
  simp [gradientFunctional]
  ring

def perspectiveRatio (a b x : Vec) : ℝ := dot b x / dot a x

def physicalPerspective (h : C2Profile) (a b x : Vec) : ℝ :=
  dot a x * h.value (perspectiveRatio a b x)

def perspectiveGradient (h : C2Profile) (a b x : Vec) : Vec :=
  (h.value (perspectiveRatio a b x) -
    perspectiveRatio a b x * h.slope (perspectiveRatio a b x)) • a +
    h.slope (perspectiveRatio a b x) • b

def ratioDifferential (a b x : Vec) : Vec →L[ℝ] ℝ :=
  (dot a x)⁻¹ • (gradientFunctional b - perspectiveRatio a b x • gradientFunctional a)

theorem hasFDerivAt_perspectiveRatio (a b x : Vec) (ha : dot a x ≠ 0) :
    HasFDerivAt (perspectiveRatio a b) (ratioDifferential a b x) x := by
  have hi := (hasDerivAt_inv ha).comp_hasFDerivAt x (gradientFunctional a).hasFDerivAt
  have hd := (gradientFunctional b).hasFDerivAt.mul hi
  convert hd using 1 <;> try rfl
  apply ContinuousLinearMap.ext
  intro z
  simp only [ratioDifferential, perspectiveRatio, smul_apply,
    add_apply, sub_apply, smul_eq_mul,
    gradientFunctional_apply, Function.comp_apply]
  field_simp [ha]
  ring

theorem hasFDerivAt_physicalPerspective (h : C2Profile) (a b x : Vec)
    (ha : dot a x ≠ 0) :
    IsGradientAt (physicalPerspective h a b) (perspectiveGradient h a b x) x := by
  have hr := hasFDerivAt_perspectiveRatio a b x ha
  have hh := (h.value_hasDerivAt (perspectiveRatio a b x)).comp_hasFDerivAt x hr
  have hd := (gradientFunctional a).hasFDerivAt.mul hh
  unfold IsGradientAt
  convert hd using 1 <;> try rfl
  rw [perspectiveGradient, gradientFunctional_add, gradientFunctional_smul,
    gradientFunctional_smul]
  apply ContinuousLinearMap.ext
  intro z
  simp only [ratioDifferential, perspectiveRatio, smul_apply,
    add_apply, sub_apply, smul_eq_mul,
    gradientFunctional_apply, Function.comp_apply]
  field_simp [ha]
  ring

def perspectiveHessian (h : C2Profile) (a b x : Vec) : Vec →L[ℝ] Vec :=
  (ratioDifferential a b x).smulRight
    (h.curvature (perspectiveRatio a b x) • (b-perspectiveRatio a b x • a))

theorem hasFDerivAt_perspectiveGradient (h : C2Profile) (a b x : Vec)
    (ha : dot a x ≠ 0) :
    HasFDerivAt (perspectiveGradient h a b) (perspectiveHessian h a b x) x := by
  have hr := hasFDerivAt_perspectiveRatio a b x ha
  have hh := (h.value_hasDerivAt (perspectiveRatio a b x)).comp_hasFDerivAt x hr
  have hs := (h.slope_hasDerivAt (perspectiveRatio a b x)).comp_hasFDerivAt x hr
  have hu := hh.sub (hr.mul hs)
  have hd := (hu.smul_const a).add (hs.smul_const b)
  convert hd using 1 <;> try rfl
  apply ContinuousLinearMap.ext
  intro z
  apply Prod.ext <;> simp [perspectiveHessian, ContinuousLinearMap.smulRight_apply] <;> ring


/-- The globally defined objective in arbitrary physical linear coordinates. -/
def physicalAngular (hMinus hPlus : C2Profile) (e v x : Vec) : ℝ :=
  angularLift hMinus.value hPlus.value (dot e x, dot v x)

def physicalAngularGradient (hMinus hPlus : C2Profile) (e v x : Vec) : Vec :=
  if dot e x < 0 then perspectiveGradient hMinus (-e) v x
  else perspectiveGradient hPlus e v x

def physicalAngularHessian (hMinus hPlus : C2Profile) (e v x : Vec) : Vec →L[ℝ] Vec :=
  if dot e x < 0 then perspectiveHessian hMinus (-e) v x
  else perspectiveHessian hPlus e v x

private theorem eventually_dot_pos (e x : Vec) (hx : 0 < dot e x) :
    ∀ᶠ z in nhds x, 0 < dot e z :=
  (isOpen_lt continuous_const (gradientFunctional e).continuous).mem_nhds hx

private theorem eventually_dot_neg (e x : Vec) (hx : dot e x < 0) :
    ∀ᶠ z in nhds x, dot e z < 0 :=
  (isOpen_lt (gradientFunctional e).continuous continuous_const).mem_nhds hx

@[simp] theorem dot_neg_left (e x : Vec) : dot (-e) x = - dot e x := by
  simp [dot]
  ring

theorem physicalAngular_eventuallyEq_pos (hMinus hPlus : C2Profile)
    (e v x : Vec) (hx : 0 < dot e x) :
    physicalAngular hMinus hPlus e v =ᶠ[nhds x] physicalPerspective hPlus e v := by
  filter_upwards [eventually_dot_pos e x hx] with z hz
  simp [physicalAngular, angularLift, hz.ne', not_lt.mpr hz.le, abs_of_pos hz,
    physicalPerspective, perspectiveRatio]

theorem physicalAngular_eventuallyEq_neg (hMinus hPlus : C2Profile)
    (e v x : Vec) (hx : dot e x < 0) :
    physicalAngular hMinus hPlus e v =ᶠ[nhds x] physicalPerspective hMinus (-e) v := by
  filter_upwards [eventually_dot_neg e x hx] with z hz
  simp [physicalAngular, angularLift, hz.ne, hz, abs_of_neg hz,
    physicalPerspective, perspectiveRatio]

theorem physicalAngularGradient_eventuallyEq_pos (hMinus hPlus : C2Profile)
    (e v x : Vec) (hx : 0 < dot e x) :
    physicalAngularGradient hMinus hPlus e v =ᶠ[nhds x]
      perspectiveGradient hPlus e v := by
  filter_upwards [eventually_dot_pos e x hx] with z hz
  simp [physicalAngularGradient, not_lt.mpr hz.le]

theorem physicalAngularGradient_eventuallyEq_neg (hMinus hPlus : C2Profile)
    (e v x : Vec) (hx : dot e x < 0) :
    physicalAngularGradient hMinus hPlus e v =ᶠ[nhds x]
      perspectiveGradient hMinus (-e) v := by
  filter_upwards [eventually_dot_neg e x hx] with z hz
  simp [physicalAngularGradient, hz]

theorem physicalAngular_isGradientAt (hMinus hPlus : C2Profile)
    (e v x : Vec) (hx : dot e x ≠ 0) :
    IsGradientAt (physicalAngular hMinus hPlus e v)
      (physicalAngularGradient hMinus hPlus e v x) x := by
  rcases lt_or_gt_of_ne hx with hm | hp
  · have ha : dot (-e) x ≠ 0 := by simpa only [dot_neg_left, neg_ne_zero] using hx
    have hg := hasFDerivAt_physicalPerspective hMinus (-e) v x ha
    simpa only [IsGradientAt, physicalAngularGradient, hm, if_true] using
      hg.congr_of_eventuallyEq (physicalAngular_eventuallyEq_neg hMinus hPlus e v x hm)
  · have hg := hasFDerivAt_physicalPerspective hPlus e v x hx
    simpa only [IsGradientAt, physicalAngularGradient, not_lt.mpr hp.le, if_false] using
      hg.congr_of_eventuallyEq (physicalAngular_eventuallyEq_pos hMinus hPlus e v x hp)

theorem physicalAngularGradient_hasFDerivAt (hMinus hPlus : C2Profile)
    (e v x : Vec) (hx : dot e x ≠ 0) :
    HasFDerivAt (physicalAngularGradient hMinus hPlus e v)
      (physicalAngularHessian hMinus hPlus e v x) x := by
  rcases lt_or_gt_of_ne hx with hm | hp
  · have ha : dot (-e) x ≠ 0 := by simpa only [dot_neg_left, neg_ne_zero] using hx
    have hg := hasFDerivAt_perspectiveGradient hMinus (-e) v x ha
    simpa only [physicalAngularHessian, hm, if_true] using
      hg.congr_of_eventuallyEq (physicalAngularGradient_eventuallyEq_neg hMinus hPlus e v x hm)
  · have hg := hasFDerivAt_perspectiveGradient hPlus e v x hx
    simpa only [physicalAngularHessian, not_lt.mpr hp.le, if_false] using
      hg.congr_of_eventuallyEq (physicalAngularGradient_eventuallyEq_pos hMinus hPlus e v x hp)

open scoped ContDiff

theorem physicalPerspective_contDiffAt (h : C2Profile) (a b x : Vec)
    (ha : dot a x ≠ 0) : ContDiffAt ℝ 2 (physicalPerspective h a b) x := by
  have hu : ContDiffAt ℝ 2 (dot a) x := (gradientFunctional a).contDiff.contDiffAt
  have hw : ContDiffAt ℝ 2 (dot b) x := (gradientFunctional b).contDiff.contDiffAt
  have hr : ContDiffAt ℝ 2 (perspectiveRatio a b) x := hw.div hu ha
  exact hu.mul (h.contDiff_value.contDiffAt.comp x hr)

theorem physicalAngular_contDiffAt (hMinus hPlus : C2Profile)
    (e v x : Vec) (hx : dot e x ≠ 0) :
    ContDiffAt ℝ 2 (physicalAngular hMinus hPlus e v) x := by
  rcases lt_or_gt_of_ne hx with hm | hp
  · exact (physicalPerspective_contDiffAt hMinus (-e) v x (by simpa using hx)).congr_of_eventuallyEq
      (physicalAngular_eventuallyEq_neg hMinus hPlus e v x hm)
  · exact (physicalPerspective_contDiffAt hPlus e v x hx).congr_of_eventuallyEq
      (physicalAngular_eventuallyEq_pos hMinus hPlus e v x hp)

/-- The elementary identity needed to interpret angular jets as physical jets. -/
def CoordinateExpansion (a b : Vec) : Prop :=
  ∀ z : Vec, dot a z • a + dot b z • b = z

theorem coordinateExpansion_rotation (p q : ℝ) (hn : p^2+q^2=1) :
    CoordinateExpansion (p,q) (-q,p) := by
  intro z
  apply Prod.ext <;> simp [dot]
  · nlinarith [congrArg (fun t : ℝ ↦ t*z.1) hn]
  · nlinarith [congrArg (fun t : ℝ ↦ t*z.2) hn]

theorem CoordinateExpansion.neg_left {a b : Vec} (h : CoordinateExpansion a b) :
    CoordinateExpansion (-a) b := by
  intro z
  simpa only [dot_neg_left, neg_smul, smul_neg, neg_neg] using h z

theorem perspectiveGradient_eq_of_jet (h : C2Profile) (a b x g : Vec)
    (ha : dot a x ≠ 0) (hbasis : CoordinateExpansion a b)
    (hvalue : h.value (perspectiveRatio a b x) = dot g x / dot a x)
    (hslope : h.slope (perspectiveRatio a b x) = dot b g) :
    perspectiveGradient h a b x = g := by
  have hEuler : dot g x = dot a g * dot a x + dot b g * dot b x := by
    have he := congrArg (fun z ↦ dot z x) (hbasis g)
    simp only [dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul] at he ⊢
    nlinarith [he]
  have hcoef : h.value (perspectiveRatio a b x) -
      perspectiveRatio a b x * h.slope (perspectiveRatio a b x) = dot a g := by
    rw [hvalue, hslope, perspectiveRatio, hEuler]
    field_simp
    ring
  rw [perspectiveGradient, hcoef, hslope]
  exact hbasis g


@[simp] theorem dot_smul_left (c : ℝ) (a b : Vec) : dot (c • a) b = c * dot a b := by
  simp [dot]
  ring

@[simp] theorem dot_smul_right (c : ℝ) (a b : Vec) : dot a (c • b) = c * dot a b := by
  simp [dot]
  ring

@[simp] theorem dot_comm (a b : Vec) : dot a b = dot b a := by
  simp only [dot]
  ring

/-- A symmetric planar map annihilating a nonvertical ray is determined by
its value on the transverse basis vector. This is the physical Hessian
reconstruction used by angular interpolation. -/
theorem symmetric_kernel_rankOne (L : Vec →L[ℝ] Vec) (a b x : Vec)
    (ha : dot a x ≠ 0) (hbasis : CoordinateExpansion a b)
    (hsym : ∀ z w, dot z (L w) = dot (L z) w) (hkernel : L x = 0) :
    ∀ z, L z = (dot b (L b) *
      (dot b z-perspectiveRatio a b x * dot a z)) •
      (b-perspectiveRatio a b x • a) := by
  let t := perspectiveRatio a b x
  have hlin : dot a x • L a + dot b x • L b = 0 := by
    simpa only [map_add, map_smul, hkernel] using congrArg L (hbasis x)
  have hA : dot a x • L a = (-dot b x) • L b := by
    simpa only [neg_smul] using eq_neg_of_add_eq_zero_left hlin
  have hLa : L a = (-t) • L b := by
    calc
      L a = (dot a x)⁻¹ • (dot a x • L a) := by rw [inv_smul_smul₀ ha]
      _ = (dot a x)⁻¹ • ((-dot b x) • L b) := by rw [hA]
      _ = (-t) • L b := by
        rw [smul_smul]
        congr 1
        simp only [t, perspectiveRatio, div_eq_mul_inv]
        ring
  have hproj : dot a (L b) = -t * dot b (L b) := by
    rw [hsym, hLa, dot_smul_left, dot_comm (L b) b]
  have hLb : L b = dot b (L b) • (b-t • a) := by
    calc
      L b = dot a (L b) • a+dot b (L b) • b := (hbasis (L b)).symm
      _ = dot b (L b) • (b-t • a) := by
        rw [hproj]
        apply Prod.ext <;> simp <;> ring
  intro z
  calc
    L z = dot a z • L a + dot b z • L b := by
      simpa only [map_add, map_smul] using (congrArg L (hbasis z)).symm
    _ = _ := by
      conv_lhs => rw [hLa, hLb]
      apply Prod.ext <;> simp [t] <;> ring

theorem perspectiveHessian_eq_of_jet (h : C2Profile) (a b x : Vec)
    (L : Vec →L[ℝ] Vec) (ha : dot a x ≠ 0)
    (hbasis : CoordinateExpansion a b)
    (hsym : ∀ z w, dot z (L w) = dot (L z) w) (hkernel : L x = 0)
    (hcurvature : h.curvature (perspectiveRatio a b x) = dot a x * dot b (L b)) :
    perspectiveHessian h a b x = L := by
  apply ContinuousLinearMap.ext
  intro z
  rw [symmetric_kernel_rankOne L a b x ha hbasis hsym hkernel]
  simp only [perspectiveHessian, ratioDifferential, ContinuousLinearMap.smulRight_apply,
    smul_apply, sub_apply, smul_eq_mul, gradientFunctional_apply, hcurvature]
  apply Prod.ext <;> simp
  all_goals field_simp [ha]


/-- The continuous linear coordinate change used by the actual objective. -/
def angularCoordinates (e v : Vec) : Vec →L[ℝ] Vec :=
  (gradientFunctional e).prod (gradientFunctional v)

@[simp] theorem angularCoordinates_apply (e v x : Vec) :
    angularCoordinates e v x = (dot e x, dot v x) := rfl

theorem physicalAngular_pos_homogeneous (hMinus hPlus : C2Profile)
    (e v x : Vec) (r : ℝ) (hr : 0 < r) :
    physicalAngular hMinus hPlus e v (r • x) = r * physicalAngular hMinus hPlus e v x := by
  change angularLift hMinus.value hPlus.value (angularCoordinates e v (r • x)) =
    r * angularLift hMinus.value hPlus.value (angularCoordinates e v x)
  rw [map_smul]
  exact angularLift_pos_homogeneous hMinus.value hPlus.value _ hr

theorem physicalAngular_hasDirectionalLowerBound (hMinus hPlus : C2Profile)
    (e v : Vec) (m : ℝ) (hev : dot e v = 0) (hvv : dot v v = 1)
    (hm : m ≤ 1) (hMinusSlope : ∀ t, m ≤ hMinus.slope t)
    (hPlusSlope : ∀ t, m ≤ hPlus.slope t) :
    HasDirectionalLowerBound (physicalAngular hMinus hPlus e v) v m := by
  have hM := hasLowerSlope_of_hasDerivAt hMinus.value_hasDerivAt hMinusSlope
  have hP := hasLowerSlope_of_hasDerivAt hPlus.value_hasDerivAt hPlusSlope
  exact (angularLift_hasDirectionalLowerBound hM hP hm).comp_linear
    (angularCoordinates e v) (by simp [hev, hvv])

theorem physicalAngular_zero_not_mem_clarkeSubdifferential (hMinus hPlus : C2Profile)
    (e v : Vec) (m : ℝ) (hev : dot e v = 0) (hvv : dot v v = 1)
    (hm0 : 0 < m) (hm1 : m ≤ 1) (hMinusSlope : ∀ t, m ≤ hMinus.slope t)
    (hPlusSlope : ∀ t, m ≤ hPlus.slope t) (x : Vec) :
    0 ∉ clarkeSubdifferential (physicalAngular hMinus hPlus e v) x := by
  exact zero_not_mem_clarkeSubdifferential
    (physicalAngular_hasDirectionalLowerBound hMinus hPlus e v m hev hvv hm1
      hMinusSlope hPlusSlope) hm0 x

theorem physicalAngular_lipschitz_of_affine_tails (hMinus hPlus : C2Profile)
    (e v : Vec)
    {aMinus bMinus leftMinus rightMinus aPlus bPlus leftPlus rightPlus : ℝ}
    (hMinusLeft : ∀ t ≤ aMinus, hMinus.value t = t + leftMinus)
    (hMinusRight : ∀ t, bMinus ≤ t → hMinus.value t = t + rightMinus)
    (hPlusLeft : ∀ t ≤ aPlus, hPlus.value t = t + leftPlus)
    (hPlusRight : ∀ t, bPlus ≤ t → hPlus.value t = t + rightPlus) :
    ∃ K : NNReal, LipschitzWith K (physicalAngular hMinus hPlus e v) := by
  obtain ⟨K, hK⟩ := angularLift_lipschitz_of_affine_tails hMinus hPlus
    hMinusLeft hMinusRight hPlusLeft hPlusRight
  exact ⟨_, hK.comp (angularCoordinates e v).lipschitz⟩

theorem perspectiveRatio_scale (a b x : Vec) (r : ℝ) (hr : r ≠ 0) :
    perspectiveRatio a b (r • x) = perspectiveRatio a b x := by
  simp only [perspectiveRatio, dot_smul_right]
  exact mul_div_mul_left _ _ hr

theorem perspectiveGradient_scale (h : C2Profile) (a b x : Vec) (r : ℝ) (hr : r ≠ 0) :
    perspectiveGradient h a b (r • x) = perspectiveGradient h a b x := by
  simp only [perspectiveGradient, perspectiveRatio_scale a b x r hr]

theorem physicalAngularGradient_scale (hMinus hPlus : C2Profile)
    (e v x : Vec) (r : ℝ) (hr : 0 < r) :
    physicalAngularGradient hMinus hPlus e v (r • x) =
      physicalAngularGradient hMinus hPlus e v x := by
  have hsign : r * dot e x < 0 ↔ dot e x < 0 := by
    simpa only [mul_zero] using (mul_lt_mul_iff_right₀ hr : r * dot e x < r * 0 ↔ dot e x < 0)
  simp only [physicalAngularGradient, dot_smul_right, hsign,
    perspectiveGradient_scale _ _ _ _ _ hr.ne']


/-- Interpret a matched angular value and slope in the physical basis. -/
theorem physicalAngularGradient_eq_of_jet (hMinus hPlus : C2Profile)
    (e v x g : Vec) (hx : dot e x ≠ 0) (hbasis : CoordinateExpansion e v)
    (hvalue : (if dot e x < 0 then hMinus else hPlus).value
      (dot v x / |dot e x|) = dot g x / |dot e x|)
    (hslope : (if dot e x < 0 then hMinus else hPlus).slope
      (dot v x / |dot e x|) = dot v g) :
    physicalAngularGradient hMinus hPlus e v x = g := by
  rcases lt_or_gt_of_ne hx with hm | hp
  · have ha : dot (-e) x ≠ 0 := by simpa only [dot_neg_left, neg_ne_zero] using hx
    simp only [hm, if_true, abs_of_neg hm] at hvalue hslope
    simp only [physicalAngularGradient, hm, if_true]
    exact perspectiveGradient_eq_of_jet hMinus (-e) v x g ha hbasis.neg_left
      (by simpa only [perspectiveRatio, dot_neg_left] using hvalue)
      (by simpa only [perspectiveRatio, dot_neg_left] using hslope)
  · simp only [not_lt.mpr hp.le, if_false, abs_of_pos hp] at hvalue hslope
    simp only [physicalAngularGradient, not_lt.mpr hp.le, if_false]
    exact perspectiveGradient_eq_of_jet hPlus e v x g hx hbasis hvalue hslope

theorem physicalAngular_value_of_jet (hMinus hPlus : C2Profile)
    (e v x : Vec) (A : ℝ) (hx : dot e x ≠ 0)
    (hvalue : (if dot e x < 0 then hMinus else hPlus).value
      (dot v x / |dot e x|) = A / |dot e x|) :
    physicalAngular hMinus hPlus e v x = A := by
  have habs : |dot e x| ≠ 0 := abs_ne_zero.mpr hx
  unfold physicalAngular angularLift
  simp only [hx, if_false]
  have he : (if dot e x < 0 then hMinus.value else hPlus.value)
      (dot v x / |dot e x|) = A / |dot e x| := by
    split_ifs with hh <;> simpa only [hh, if_true, if_false] using hvalue
  rw [he]
  exact mul_div_cancel₀ A habs


theorem physicalAngularHessian_eq_of_jet (hMinus hPlus : C2Profile)
    (e v x : Vec) (L : Vec →L[ℝ] Vec) (hx : dot e x ≠ 0)
    (hbasis : CoordinateExpansion e v)
    (hsym : ∀ z w, dot z (L w) = dot (L z) w) (hkernel : L x = 0)
    (hcurvature : (if dot e x < 0 then hMinus else hPlus).curvature
      (dot v x / |dot e x|) = |dot e x| * dot v (L v)) :
    physicalAngularHessian hMinus hPlus e v x = L := by
  rcases lt_or_gt_of_ne hx with hm | hp
  · have ha : dot (-e) x ≠ 0 := by simpa only [dot_neg_left, neg_ne_zero] using hx
    simp only [hm, if_true, abs_of_neg hm] at hcurvature
    simp only [physicalAngularHessian, hm, if_true]
    exact perspectiveHessian_eq_of_jet hMinus (-e) v x L ha hbasis.neg_left hsym hkernel
      (by simpa only [perspectiveRatio, dot_neg_left] using hcurvature)
  · simp only [not_lt.mpr hp.le, if_false, abs_of_pos hp] at hcurvature
    simp only [physicalAngularHessian, not_lt.mpr hp.le, if_false]
    exact perspectiveHessian_eq_of_jet hPlus e v x L hx hbasis hsym hkernel hcurvature

theorem perspectiveHessian_scale (h : C2Profile) (a b x : Vec) (r : ℝ) (hr : r ≠ 0) :
    perspectiveHessian h a b (r • x) = r⁻¹ • perspectiveHessian h a b x := by
  apply ContinuousLinearMap.ext
  intro z
  simp only [perspectiveHessian, ratioDifferential, perspectiveRatio_scale a b x r hr,
    dot_smul_right, ContinuousLinearMap.smulRight_apply, smul_apply, sub_apply,
    smul_eq_mul, gradientFunctional_apply]
  apply Prod.ext <;> simp [mul_inv_rev] <;> ring

theorem physicalAngularHessian_scale (hMinus hPlus : C2Profile)
    (e v x : Vec) (r : ℝ) (hr : 0 < r) :
    physicalAngularHessian hMinus hPlus e v (r • x) =
      r⁻¹ • physicalAngularHessian hMinus hPlus e v x := by
  have hsign : r * dot e x < 0 ↔ dot e x < 0 := by
    simpa only [mul_zero] using (mul_lt_mul_iff_right₀ hr : r * dot e x < r * 0 ↔ dot e x < 0)
  simp only [physicalAngularHessian, dot_smul_right, hsign]
  split_ifs <;> exact perspectiveHessian_scale _ _ _ _ _ hr.ne'

end
end BFGS
