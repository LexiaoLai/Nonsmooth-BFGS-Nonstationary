import BFGS.Analysis.CanonicalProfile
import BFGS.Analysis.AngularJets
import BFGS.Analysis.EuclideanCoercive

/-!
# Analytic realization of the homogeneous objective

The coordinates are the nonorthogonal shear from Section 2.2. The results apply to the chosen interpolation data.
-/
namespace BFGS.Counterexample
noncomputable section
open Algorithm Filter Set Topology
open scoped ContDiff

/-- The rows of the inverse shear, and the primal separating direction. -/
def shearRow (q : ℝ) : Vec := (1, -q)
def verticalRow : Vec := (0, 1)
def shearDirection (q : ℝ) : Vec := (q, 1)

def shearObjective (q : ℝ) (hm hp : C2Profile) : Vec → ℝ :=
  physicalAngular hm hp (shearRow q) verticalRow

def shearGradient (q : ℝ) (hm hp : C2Profile) : Vec → Vec :=
  physicalAngularGradient hm hp (shearRow q) verticalRow

def shearHessian (q : ℝ) (hm hp : C2Profile) : Vec → (Vec →L[ℝ] Vec) :=
  physicalAngularHessian hm hp (shearRow q) verticalRow

@[simp] theorem shearRow_dot (q : ℝ) (x : Vec) :
    dot (shearRow q) x = x.1 - q*x.2 := by simp [shearRow, dot]; ring

@[simp] theorem verticalRow_dot (x : Vec) : dot verticalRow x = x.2 := by
  simp [verticalRow, dot]

@[simp] theorem shearDirection_dot (q : ℝ) (g : Vec) :
    dot g (shearDirection q) = q*g.1+g.2 := by simp [shearDirection, dot]; ring

@[simp] theorem shear_coordinates_direction (q : ℝ) :
    angularCoordinates (shearRow q) verticalRow (shearDirection q) = (0,1) := by
  simp [angularCoordinates_apply, shearDirection, shearRow, verticalRow, dot]

/-- Identity tails are stronger than the affine tails needed for global
Lipschitz continuity: they also remove the apparent chart-axis singularity. -/
def HasIdentityTails (h : C2Profile) : Prop :=
  ∃ R : ℝ, 0 < R ∧ ∀ t, R ≤ |t| → h.value t = t

theorem hasIdentityTails_of_two_tails (h : C2Profile) {a b : ℝ}
    (hl : ∀ t ≤ a, h.value t = t) (hr : ∀ t, b ≤ t → h.value t = t) :
    HasIdentityTails h := by
  refine ⟨1+|a|+|b|, by positivity, ?_⟩
  intro t ht
  rcases le_total t 0 with hn | hp
  · apply hl
    rw [abs_of_nonpos hn] at ht
    linarith [neg_abs_le a, abs_nonneg b]
  · apply hr
    rw [abs_of_nonneg hp] at ht
    linarith [le_abs_self b, abs_nonneg a]

/-- Finite monotone interpolation with identity outer data gives genuine
identity tails, with arbitrary interior second derivatives. -/
theorem exists_identity_profile (n : ℕ) (t A p P : ℕ → ℝ) (m : ℝ)
    (hm0 : m ≤ 1) (hA0 : A 0 = t 0) (hAn : A n = t n)
    (hp0 : p 0 = 1) (hpn : p n = 1) (hP0 : P 0 = 0) (hPn : P n = 0)
    (hstep : ∀ i < n, t i < t (i+1) ∧ m < p i ∧ m < p (i+1) ∧
      m*(t (i+1)-t i) < A (i+1)-A i) :
    ∃ h : C2Profile, PiecewisePolynomial h.value ∧
      (∀ i ≤ n, MatchesJet h (t i) (A i) (p i) (P i)) ∧
      (∀ x, m ≤ h.slope x) ∧ HasIdentityTails h := by
  obtain ⟨h, hpoly, hjets, hslope, hl, hr⟩ :=
    exists_finite_monotone_profile n t A p P m (by simpa [hp0] using hm0)
      hP0 hPn hstep
  refine ⟨h, hpoly, hjets, hslope, hasIdentityTails_of_two_tails h (a := t 0) (b := t n) ?_ ?_⟩
  · intro x hx
    simpa [hp0, hA0] using hl x hx
  · intro x hx
    simpa [hpn, hAn] using hr x hx

theorem shearObjective_pos_homogeneous (q : ℝ) (hm hp : C2Profile)
    (r : ℝ) (hr : 0 < r) (x : Vec) :
    shearObjective q hm hp (r • x) = r*shearObjective q hm hp x :=
  physicalAngular_pos_homogeneous hm hp (shearRow q) verticalRow x r hr

@[simp] theorem shearObjective_zero (q : ℝ) (hm hp : C2Profile) :
    shearObjective q hm hp 0 = 0 := by
  simp [shearObjective, physicalAngular, angularLift, dot]

theorem shearObjective_lipschitz (q : ℝ) (hm hp : C2Profile)
    (hmt : HasIdentityTails hm) (hpt : HasIdentityTails hp) :
    ∃ K : NNReal, LipschitzWith K (shearObjective q hm hp) := by
  obtain ⟨Rm, hRm, hm'⟩ := hmt
  obtain ⟨Rp, hRp, hp'⟩ := hpt
  apply physicalAngular_lipschitz_of_affine_tails hm hp (shearRow q) verticalRow
    (aMinus := -Rm) (bMinus := Rm) (leftMinus := 0) (rightMinus := 0)
    (aPlus := -Rp) (bPlus := Rp) (leftPlus := 0) (rightPlus := 0)
  · intro t ht; simpa using hm' t (by linarith [neg_le_abs t])
  · intro t ht; simpa using hm' t (ht.trans (le_abs_self t))
  · intro t ht; simpa using hp' t (by linarith [neg_le_abs t])
  · intro t ht; simpa using hp' t (ht.trans (le_abs_self t))

theorem shearObjective_directional_lower_bound (q m : ℝ) (hm hp : C2Profile)
    (hm1 : m ≤ 1) (hms : ∀ t, m ≤ hm.slope t) (hps : ∀ t, m ≤ hp.slope t) :
    HasDirectionalLowerBound (shearObjective q hm hp) (shearDirection q) m := by
  exact (angularLift_hasDirectionalLowerBound
    (hasLowerSlope_of_hasDerivAt hm.value_hasDerivAt hms)
    (hasLowerSlope_of_hasDerivAt hp.value_hasDerivAt hps) hm1).comp_linear
      (angularCoordinates (shearRow q) verticalRow) (shear_coordinates_direction q)

theorem shearObjective_nonstationary (q m : ℝ) (hm hp : C2Profile)
    (hm0 : 0 < m) (hm1 : m ≤ 1)
    (hms : ∀ t, m ≤ hm.slope t) (hps : ∀ t, m ≤ hp.slope t) (x : Vec) :
    0 ∉ clarkeSubdifferential (shearObjective q hm hp) x :=
  zero_not_mem_clarkeSubdifferential
    (shearObjective_directional_lower_bound q m hm hp hm1 hms hps) hm0 x

/-- On a cone adjacent to the nonzero chart axis both identity tails agree. -/
theorem angularLift_eq_vertical_of_tail_cone (hm hp : C2Profile) (R u w : ℝ)
    (hmt : ∀ t, R ≤ |t| → hm.value t = t)
    (hpt : ∀ t, R ≤ |t| → hp.value t = t)
    (hcone : R*|u| ≤ |w|) : angularLift hm.value hp.value (u,w) = w := by
  by_cases hu : u = 0
  · simp [hu]
  have hua : 0 < |u| := abs_pos.mpr hu
  have hratio : R ≤ |w / (|u|)| := by
    rw [abs_div, abs_abs]
    exact (le_div_iff₀ hua).mpr hcone
  by_cases hun : u < 0
  · simp only [angularLift, hu, if_false, hun, if_true, hmt _ hratio]
    field_simp
  · simp only [angularLift, hu, if_false, hun, hpt _ hratio]
    field_simp

/-- Identity tails imply exact local linearity at every nonzero axis point. -/
theorem shearObjective_eventuallyEq_axis (q : ℝ) (hm hp : C2Profile)
    (hmt : HasIdentityTails hm) (hpt : HasIdentityTails hp)
    (x : Vec) (hx : x ≠ 0) (hu : dot (shearRow q) x = 0) :
    shearObjective q hm hp =ᶠ[𝓝 x] (fun y : Vec => y.2) := by
  obtain ⟨Rm, _, hm'⟩ := hmt
  obtain ⟨Rp, _, hp'⟩ := hpt
  let R := max Rm Rp
  have hx2 : x.2 ≠ 0 := by
    intro hx2
    apply hx
    apply Prod.ext
    · simp only [shearRow_dot, hx2, mul_zero, sub_zero] at hu
      exact hu
    · exact hx2
  have hopen : IsOpen {y : Vec | R*|dot (shearRow q) y| < |y.2|} := by
    apply isOpen_lt
    · exact continuous_const.mul ((gradientFunctional (shearRow q)).continuous.abs)
    · exact continuous_snd.abs
  have hmem : x ∈ {y : Vec | R*|dot (shearRow q) y| < |y.2|} := by
    change R*|dot (shearRow q) x| < |x.2|
    simpa only [hu, abs_zero, mul_zero] using abs_pos.mpr hx2
  filter_upwards [hopen.mem_nhds hmem] with y hy
  unfold shearObjective physicalAngular
  rw [verticalRow_dot]
  apply angularLift_eq_vertical_of_tail_cone hm hp R
  · intro t ht; exact hm' t ((le_max_left _ _).trans ht)
  · intro t ht; exact hp' t ((le_max_right _ _).trans ht)
  · exact (show R*|dot (shearRow q) y| < |y.2| from hy).le

/-- The full punctured-plane C² claim, including the chart axis. -/
theorem shearObjective_contDiffAt (q : ℝ) (hm hp : C2Profile)
    (hmt : HasIdentityTails hm) (hpt : HasIdentityTails hp)
    (x : Vec) (hx : x ≠ 0) : ContDiffAt ℝ 2 (shearObjective q hm hp) x := by
  by_cases hu : dot (shearRow q) x = 0
  · exact contDiff_snd.contDiffAt.congr_of_eventuallyEq
      (shearObjective_eventuallyEq_axis q hm hp hmt hpt x hx hu)
  · exact physicalAngular_contDiffAt hm hp (shearRow q) verticalRow x hu

theorem shearObjective_gradient (q : ℝ) (hm hp : C2Profile)
    (x : Vec) (hx : dot (shearRow q) x ≠ 0) :
    IsGradientAt (shearObjective q hm hp) (shearGradient q hm hp x) x :=
  physicalAngular_isGradientAt hm hp (shearRow q) verticalRow x hx

theorem shearGradient_derivative (q : ℝ) (hm hp : C2Profile)
    (x : Vec) (hx : dot (shearRow q) x ≠ 0) :
    HasFDerivAt (shearGradient q hm hp) (shearHessian q hm hp x) x :=
  physicalAngularGradient_hasFDerivAt hm hp (shearRow q) verticalRow x hx

/-- The two scalar interpolation prescriptions reconstruct the full gradient
in shear coordinates; no orthogonality assumption is used. -/
theorem perspectiveGradient_shear_eq_of_jet (q σ : ℝ) (h : C2Profile) (x g : Vec)
    (ha : dot (σ, -σ*q) x ≠ 0)
    (hvalue : h.value (perspectiveRatio (σ,-σ*q) verticalRow x) =
      dot g x / dot (σ,-σ*q) x)
    (hslope : h.slope (perspectiveRatio (σ,-σ*q) verticalRow x) =
      dot g (shearDirection q)) :
    perspectiveGradient h (σ,-σ*q) verticalRow x = g := by
  let a : Vec := (σ,-σ*q)
  have hcoef : (h.value (perspectiveRatio a verticalRow x) -
      perspectiveRatio a verticalRow x*h.slope (perspectiveRatio a verticalRow x))*σ = g.1 := by
    rw [hvalue, hslope]
    calc
      (dot g x / dot a x - perspectiveRatio a verticalRow x *
          dot g (shearDirection q))*σ =
          ((dot g x - dot verticalRow x*dot g (shearDirection q))*σ) / dot a x := by
            simp only [perspectiveRatio]
            ring
      _ = (g.1*dot a x)/dot a x := by
        congr 1
        dsimp [a, dot, verticalRow, shearDirection]
        ring
      _ = g.1 := mul_div_cancel_right₀ g.1 ha
  apply Prod.ext
  · simpa only [perspectiveGradient, a, verticalRow, Prod.fst_add, Prod.smul_fst,
      smul_eq_mul, mul_zero, add_zero] using hcoef
  · simp only [perspectiveGradient, verticalRow, Prod.snd_add, Prod.smul_snd,
      smul_eq_mul, mul_one]
    change (h.value (perspectiveRatio a verticalRow x) -
      perspectiveRatio a verticalRow x*h.slope (perspectiveRatio a verticalRow x))*(-σ*q) +
        h.slope (perspectiveRatio a verticalRow x) = g.2
    rw [hslope, shearDirection_dot]
    dsimp [a] at hcoef ⊢
    rw [hslope, shearDirection_dot] at hcoef
    nlinarith [congrArg (fun t : ℝ => t*q) hcoef]

theorem shearGradient_eq_of_jet (q : ℝ) (hm hp : C2Profile) (x g : Vec)
    (hx : dot (shearRow q) x ≠ 0)
    (hvalue : (if dot (shearRow q) x < 0 then hm else hp).value
      (x.2 / |dot (shearRow q) x|) = dot g x / |dot (shearRow q) x|)
    (hslope : (if dot (shearRow q) x < 0 then hm else hp).slope
      (x.2 / |dot (shearRow q) x|) = dot g (shearDirection q)) :
    shearGradient q hm hp x = g := by
  rcases lt_or_gt_of_ne hx with hn | hp'
  · have ha : dot (-shearRow q) x ≠ 0 := by
      simpa only [dot_neg_left, neg_ne_zero] using hx
    simp only [hn, if_true, abs_of_neg hn] at hvalue hslope
    simp only [shearGradient, physicalAngularGradient, hn, if_true]
    have hrow : -shearRow q = (-1, -(-1)*q) := by
      simp [shearRow]
    rw [hrow] at ha ⊢
    apply perspectiveGradient_shear_eq_of_jet q (-1) hm x g ha
    · simpa [perspectiveRatio, verticalRow, dot, shearRow, add_comm] using hvalue
    · simpa [perspectiveRatio, verticalRow, dot, shearRow, add_comm] using hslope
  · simp only [not_lt.mpr hp'.le, if_false, abs_of_pos hp'] at hvalue hslope
    simp only [shearGradient, physicalAngularGradient, not_lt.mpr hp'.le, if_false]
    have hrow : shearRow q = (1, -1*q) := by simp [shearRow]
    rw [hrow]
    apply perspectiveGradient_shear_eq_of_jet q 1 hp x g
    · simpa [shearRow] using hx
    · simpa [perspectiveRatio, shearRow, verticalRow, dot] using hvalue
    · simpa [perspectiveRatio, shearRow, verticalRow, dot] using hslope

theorem shearObjective_value_of_jet (q : ℝ) (hm hp : C2Profile) (x : Vec) (A : ℝ)
    (hx : dot (shearRow q) x ≠ 0)
    (hvalue : (if dot (shearRow q) x < 0 then hm else hp).value
      (x.2 / |dot (shearRow q) x|) = A / |dot (shearRow q) x|) :
    shearObjective q hm hp x = A :=
  physicalAngular_value_of_jet hm hp (shearRow q) verticalRow x A hx
    (by simpa only [verticalRow_dot] using hvalue)

/-- Pairings with a nonaxis point and the primal shear direction determine
any planar vector. -/
theorem vec_eq_of_shear_pairings (q : ℝ) (x g h : Vec)
    (hx : dot (shearRow q) x ≠ 0)
    (hpoint : dot g x = dot h x)
    (hdir : dot g (shearDirection q) = dot h (shearDirection q)) : g = h := by
  have hdir' := congrArg (fun a : ℝ => a*x.2) hdir
  have hprod : (g.1-h.1)*(x.1-q*x.2) = 0 := by
    simp only [dot, shearDirection] at hpoint hdir'
    nlinarith [hpoint, hdir']
  have hx' : x.1-q*x.2 ≠ 0 := by simpa only [shearRow_dot] using hx
  have hfirst : g.1 = h.1 := sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right hx')
  apply Prod.ext hfirst
  simp only [shearDirection_dot, hfirst] at hdir
  linarith

/-- A symmetric map annihilating the prescribed ray is determined by its
quadratic form on the primal shear direction. -/
theorem symmetric_maps_eq_of_kernel_and_shear_entry
    (q : ℝ) (x : Vec) (L K : Vec →L[ℝ] Vec)
    (hx : dot (shearRow q) x ≠ 0)
    (hLs : ∀ z w, dot z (L w) = dot (L z) w)
    (hKs : ∀ z w, dot z (K w) = dot (K z) w)
    (hLx : L x = 0) (hKx : K x = 0)
    (hentry : dot (shearDirection q) (L (shearDirection q)) =
      dot (shearDirection q) (K (shearDirection q))) : L = K := by
  have hv : L (shearDirection q) = K (shearDirection q) := by
    apply vec_eq_of_shear_pairings q x _ _ hx
    · rw [dot_comm (L _), dot_comm (K _), hLs, hKs, hLx, hKx]
    · simpa only [dot_comm] using hentry
  apply ContinuousLinearMap.ext
  intro z
  apply vec_eq_of_shear_pairings q x _ _ hx
  · rw [dot_comm (L _), dot_comm (K _), hLs, hKs, hLx, hKx]
  · rw [dot_comm (L _), dot_comm (K _), hLs, hKs, hv]

theorem perspectiveHessian_symmetric (h : C2Profile) (a b x : Vec) :
    ∀ z w, dot z (perspectiveHessian h a b x w) =
      dot (perspectiveHessian h a b x z) w := by
  intro z w
  simp only [perspectiveHessian, ratioDifferential, ContinuousLinearMap.smulRight_apply,
    smul_apply, sub_apply,
    gradientFunctional_apply, dot, Prod.smul_fst, Prod.smul_snd,
    Prod.fst_sub, Prod.snd_sub, smul_eq_mul]
  ring

theorem perspectiveHessian_kernel (h : C2Profile) (a b x : Vec)
    (ha : dot a x ≠ 0) : perspectiveHessian h a b x x = 0 := by
  have hr : dot b x - perspectiveRatio a b x*dot a x = 0 := by
    simp only [perspectiveRatio, div_mul_cancel₀ _ ha, sub_self]
  simp only [perspectiveHessian, ratioDifferential, ContinuousLinearMap.smulRight_apply,
    smul_apply, sub_apply, gradientFunctional_apply,
    smul_eq_mul, hr, mul_zero, zero_smul]

theorem perspectiveHessian_primal_entry (h : C2Profile) (a b x v : Vec)
    (_ha : dot a x ≠ 0) (hav : dot a v = 0) (hbv : dot b v = 1) :
    dot v (perspectiveHessian h a b x v) =
      h.curvature (perspectiveRatio a b x) / dot a x := by
  have he : dot v (perspectiveHessian h a b x v) =
      ((dot a x)⁻¹ * (dot b v-perspectiveRatio a b x*dot a v)) *
        (h.curvature (perspectiveRatio a b x)*(dot b v-perspectiveRatio a b x*dot a v)) := by
    simp only [perspectiveHessian, ratioDifferential, ContinuousLinearMap.smulRight_apply,
      smul_apply, sub_apply,
      gradientFunctional_apply, dot, Prod.smul_fst, Prod.smul_snd,
      Prod.fst_sub, Prod.snd_sub, smul_eq_mul]
    ring
  rw [he, hav, hbv]
  simp [div_eq_mul_inv, mul_comm]

theorem perspectiveHessian_shear_eq_of_jet (q σ : ℝ) (h : C2Profile) (x : Vec)
    (L : Vec →L[ℝ] Vec) (hx : dot (shearRow q) x ≠ 0)
    (ha : dot (σ,-σ*q) x ≠ 0)
    (hsym : ∀ z w, dot z (L w) = dot (L z) w) (hkernel : L x = 0)
    (hcurvature : h.curvature (perspectiveRatio (σ,-σ*q) verticalRow x) =
      dot (σ,-σ*q) x * dot (shearDirection q) (L (shearDirection q))) :
    perspectiveHessian h (σ,-σ*q) verticalRow x = L := by
  apply symmetric_maps_eq_of_kernel_and_shear_entry q x _ L hx
    (perspectiveHessian_symmetric _ _ _ _) hsym
    (perspectiveHessian_kernel _ _ _ _ ha) hkernel
  rw [perspectiveHessian_primal_entry h (σ,-σ*q) verticalRow x (shearDirection q) ha]
  · rw [hcurvature]
    exact mul_div_cancel_left₀ _ ha
  · simp [dot, shearDirection]
  · simp [dot, verticalRow, shearDirection]

theorem shearHessian_eq_of_jet (q : ℝ) (hm hp : C2Profile) (x : Vec)
    (L : Vec →L[ℝ] Vec) (hx : dot (shearRow q) x ≠ 0)
    (hsym : ∀ z w, dot z (L w) = dot (L z) w) (hkernel : L x = 0)
    (hcurvature : (if dot (shearRow q) x < 0 then hm else hp).curvature
      (x.2 / |dot (shearRow q) x|) =
        |dot (shearRow q) x| * dot (shearDirection q) (L (shearDirection q))) :
    shearHessian q hm hp x = L := by
  rcases lt_or_gt_of_ne hx with hn | hp'
  · have ha : dot (-shearRow q) x ≠ 0 := by
      simpa only [dot_neg_left, neg_ne_zero] using hx
    simp only [hn, if_true, abs_of_neg hn] at hcurvature
    simp only [shearHessian, physicalAngularHessian, hn, if_true]
    have hrow : -shearRow q = (-1, -(-1)*q) := by simp [shearRow]
    rw [hrow] at ha ⊢
    apply perspectiveHessian_shear_eq_of_jet q (-1) hm x L hx ha hsym hkernel
    simpa [perspectiveRatio, verticalRow, dot, shearRow, add_comm] using hcurvature
  · simp only [not_lt.mpr hp'.le, if_false, abs_of_pos hp'] at hcurvature
    simp only [shearHessian, physicalAngularHessian, not_lt.mpr hp'.le, if_false]
    have hrow : shearRow q = (1, -1*q) := by simp [shearRow]
    rw [hrow]
    apply perspectiveHessian_shear_eq_of_jet q 1 hp x L hx
      (by simpa [shearRow] using hx) hsym hkernel
    simpa [perspectiveRatio, shearRow, verticalRow, dot] using hcurvature

end
end BFGS.Counterexample
