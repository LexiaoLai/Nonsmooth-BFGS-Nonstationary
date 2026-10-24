import BFGS.Analysis.PolynomialBridge

/-!
# Gluing angular profiles with matching two-jets

`C2Profile` records ordinary real derivatives, not an uninterpreted
smoothness certificate. The gluing theorem proves differentiability at the
joining point by joining the two one-sided derivative filters. Consequently
the polynomial bridges may be assembled finitely without leaving analytic
boundary conditions as assumptions about a newly chosen function.
-/

namespace BFGS

noncomputable section

open Filter Set
open scoped ContDiff

def glueAt (c : ℝ) (f g : ℝ → ℝ) (x : ℝ) : ℝ := if x ≤ c then f x else g x

/-- A concrete finite piecewise-polynomial representation. -/
inductive PiecewisePolynomial : (ℝ → ℝ) → Prop
  | polynomial (P : Polynomial ℝ) : PiecewisePolynomial (fun x ↦ P.eval x)
  | glue {f g : ℝ → ℝ} (c : ℝ) :
      PiecewisePolynomial f → PiecewisePolynomial g → PiecewisePolynomial (glueAt c f g)

theorem hasDerivAt_glueAt {c : ℝ} {f g f' g' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hg : ∀ x, HasDerivAt g (g' x) x)
    (hval : f c = g c) (hderiv : f' c = g' c) (x : ℝ) :
    HasDerivAt (glueAt c f g) (glueAt c f' g' x) x := by
  rcases lt_trichotomy x c with hx | hx | hx
  · have heq : glueAt c f g =ᶠ[nhds x] f := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      change y < c at hy
      simp [glueAt, hy.le]
    simpa [glueAt, hx.le] using (hf x).congr_of_eventuallyEq heq
  · subst x
    have hl : HasDerivWithinAt (glueAt c f g) (f' c) (Iic c) c := by
      apply (hf c).hasDerivWithinAt.congr_of_mem
      · intro y hy
        change y ≤ c at hy
        simp [glueAt, hy]
      · exact mem_Iic.mpr le_rfl
    have hr : HasDerivWithinAt (glueAt c f g) (f' c) (Ici c) c := by
      rw [hderiv]
      apply (hg c).hasDerivWithinAt.congr_of_mem
      · intro y hy
        change c ≤ y at hy
        by_cases hc : y ≤ c
        · have heq : y = c := le_antisymm hc hy
          subst y
          simpa [glueAt] using hval
        · simp [glueAt, hc]
      · exact mem_Ici.mpr le_rfl
    have h := hl.union hr
    simpa [Iic_union_Ici, hasDerivWithinAt_univ, glueAt] using h
  · have heq : glueAt c f g =ᶠ[nhds x] g := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      change c < y at hy
      simp [glueAt, not_le_of_gt hy]
    simpa [glueAt, not_le_of_gt hx] using (hg x).congr_of_eventuallyEq heq

theorem continuous_glueAt {c : ℝ} {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hval : f c = g c) :
    Continuous (glueAt c f g) := by
  have hboundary : ∀ x ∈ frontier (Iic c), f x = g x := by
    intro x hx
    rw [frontier_Iic, mem_singleton_iff] at hx
    simpa [hx] using hval
  exact hf.if hboundary hg

/-- A profile with genuine first and second derivatives and continuous
curvature. Its `ContDiff ℝ 2` property is derived below. -/
structure C2Profile where
  value : ℝ → ℝ
  slope : ℝ → ℝ
  curvature : ℝ → ℝ
  value_hasDerivAt : ∀ x, HasDerivAt value (slope x) x
  slope_hasDerivAt : ∀ x, HasDerivAt slope (curvature x) x
  continuous_curvature : Continuous curvature

namespace C2Profile

private theorem polynomial_hasDerivAt (P : Polynomial ℝ) (x : ℝ) :
    HasDerivAt (fun t ↦ P.eval t) (P.derivative.eval x) x := by
  exact P.hasDerivAt x

def ofPolynomial (P : Polynomial ℝ) : C2Profile where
  value := fun x ↦ P.eval x
  slope := fun x ↦ P.derivative.eval x
  curvature := fun x ↦ P.derivative.derivative.eval x
  value_hasDerivAt := polynomial_hasDerivAt P
  slope_hasDerivAt := polynomial_hasDerivAt P.derivative
  continuous_curvature := P.derivative.derivative.continuous

def affine (a b : ℝ) : C2Profile :=
  ofPolynomial (Polynomial.C a * Polynomial.X + Polynomial.C b)

@[simp] theorem affine_value (a b x : ℝ) : (affine a b).value x = a * x + b := by
  simp [affine, ofPolynomial]

@[simp] theorem affine_slope (a b x : ℝ) : (affine a b).slope x = a := by
  simp [affine, ofPolynomial, Polynomial.derivative_mul]

@[simp] theorem affine_curvature (a b x : ℝ) : (affine a b).curvature x = 0 := by
  simp [affine, ofPolynomial, Polynomial.derivative_mul]

theorem affine_piecewisePolynomial (a b : ℝ) : PiecewisePolynomial (affine a b).value :=
  PiecewisePolynomial.polynomial _

theorem continuous_value (f : C2Profile) : Continuous f.value :=
  continuous_iff_continuousAt.mpr fun x ↦ (f.value_hasDerivAt x).continuousAt

theorem continuous_slope (f : C2Profile) : Continuous f.slope :=
  continuous_iff_continuousAt.mpr fun x ↦ (f.slope_hasDerivAt x).continuousAt

@[simp] theorem deriv_value (f : C2Profile) : deriv f.value = f.slope :=
  funext fun x ↦ (f.value_hasDerivAt x).deriv

@[simp] theorem deriv_slope (f : C2Profile) : deriv f.slope = f.curvature :=
  funext fun x ↦ (f.slope_hasDerivAt x).deriv

theorem contDiff_slope (f : C2Profile) : ContDiff ℝ 1 f.slope := by
  rw [contDiff_one_iff_deriv, deriv_slope]
  exact ⟨fun x ↦ (f.slope_hasDerivAt x).differentiableAt, f.continuous_curvature⟩

theorem contDiff_value (f : C2Profile) : ContDiff ℝ 2 f.value := by
  rw [show (2 : ℕ∞ω) = 1 + 1 by rfl, contDiff_succ_iff_deriv, deriv_value]
  refine ⟨fun x ↦ (f.value_hasDerivAt x).differentiableAt, ?_, f.contDiff_slope⟩
  intro h
  simp at h

/-- Two profiles with matching values, slopes and curvatures glue to a
genuine globally `C²` profile. This operation can be iterated finitely. -/
def glue (f g : C2Profile) (c : ℝ)
    (hval : f.value c = g.value c) (hslope : f.slope c = g.slope c)
    (hcurv : f.curvature c = g.curvature c) : C2Profile where
  value := glueAt c f.value g.value
  slope := glueAt c f.slope g.slope
  curvature := glueAt c f.curvature g.curvature
  value_hasDerivAt := hasDerivAt_glueAt f.value_hasDerivAt g.value_hasDerivAt hval hslope
  slope_hasDerivAt := hasDerivAt_glueAt f.slope_hasDerivAt g.slope_hasDerivAt hslope hcurv
  continuous_curvature := continuous_glueAt f.continuous_curvature g.continuous_curvature hcurv

theorem glue_piecewisePolynomial (f g : C2Profile) (c : ℝ)
    (hval : f.value c = g.value c) (hslope : f.slope c = g.slope c)
    (hcurv : f.curvature c = g.curvature c)
    (hf : PiecewisePolynomial f.value) (hg : PiecewisePolynomial g.value) :
    PiecewisePolynomial (f.glue g c hval hslope hcurv).value :=
  PiecewisePolynomial.glue c hf hg

theorem glue_slope_lower (f g : C2Profile) (c : ℝ)
    (hval : f.value c = g.value c) (hslope : f.slope c = g.slope c)
    (hcurv : f.curvature c = g.curvature c) {m : ℝ}
    (hf : ∀ x ≤ c, m ≤ f.slope x) (hg : ∀ x, c < x → m ≤ g.slope x) :
    ∀ x, m ≤ (f.glue g c hval hslope hcurv).slope x := by
  intro x
  change m ≤ if x ≤ c then f.slope x else g.slope x
  split_ifs with hx
  · exact hf x hx
  · exact hg x (lt_of_not_ge hx)

end C2Profile

end

end BFGS
