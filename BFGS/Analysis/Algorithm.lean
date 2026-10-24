import Mathlib

/-!
# Algebra of the actual two-dimensional inverse-BFGS update

This module proves facts about the ordinary update and the Armijo–Wolfe search. It does not assert that the interpolated objective
has already been constructed in Lean.
-/
namespace BFGS
namespace Algorithm

noncomputable section
open Classical

abbrev Vec := ℝ × ℝ

def dot (x y : Vec) : ℝ := x.1 * y.1 + x.2 * y.2

@[ext] structure Sym2 where
  a : ℝ
  b : ℝ
  d : ℝ
  deriving DecidableEq

def Sym2.mulV (H : Sym2) (x : Vec) : Vec :=
  (H.a * x.1 + H.b * x.2, H.b * x.1 + H.d * x.2)

def Sym2.scale (t : ℝ) (H : Sym2) : Sym2 := ⟨t*H.a,t*H.b,t*H.d⟩

def Sym2.quad (H : Sym2) (x : Vec) : ℝ := dot x (H.mulV x)

def Sym2.Positive (H : Sym2) : Prop := ∀ x : Vec, x ≠ 0 → 0 < H.quad x

/-- The expanded ordinary inverse-BFGS formula. -/
def update (H : Sym2) (s y : Vec) : Sym2 :=
  let c := dot s y
  let h := H.mulV y
  let b := (1 + dot y h / c) / c
  ⟨H.a - 2*h.1*s.1/c + b*s.1*s.1,
   H.b - (h.1*s.2+s.1*h.2)/c + b*s.1*s.2,
   H.d - 2*h.2*s.2/c + b*s.2*s.2⟩

theorem secant_identity (H : Sym2) (s y : Vec) (hc : dot s y ≠ 0) :
    (update H s y).mulV y = s := by
  rcases s with ⟨s₁,s₂⟩
  rcases y with ⟨y₁,y₂⟩
  simp only [dot] at hc
  apply Prod.ext <;> dsimp [update, Sym2.mulV, dot]
  all_goals
    generalize heq : s₁*y₁+s₂*y₂ = c at *
    field_simp [hc]
    rw [← heq]
    ring

/-- The rank-two matrix update has the usual positive quadratic-form representation. -/
theorem quadratic_update (H : Sym2) (s y w : Vec) (hc : dot s y ≠ 0) :
    (update H s y).quad w =
      H.quad (w - (dot s w / dot s y) • y) + (dot s w)^2 / dot s y := by
  rcases s with ⟨s₁,s₂⟩
  rcases y with ⟨y₁,y₂⟩
  rcases w with ⟨w₁,w₂⟩
  simp only [update, Sym2.quad, Sym2.mulV, dot, Prod.fst_sub, Prod.snd_sub,
    Prod.smul_mk, smul_eq_mul]
  simp only [dot] at hc
  field_simp [hc]
  ring

theorem update_positive (H : Sym2) (s y : Vec)
    (hH : H.Positive) (hc : 0 < dot s y) : (update H s y).Positive := by
  intro w hw
  rw [quadratic_update H s y w hc.ne']
  have hnonneg : ∀ z : Vec, 0 ≤ H.quad z := by
    intro z
    by_cases hz : z = 0
    · subst z; simp [Sym2.quad, Sym2.mulV, dot]
    · exact (hH z hz).le
  by_cases hsw : dot s w = 0
  · simpa [hsw] using hH w hw
  · exact add_pos_of_nonneg_of_pos (hnonneg _)
      (div_pos (sq_pos_of_ne_zero hsw) hc)

theorem update_scale (H : Sym2) (s y : Vec) (t : ℝ)
    (ht : t ≠ 0) (hc : dot s y ≠ 0) :
    update (H.scale t) (t • s) y = (update H s y).scale t := by
  rcases s with ⟨s₁,s₂⟩
  rcases y with ⟨y₁,y₂⟩
  simp only [dot] at hc
  have htc : t*s₁*y₁+t*s₂*y₂ ≠ 0 := by
    rw [show t*s₁*y₁+t*s₂*y₂ = t*(s₁*y₁+s₂*y₂) by ring]
    exact mul_ne_zero ht hc
  apply Sym2.ext <;>
    simp only [update, Sym2.scale, Sym2.mulV, dot, Prod.smul_mk, smul_eq_mul]
  all_goals
    ring_nf at hc htc
    field_simp [ht,hc,htc]

/-- Homogeneity also holds for the totalized formula at zero curvature.
Actual BFGS trajectories use the positive-curvature theorem above. -/
theorem update_scale_total (H : Sym2) (s y : Vec) (t : ℝ) (ht : t ≠ 0) :
    update (H.scale t) (t • s) y = (update H s y).scale t := by
  by_cases hc : dot s y = 0
  · have htc : dot (t • s) y = 0 := by
      dsimp [dot] at hc ⊢
      calc
        t*s.1*y.1+t*s.2*y.2 = t*(s.1*y.1+s.2*y.2) := by ring
        _ = 0 := by rw [hc,mul_zero]
    simp [update,hc,htc,Sym2.scale]
  · exact update_scale H s y t ht hc

def gradientFunctional (g : Vec) : Vec →L[ℝ] ℝ :=
  g.1 • ContinuousLinearMap.fst ℝ ℝ ℝ +
  g.2 • ContinuousLinearMap.snd ℝ ℝ ℝ

def IsGradientAt (f : Vec → ℝ) (g x : Vec) : Prop :=
  HasFDerivAt f (gradientFunctional g) x

def armijo (f : Vec → ℝ) (x p g : Vec) (c₁ α : ℝ) : Prop :=
  f (x + α • p) < f x + c₁ * α * dot g p

def weakWolfe (g : Vec → Vec) (x p : Vec) (c₂ α : ℝ) : Prop :=
  c₂ * dot (g x) p < dot (g (x + α • p)) p

/-- Finite-budget Armijo–Wolfe search on smooth trial points. `none` means
fuel exhausted. At smooth trials the gradient gives the line derivative used
by Algorithm 1; the constructed runs prove this smoothness.
No correspondence at nonsmooth trial points is assumed. -/
def lineSearch (f : Vec → ℝ) (g : Vec → Vec) (x p : Vec) (c₁ c₂ : ℝ) :
    ℕ → ℝ → Option ℝ → ℝ → Option ℝ
  | 0, _, _, _ => none
  | n+1, lo, hi, α =>
    if ¬ armijo f x p (g x) c₁ α then
      lineSearch f g x p c₁ c₂ n lo (some α) ((lo+α)/2)
    else if ¬ weakWolfe g x p c₂ α then
      let next := match hi with | none => 2*α | some b => (α+b)/2
      lineSearch f g x p c₁ c₂ n α hi next
    else some α

theorem lineSearch_halfstep (f : Vec → ℝ) (g : Vec → Vec) (x p : Vec)
    (c₁ c₂ : ℝ) (fuel : ℕ)
    (hu : ¬ armijo f x p (g x) c₁ 1)
    (ha : armijo f x p (g x) c₁ (1/2))
    (hw : weakWolfe g x p c₂ (1/2)) :
    lineSearch f g x p c₁ c₂ (fuel+2) 0 none 1 = some (1/2) := by
  simp only [one_div] at ha hw ⊢
  simp [lineSearch, hu, ha, hw]

theorem weakWolfe_positive_curvature (g₀ g₁ p : Vec) (α c₂ : ℝ)
    (hα : 0 < α) (hc₂ : c₂ < 1) (hd : dot g₀ p < 0)
    (hw : c₂ * dot g₀ p < dot g₁ p) :
    0 < dot (α • p) (g₁-g₀) := by
  have hi : dot g₀ p < c₂ * dot g₀ p := by nlinarith
  have hj : 0 < dot g₁ p - dot g₀ p := by linarith
  have he : dot (α • p) (g₁-g₀) = α*(dot g₁ p-dot g₀ p) := by
    simp [dot]; ring
  rw [he]
  exact mul_pos hα hj

end
end Algorithm
end BFGS
