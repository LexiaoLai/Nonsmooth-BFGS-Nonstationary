import Mathlib

/-! Standard quantifier-free semialgebraic sets: finite Boolean combinations
of signs of multivariate real polynomials. No closure under projection is
postulated. Rational formulas are handled by clearing nonzero denominators. -/
namespace BFGS.Semialgebraic
noncomputable section
open Set

abbrev Space (n : ℕ) := Fin n → ℝ

def Poly {n : ℕ} (f : Space n → ℝ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ, ∀ x, MvPolynomial.eval x p = f x

namespace Poly
variable {n : ℕ} {f g : Space n → ℝ}
theorem const (c : ℝ) : Poly (fun _ : Space n => c) :=
  ⟨MvPolynomial.C c, by simp⟩
theorem coord (i : Fin n) : Poly (fun x : Space n => x i) :=
  ⟨MvPolynomial.X i, by simp⟩
theorem add (hf : Poly f) (hg : Poly g) : Poly (fun x => f x+g x) := by
  obtain ⟨p,hp⟩ := hf; obtain ⟨q,hq⟩ := hg
  exact ⟨p+q, by intro x; simp [hp,hq]⟩
theorem mul (hf : Poly f) (hg : Poly g) : Poly (fun x => f x*g x) := by
  obtain ⟨p,hp⟩ := hf; obtain ⟨q,hq⟩ := hg
  exact ⟨p*q, by intro x; simp [hp,hq]⟩
theorem neg (hf : Poly f) : Poly (fun x => -f x) := by
  obtain ⟨p,hp⟩ := hf
  exact ⟨-p, by intro x; simp [hp]⟩
theorem sub (hf : Poly f) (hg : Poly g) : Poly (fun x => f x-g x) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg
theorem pow (hf : Poly f) (k : ℕ) : Poly (fun x => f x^k) := by
  obtain ⟨p,hp⟩ := hf
  exact ⟨p^k, by intro x; simp [hp]⟩
end Poly

/-- A literal finite Boolean polynomial-sign definition of semialgebraicity. -/
inductive IsSemialgebraic {n : ℕ} : Set (Space n) → Prop
  | nonneg {f : Space n → ℝ} (hf : Poly f) :
      IsSemialgebraic {x | 0 ≤ f x}
  | inter {S T} : IsSemialgebraic S → IsSemialgebraic T → IsSemialgebraic (S ∩ T)
  | union {S T} : IsSemialgebraic S → IsSemialgebraic T → IsSemialgebraic (S ∪ T)
  | compl {S} : IsSemialgebraic S → IsSemialgebraic Sᶜ

namespace IsSemialgebraic
variable {n : ℕ} {f g : Space n → ℝ}
theorem univ : IsSemialgebraic (Set.univ : Set (Space n)) := by
  simpa using nonneg (Poly.const (n:=n) 0)
theorem le (hf : Poly f) (hg : Poly g) : IsSemialgebraic {x | f x ≤ g x} := by
  simpa only [sub_nonneg] using nonneg (hg.sub hf)
theorem lt (hf : Poly f) (hg : Poly g) : IsSemialgebraic {x | f x < g x} := by
  simpa only [compl_ofPred,not_le] using (le hg hf).compl
theorem eq (hf : Poly f) (hg : Poly g) : IsSemialgebraic {x | f x = g x} := by
  convert (le hf hg).inter (le hg hf) using 1
  ext x; simp only [mem_ofPred_eq,mem_inter_iff]; exact le_antisymm_iff
end IsSemialgebraic

/-- A single rational formula with its denominator proved nonzero on its domain. -/
def RationalOn {n : ℕ} (S : Set (Space n)) (f : Space n → ℝ) : Prop :=
  ∃ p q : Space n → ℝ, Poly p ∧ Poly q ∧
    (∀ x ∈ S, q x ≠ 0) ∧ (∀ x ∈ S, f x = p x/q x)

namespace RationalOn
variable {n : ℕ} {S T : Set (Space n)} {f g : Space n → ℝ}
theorem of_poly (hf : Poly f) : RationalOn S f :=
  ⟨f,fun _ => 1,hf,Poly.const 1,by simp,by simp⟩
theorem const (c : ℝ) : RationalOn S (fun _ => c) := of_poly (Poly.const c)
theorem mono (h : RationalOn S f) (hTS : T ⊆ S) : RationalOn T f := by
  obtain ⟨p,q,hp,hq,hn,hf⟩ := h
  exact ⟨p,q,hp,hq,fun x hx => hn x (hTS hx),fun x hx => hf x (hTS hx)⟩
theorem congr (h : RationalOn S f) (he : ∀ x ∈ S, f x = g x) : RationalOn S g := by
  obtain ⟨p,q,hp,hq,hn,hf⟩ := h
  exact ⟨p,q,hp,hq,hn,fun x hx => (he x hx).symm.trans (hf x hx)⟩
theorem add (hf : RationalOn S f) (hg : RationalOn S g) :
    RationalOn S (fun x => f x+g x) := by
  obtain ⟨p,q,hp,hq,hn,he⟩ := hf
  obtain ⟨r,s,hr,hs,hm,hj⟩ := hg
  refine ⟨fun x => p x*s x+r x*q x,fun x => q x*s x,
    (hp.mul hs).add (hr.mul hq),hq.mul hs,
    fun x hx => mul_ne_zero (hn x hx) (hm x hx),?_⟩
  intro x hx; dsimp only; rw [he x hx,hj x hx]; field_simp [hn x hx,hm x hx]
theorem mul (hf : RationalOn S f) (hg : RationalOn S g) :
    RationalOn S (fun x => f x*g x) := by
  obtain ⟨p,q,hp,hq,hn,he⟩ := hf
  obtain ⟨r,s,hr,hs,hm,hj⟩ := hg
  refine ⟨fun x => p x*r x,fun x => q x*s x,hp.mul hr,hq.mul hs,
    fun x hx => mul_ne_zero (hn x hx) (hm x hx),?_⟩
  intro x hx; dsimp only; rw [he x hx,hj x hx]; exact div_mul_div_comm _ _ _ _
theorem inv (hf : RationalOn S f) (hn : ∀ x ∈ S, f x ≠ 0) :
    RationalOn S (fun x => (f x)⁻¹) := by
  obtain ⟨p,q,hp,hq,hm,he⟩ := hf
  refine ⟨q,p,hq,hp,?_,?_⟩
  · intro x hx; have := hn x hx; rw [he x hx] at this
    exact (div_ne_zero_iff.mp this).1
  · intro x hx; dsimp only; rw [he x hx,inv_div]
theorem div (hf : RationalOn S f) (hg : RationalOn S g)
    (hn : ∀ x ∈ S, g x ≠ 0) : RationalOn S (fun x => f x/g x) := by
  simpa only [div_eq_mul_inv] using hf.mul (hg.inv hn)
theorem pow (hf : RationalOn S f) (k : ℕ) : RationalOn S (fun x => f x^k) := by
  induction k with
  | zero => simpa using (const (S:=S) 1)
  | succ k ih => simpa only [pow_succ] using ih.mul hf
theorem eval (hf : RationalOn S f) (P : Polynomial ℝ) :
    RationalOn S (fun x => P.eval (f x)) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => simpa only [Polynomial.eval_add] using hp.add hq
  | monomial k c => simpa only [Polynomial.eval_monomial] using (const c).mul (hf.pow k)
end RationalOn

/-- A finite cover by semialgebraic domains carrying rational formulas. -/
inductive PiecewiseRationalOn {n : ℕ} : Set (Space n) → (Space n → ℝ) → Prop
  | single {S f} : IsSemialgebraic S → RationalOn S f → PiecewiseRationalOn S f
  | union {S T f} : PiecewiseRationalOn S f → PiecewiseRationalOn T f →
      PiecewiseRationalOn (S ∪ T) f

namespace PiecewiseRationalOn
variable {n : ℕ} {S T : Set (Space n)} {f g : Space n → ℝ}
theorem congr (hf : PiecewiseRationalOn S f) (he : ∀ x ∈ S, f x=g x) :
    PiecewiseRationalOn S g := by
  induction hf with
  | single hS hr => exact single hS (hr.congr he)
  | union hS hT ihS ihT =>
    exact (ihS fun x hx => he x (Or.inl hx)).union (ihT fun x hx => he x (Or.inr hx))
theorem restrict (hf : PiecewiseRationalOn S f) (hT : IsSemialgebraic T) :
    PiecewiseRationalOn (S ∩ T) f := by
  induction hf with
  | single hS hr => exact single (hS.inter hT) (hr.mono inter_subset_left)
  | union hS hU ihS ihU => simpa only [union_inter_distrib_right] using ihS.union ihU

theorem graph (hf : PiecewiseRationalOn S f) (hg : Poly g) :
    IsSemialgebraic {x | x ∈ S ∧ f x=g x} := by
  induction hf with
  | single hS hr =>
    obtain ⟨p,q,hp,hq,hn,he⟩ := hr
    convert hS.inter (IsSemialgebraic.eq hp (hg.mul hq)) using 1
    ext x
    simp only [mem_ofPred_eq,mem_inter_iff]
    constructor
    · rintro ⟨hx,h⟩; refine ⟨hx,?_⟩
      rw [he x hx] at h; exact (div_eq_iff (hn x hx)).mp h
    · rintro ⟨hx,h⟩; refine ⟨hx,?_⟩
      rw [he x hx]; exact (div_eq_iff (hn x hx)).mpr h
  | union hS hT ihS ihT =>
    convert ihS.union ihT using 1
    ext x; simp only [mem_ofPred_eq,mem_union,or_and_right]
end PiecewiseRationalOn

end
end BFGS.Semialgebraic
