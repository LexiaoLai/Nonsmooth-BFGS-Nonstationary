import Mathlib

/-!
# Sound rational interval operations

This file proves semantic soundness of elementary interval operations. It does
not claim that the external Python root or Jacobian enclosures have been
replayed in Lean. A closed expression evaluator and the analytic root bridge
are separate obligations.
-/
namespace BFGS

structure RationalInterval where
  lo : ℚ
  hi : ℚ

namespace RationalInterval

def Contains (I : RationalInterval) (x : ℝ) : Prop :=
  (I.lo : ℝ) ≤ x ∧ x ≤ (I.hi : ℝ)

def point (q : ℚ) : RationalInterval := ⟨q, q⟩
def add (I J : RationalInterval) : RationalInterval := ⟨I.lo + J.lo, I.hi + J.hi⟩
def neg (I : RationalInterval) : RationalInterval := ⟨-I.hi, -I.lo⟩
def mul (I J : RationalInterval) : RationalInterval :=
  ⟨min (min (I.lo * J.lo) (I.lo * J.hi)) (min (I.hi * J.lo) (I.hi * J.hi)),
   max (max (I.lo * J.lo) (I.lo * J.hi)) (max (I.hi * J.lo) (I.hi * J.hi))⟩
def inv (I : RationalInterval) : RationalInterval := ⟨1 / I.hi, 1 / I.lo⟩

theorem contains_point (q : ℚ) : (point q).Contains (q : ℝ) := ⟨le_rfl, le_rfl⟩

theorem contains_widen {I J : RationalInterval} {x : ℝ}
    (hx : I.Contains x) (hlo : J.lo ≤ I.lo) (hhi : I.hi ≤ J.hi) : J.Contains x := by
  have hlo' : (J.lo : ℝ) ≤ (I.lo : ℝ) := by exact_mod_cast hlo
  have hhi' : (I.hi : ℝ) ≤ (J.hi : ℝ) := by exact_mod_cast hhi
  exact ⟨hlo'.trans hx.1, hx.2.trans hhi'⟩

theorem contains_add {I J : RationalInterval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) : (I.add J).Contains (x + y) := by
  constructor
  · simpa [add] using add_le_add hx.1 hy.1
  · simpa [add] using add_le_add hx.2 hy.2

theorem contains_neg {I : RationalInterval} {x : ℝ}
    (hx : I.Contains x) : I.neg.Contains (-x) := by
  constructor
  · simpa [neg] using neg_le_neg hx.2
  · simpa [neg] using neg_le_neg hx.1

private theorem min_mul_le {a b x c : ℝ} (hax : a ≤ x) (hxb : x ≤ b) :
    min (a*c) (b*c) ≤ x*c := by
  by_cases hc : 0 ≤ c
  · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_right hax hc)
  · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_right hxb (le_of_not_ge hc))

private theorem mul_le_max {a b x c : ℝ} (hax : a ≤ x) (hxb : x ≤ b) :
    x*c ≤ max (a*c) (b*c) := by
  by_cases hc : 0 ≤ c
  · exact (mul_le_mul_of_nonneg_right hxb hc).trans (le_max_right _ _)
  · exact (mul_le_mul_of_nonpos_right hax (le_of_not_ge hc)).trans (le_max_left _ _)

private theorem four_corner_bounds {a b c d x y : ℝ}
    (hax : a ≤ x) (hxb : x ≤ b) (hcy : c ≤ y) (hyd : y ≤ d) :
    min (min (a*c) (a*d)) (min (b*c) (b*d)) ≤ x*y ∧
      x*y ≤ max (max (a*c) (a*d)) (max (b*c) (b*d)) := by
  have ha : min (a*c) (a*d) ≤ a*y := by
    simpa [mul_comm] using (min_mul_le (c := a) hcy hyd)
  have hb : min (b*c) (b*d) ≤ b*y := by
    simpa [mul_comm] using (min_mul_le (c := b) hcy hyd)
  have ha' : a*y ≤ max (a*c) (a*d) := by
    simpa [mul_comm] using (mul_le_max (c := a) hcy hyd)
  have hb' : b*y ≤ max (b*c) (b*d) := by
    simpa [mul_comm] using (mul_le_max (c := b) hcy hyd)
  constructor
  · exact (le_min ((min_le_left _ _).trans ha) ((min_le_right _ _).trans hb)).trans
      (min_mul_le hax hxb)
  · exact (mul_le_max hax hxb).trans
      (max_le (ha'.trans (le_max_left _ _)) (hb'.trans (le_max_right _ _)))

theorem contains_mul {I J : RationalInterval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) : (I.mul J).Contains (x*y) := by
  simpa [Contains, mul] using four_corner_bounds hx.1 hx.2 hy.1 hy.2

theorem contains_inv_of_positive {I : RationalInterval} {x : ℝ}
    (hx : I.Contains x) (hlo : 0 < I.lo) : I.inv.Contains (1/x) := by
  have hp : 0 < (I.lo : ℝ) := by exact_mod_cast hlo
  have hxp : 0 < x := hp.trans_le hx.1
  constructor
  · simpa [inv] using one_div_le_one_div_of_le hxp hx.2
  · simpa [inv] using one_div_le_one_div_of_le hp hx.1

theorem contains_inv_of_negative {I : RationalInterval} {x : ℝ}
    (hx : I.Contains x) (hhi : I.hi < 0) : I.inv.Contains (1/x) := by
  have hp : 0 < I.neg.lo := by dsimp [neg]; linarith
  have h := contains_neg (contains_inv_of_positive (contains_neg hx) hp)
  simpa [Contains, inv, neg] using h

/-- A square-root enclosure verified by squaring rational endpoints. -/
theorem contains_sqrt {I J : RationalInterval} {x : ℝ}
    (hx : I.Contains x) (hI : 0 ≤ I.lo) (hJ : 0 ≤ J.lo)
    (hJh : 0 ≤ J.hi) (hlo : J.lo^2 ≤ I.lo) (hhi : I.hi ≤ J.hi^2) :
    J.Contains (Real.sqrt x) := by
  have hI' : (0 : ℝ) ≤ I.lo := by exact_mod_cast hI
  have hJ' : (0 : ℝ) ≤ J.lo := by exact_mod_cast hJ
  have hJh' : (0 : ℝ) ≤ J.hi := by exact_mod_cast hJh
  have hlo' : (J.lo : ℝ)^2 ≤ (I.lo : ℝ) := by exact_mod_cast hlo
  have hhi' : (I.hi : ℝ) ≤ (J.hi : ℝ)^2 := by exact_mod_cast hhi
  have hx0 : 0 ≤ x := hI'.trans hx.1
  have hs := Real.sq_sqrt hx0
  have hs0 := Real.sqrt_nonneg x
  constructor <;> dsimp [Contains] at * <;> nlinarith

end RationalInterval
end BFGS
