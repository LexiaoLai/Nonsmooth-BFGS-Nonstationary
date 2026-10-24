import BFGS.Analysis.FiniteInterpolation

/-! Deterministic least-degree polynomial profiles with affine tails.
There is no choice of an unspecified interpolating function: each bridge
uses the least natural degree satisfying the displayed three inequalities. -/
namespace BFGS
noncomputable section

def canonicalBridgeDegree {m p q P Q Δ : ℝ}
    (hp : m < p) (hq : m < q) (hΔ : m < Δ) : ℕ := by
  classical
  exact Nat.find (exists_bridge_degree (P := P) (Q := Q) hp hq hΔ)

theorem canonicalBridgeDegree_spec {m p q P Q Δ : ℝ}
    (hp : m < p) (hq : m < q) (hΔ : m < Δ) :
    0 ≤ bridgeLeft (canonicalBridgeDegree (P := P) (Q := Q) hp hq hΔ) m p P ∧
    bridgeRight (canonicalBridgeDegree (P := P) (Q := Q) hp hq hΔ) m q Q ≤ 0 ∧
    bridgeBaseIntegral (canonicalBridgeDegree (P := P) (Q := Q) hp hq hΔ) m p q P Q < Δ := by
  classical
  exact Nat.find_spec (exists_bridge_degree (P := P) (Q := Q) hp hq hΔ)

theorem canonicalBridgeDegree_min {m p q P Q Δ : ℝ}
    (hp : m < p) (hq : m < q) (hΔ : m < Δ) {n : ℕ}
    (hn : n < canonicalBridgeDegree (P := P) (Q := Q) hp hq hΔ) :
    ¬ (0 ≤ bridgeLeft n m p P ∧ bridgeRight n m q Q ≤ 0 ∧
      bridgeBaseIntegral n m p q P Q < Δ) := by
  classical
  exact Nat.find_min (exists_bridge_degree (P := P) (Q := Q) hp hq hΔ) hn

def canonicalUnitBridge {m p q P Q Δ : ℝ}
    (hp : m < p) (hq : m < q) (hΔ : m < Δ) :
    {H : Polynomial ℝ //
      H.eval 0 = 0 ∧ H.eval 1 = Δ ∧
      H.derivative.eval 0 = p ∧ H.derivative.eval 1 = q ∧
      H.derivative.derivative.eval 0 = P ∧ H.derivative.derivative.eval 1 = Q ∧
      ∀ x ∈ Set.Icc (0 : ℝ) 1, m ≤ H.derivative.eval x} := by
  let n := canonicalBridgeDegree (P := P) (Q := Q) hp hq hΔ
  obtain ⟨hL, hR, hbase⟩ := canonicalBridgeDegree_spec (P := P) (Q := Q) hp hq hΔ
  let c := 30 * (Δ - bridgeBaseIntegral n m p q P Q)
  have hc : 0 < c := by dsimp [c]; linarith
  refine ⟨bridgePolynomial n m p q P Q c, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp
  · rw [bridgePolynomial_eval, bridgePrimitive_one]
    dsimp [c]
    ring
  · simp
  · simp
  · simp
  · simp
  · intro x hx
    rw [bridgePolynomial_derivative_eval]
    exact bridgeDerivative_lower n hp.le hq.le hL hR hc.le hx.1 hx.2

def canonicalPolynomialBridge
    {a b A B m p q P Q : ℝ} (hab : a < b)
    (hp : m < p) (hq : m < q) (hAB : m * (b - a) < B - A) :
    {H : Polynomial ℝ //
      H.eval a = A ∧ H.eval b = B ∧
      H.derivative.eval a = p ∧ H.derivative.eval b = q ∧
      H.derivative.derivative.eval a = P ∧ H.derivative.derivative.eval b = Q ∧
      ∀ x ∈ Set.Icc a b, m ≤ H.derivative.eval x} := by
  let L := b - a
  have hL : 0 < L := sub_pos.mpr hab
  obtain ⟨K, hK0, hK1, hp0, hq1, hP0, hQ1, hbound⟩ :=
    canonicalUnitBridge
      (p := p * L) (q := q * L) (P := P * L ^ 2) (Q := Q * L ^ 2)
      (mul_lt_mul_of_pos_right hp hL) (mul_lt_mul_of_pos_right hq hL) hAB
  refine ⟨rescalePolynomial K a A L, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hK0]
  · simp [L, hL.ne', hK1]
  · simp [hp0, hL.ne']
  · simp [L, hL.ne', hq1]
  · simp [hP0, hL.ne']
  · simp [L, hL.ne', hQ1]
  · intro x hx
    have hx0 : 0 ≤ (x - a) / L := div_nonneg (sub_nonneg.mpr hx.1) hL.le
    have hx1 : (x - a) / L ≤ 1 := by
      apply (div_le_iff₀ hL).2
      dsimp [L]
      linarith [hx.2]
    have hh := hbound ((x - a) / L) ⟨hx0, hx1⟩
    rw [rescalePolynomial_derivative_eval]
    exact (le_div_iff₀ hL).2 hh

private theorem canonical_node_le_of_adjacent {t : ℕ → ℝ} {n i j : ℕ}
    (ht : ∀ k < n, t k < t (k + 1)) (hij : i ≤ j) (hjn : j ≤ n) :
    t i ≤ t j := by
  revert hjn
  induction j, hij using Nat.le_induction with
  | base => intro _; exact le_rfl
  | succ j hij ih =>
      intro hjn
      exact (ih (by omega)).trans (ht j (by omega)).le

def canonicalPartialProfile (n : ℕ) (t A p P : ℕ → ℝ) (m : ℝ)
    (hm0 : m ≤ p 0) (hP0 : P 0 = 0)
    (hstep : ∀ i < n, t i < t (i + 1) ∧ m < p i ∧ m < p (i + 1) ∧
      m * (t (i + 1) - t i) < A (i + 1) - A i) :
    {f : C2Profile // PiecewisePolynomial f.value ∧
      (∀ i ≤ n, MatchesJet f (t i) (A i) (p i) (P i)) ∧
      (∀ x ≤ t n, m ≤ f.slope x) ∧
      (∀ x ≤ t 0, f.value x = p 0 * x + (A 0 - p 0 * t 0))} := by
  induction n with
  | zero =>
      refine ⟨C2Profile.affine (p 0) (A 0 - p 0 * t 0),
        C2Profile.affine_piecewisePolynomial _ _, ?_, ?_, ?_⟩
      · intro i hi
        have hi0 : i = 0 := by omega
        subst i
        simp only [MatchesJet, C2Profile.affine_value, C2Profile.affine_slope,
          C2Profile.affine_curvature]
        exact ⟨by ring, trivial, hP0.symm⟩
      · intro x _
        simpa using hm0
      · intro x _
        exact C2Profile.affine_value _ _ _
  | succ n ih =>
      obtain ⟨f, hpoly, hmatch, hbound, hleft⟩ := ih (fun i hi ↦ hstep i (by omega))
      obtain ⟨ht, hp, hq, hAB⟩ := hstep n (by omega)
      obtain ⟨H, hHa, hHb, hHpa, hHpb, hHPa, hHPb, hHbound⟩ :=
        canonicalPolynomialBridge (P := P n) (Q := P (n + 1)) ht hp hq hAB
      let g := C2Profile.ofPolynomial H
      have hlast := hmatch n le_rfl
      have hv : f.value (t n) = g.value (t n) := hlast.1.trans hHa.symm
      have hs : f.slope (t n) = g.slope (t n) := hlast.2.1.trans hHpa.symm
      have hc : f.curvature (t n) = g.curvature (t n) := hlast.2.2.trans hHPa.symm
      let F := f.glue g (t n) hv hs hc
      have hmono : ∀ i ≤ n, t i ≤ t n := fun i hi ↦
        canonical_node_le_of_adjacent (fun k hk ↦ (hstep k (by omega)).1) hi le_rfl
      refine ⟨F, C2Profile.glue_piecewisePolynomial f g (t n) hv hs hc hpoly
        (PiecewisePolynomial.polynomial H), ?_, ?_, ?_⟩
      · intro i hi
        by_cases hin : i ≤ n
        · simpa [F, C2Profile.glue, MatchesJet, glueAt, hmono i hin] using hmatch i hin
        · have hieq : i = n + 1 := by omega
          subst i
          simp only [F, C2Profile.glue, MatchesJet, glueAt, not_le_of_gt ht, if_false]
          exact ⟨hHb, hHpb, hHPb⟩
      · intro x hx
        by_cases hxn : x ≤ t n
        · simpa [F, C2Profile.glue, glueAt, hxn] using hbound x hxn
        · simpa [F, C2Profile.glue, glueAt, hxn, g, C2Profile.ofPolynomial] using
            hHbound x ⟨(lt_of_not_ge hxn).le, hx⟩
      · intro x hx
        have hxn : x ≤ t n := hx.trans (hmono 0 (Nat.zero_le n))
        simpa [F, C2Profile.glue, glueAt, hxn] using hleft x hx

/-- Finite interpolation with a globally positive derivative floor, genuine
`C²` regularity and explicit finite piecewise-polynomial representation.
Zero curvatures at the outer nodes allow affine tails with the outer slopes. -/
def canonicalProfile (n : ℕ) (t A p P : ℕ → ℝ) (m : ℝ)
    (hm0 : m ≤ p 0) (hP0 : P 0 = 0) (hPn : P n = 0)
    (hstep : ∀ i < n, t i < t (i + 1) ∧ m < p i ∧ m < p (i + 1) ∧
      m * (t (i + 1) - t i) < A (i + 1) - A i) :
    {f : C2Profile // PiecewisePolynomial f.value ∧
      (∀ i ≤ n, MatchesJet f (t i) (A i) (p i) (P i)) ∧
      (∀ x, m ≤ f.slope x) ∧
      (∀ x ≤ t 0, f.value x = p 0 * x + (A 0 - p 0 * t 0)) ∧
      (∀ x, t n ≤ x → f.value x = p n * x + (A n - p n * t n))} := by
  obtain ⟨f, hpoly, hmatch, hbound, hleft⟩ :=
    canonicalPartialProfile n t A p P m hm0 hP0 hstep
  let g := C2Profile.affine (p n) (A n - p n * t n)
  have hlast := hmatch n le_rfl
  have hv : f.value (t n) = g.value (t n) := by
    rw [hlast.1]
    simp [g]
  have hs : f.slope (t n) = g.slope (t n) := by simpa [g] using hlast.2.1
  have hc : f.curvature (t n) = g.curvature (t n) := by simpa [g, hPn] using hlast.2.2
  let F := f.glue g (t n) hv hs hc
  have hmono : ∀ i ≤ n, t i ≤ t n := fun i hi ↦
    canonical_node_le_of_adjacent (fun k hk ↦ (hstep k hk).1) hi le_rfl
  have hpn : m ≤ p n := by simpa [hlast.2.1] using hbound (t n) le_rfl
  refine ⟨F, C2Profile.glue_piecewisePolynomial f g (t n) hv hs hc hpoly
    (C2Profile.affine_piecewisePolynomial _ _), ?_, ?_, ?_, ?_⟩
  · intro i hi
    simpa [F, C2Profile.glue, MatchesJet, glueAt, hmono i hi] using hmatch i hi
  · intro x
    by_cases hx : x ≤ t n
    · simpa [F, C2Profile.glue, glueAt, hx] using hbound x hx
    · simpa [F, C2Profile.glue, glueAt, hx, g] using hpn
  · intro x hx
    have hxn : x ≤ t n := hx.trans (hmono 0 (Nat.zero_le n))
    simpa [F, C2Profile.glue, glueAt, hxn] using hleft x hx
  · intro x hx
    by_cases hxn : x ≤ t n
    · have heq : x = t n := le_antisymm hxn hx
      subst x
      simp [F, C2Profile.glue, glueAt, hlast.1]
    · simp [F, C2Profile.glue, glueAt, hxn, g]

end
end BFGS
