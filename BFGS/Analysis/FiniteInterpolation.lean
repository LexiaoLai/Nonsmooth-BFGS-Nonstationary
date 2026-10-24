import BFGS.Analysis.ProfileGluing

/-!
# Finite monotone two-jet interpolation with affine tails

The finite existence theorem below constructs profiles by polynomial
bridges and the proved `C²` gluing operation. The first and last prescribed
curvatures are zero, permitting affine tails; arbitrary original node data
can be supplemented with the two outer nodes used in the manuscript.
-/

namespace BFGS

noncomputable section

def MatchesJet (f : C2Profile) (t A p P : ℝ) : Prop :=
  f.value t = A ∧ f.slope t = p ∧ f.curvature t = P

private theorem node_le_of_adjacent {t : ℕ → ℝ} {n i j : ℕ}
    (ht : ∀ k < n, t k < t (k + 1)) (hij : i ≤ j) (hjn : j ≤ n) :
    t i ≤ t j := by
  revert hjn
  induction j, hij using Nat.le_induction with
  | base => intro _; exact le_rfl
  | succ j hij ih =>
      intro hjn
      exact (ih (by omega)).trans (ht j (by omega)).le

theorem exists_partial_monotone_profile (n : ℕ) (t A p P : ℕ → ℝ) (m : ℝ)
    (hm0 : m ≤ p 0) (hP0 : P 0 = 0)
    (hstep : ∀ i < n, t i < t (i + 1) ∧ m < p i ∧ m < p (i + 1) ∧
      m * (t (i + 1) - t i) < A (i + 1) - A i) :
    ∃ f : C2Profile, PiecewisePolynomial f.value ∧
      (∀ i ≤ n, MatchesJet f (t i) (A i) (p i) (P i)) ∧
      (∀ x ≤ t n, m ≤ f.slope x) ∧
      (∀ x ≤ t 0, f.value x = p 0 * x + (A 0 - p 0 * t 0)) := by
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
        exists_polynomial_monotone_twoJet (P := P n) (Q := P (n + 1)) ht hp hq hAB
      let g := C2Profile.ofPolynomial H
      have hlast := hmatch n le_rfl
      have hv : f.value (t n) = g.value (t n) := hlast.1.trans hHa.symm
      have hs : f.slope (t n) = g.slope (t n) := hlast.2.1.trans hHpa.symm
      have hc : f.curvature (t n) = g.curvature (t n) := hlast.2.2.trans hHPa.symm
      let F := f.glue g (t n) hv hs hc
      have hmono : ∀ i ≤ n, t i ≤ t n := fun i hi ↦
        node_le_of_adjacent (fun k hk ↦ (hstep k (by omega)).1) hi le_rfl
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
theorem exists_finite_monotone_profile (n : ℕ) (t A p P : ℕ → ℝ) (m : ℝ)
    (hm0 : m ≤ p 0) (hP0 : P 0 = 0) (hPn : P n = 0)
    (hstep : ∀ i < n, t i < t (i + 1) ∧ m < p i ∧ m < p (i + 1) ∧
      m * (t (i + 1) - t i) < A (i + 1) - A i) :
    ∃ f : C2Profile, PiecewisePolynomial f.value ∧
      (∀ i ≤ n, MatchesJet f (t i) (A i) (p i) (P i)) ∧
      (∀ x, m ≤ f.slope x) ∧
      (∀ x ≤ t 0, f.value x = p 0 * x + (A 0 - p 0 * t 0)) ∧
      (∀ x, t n ≤ x → f.value x = p n * x + (A n - p n * t n)) := by
  obtain ⟨f, hpoly, hmatch, hbound, hleft⟩ :=
    exists_partial_monotone_profile n t A p P m hm0 hP0 hstep
  let g := C2Profile.affine (p n) (A n - p n * t n)
  have hlast := hmatch n le_rfl
  have hv : f.value (t n) = g.value (t n) := by
    rw [hlast.1]
    simp [g]
  have hs : f.slope (t n) = g.slope (t n) := by simpa [g] using hlast.2.1
  have hc : f.curvature (t n) = g.curvature (t n) := by simpa [g, hPn] using hlast.2.2
  let F := f.glue g (t n) hv hs hc
  have hmono : ∀ i ≤ n, t i ≤ t n := fun i hi ↦
    node_le_of_adjacent (fun k hk ↦ (hstep k hk).1) hi le_rfl
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
