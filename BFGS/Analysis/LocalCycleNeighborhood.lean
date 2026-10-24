import BFGS.Analysis.StateSpace

/-! Positive definite matrices and finite iterates depend continuously
on the initial state. These local facts support the invariant-neighborhood
argument in Section 2.3. -/
namespace BFGS.LocalCycle
noncomputable section
open Algorithm BFGS.StateSpace Filter Topology

theorem positive_metric_iff (H : Algorithm.Sym2) :
    H.Positive ↔ 0 < H.a ∧ 0 < H.a*H.d-H.b^2 := by
  constructor
  · intro h
    have ha : 0 < H.a := by
      simpa [Algorithm.Sym2.quad, Algorithm.Sym2.mulV, dot] using
        h (1,0) (by norm_num)
    have hv : (-H.b,H.a) ≠ (0 : Vec) := by
      intro he
      have := congrArg Prod.snd he
      exact ha.ne' this
    have hq := h (-H.b,H.a) hv
    dsimp [Algorithm.Sym2.quad, Algorithm.Sym2.mulV, dot] at hq
    refine ⟨ha, ?_⟩
    have hp : 0 < H.a*(H.a*H.d-H.b^2) := by nlinarith [hq]
    exact (mul_pos_iff_of_pos_left ha).mp hp
  · rintro ⟨ha, hdet⟩ x hx
    have he : H.a * H.quad x =
        (H.a*x.1+H.b*x.2)^2+(H.a*H.d-H.b^2)*x.2^2 := by
      dsimp [Algorithm.Sym2.quad, Algorithm.Sym2.mulV, dot]
      ring
    have hp : 0 < H.a*H.quad x := by
      rw [he]
      by_cases hx2 : x.2 = 0
      · have hx1 : x.1 ≠ 0 := by
          intro hx1
          exact hx (Prod.ext hx1 hx2)
        simpa [hx2] using sq_pos_of_ne_zero (mul_ne_zero ha.ne' hx1)
      · exact add_pos_of_nonneg_of_pos (sq_nonneg _)
          (mul_pos hdet (sq_pos_of_ne_zero hx2))
    exact (mul_pos_iff_of_pos_left ha).mp hp

theorem metric_positive_eventually (z : State) (hz : (metric z).Positive) :
    ∀ᶠ w in 𝓝 z, (metric w).Positive := by
  obtain ⟨ha, hd⟩ := (positive_metric_iff _).mp hz
  have hca : ContinuousAt (fun w : State => w 2) z :=
    (continuous_apply 2).continuousAt
  have hcd : ContinuousAt (fun w : State => w 2*w 4-(w 3)^2) z := by fun_prop
  have hea := hca.eventually_const_lt ha
  have hed := hcd.eventually_const_lt hd
  filter_upwards [hea, hed] with w hwa hwd
  exact (positive_metric_iff _).mpr ⟨hwa,hwd⟩

theorem iterate_continuousAt_bounded (T : State → State) (z : State) (n : ℕ)
    (hT : ∀ k < n, ContinuousAt T (T^[k] z)) : ContinuousAt (T^[n]) z := by
  induction n with
  | zero => exact continuousAt_id
  | succ n ih =>
    rw [Function.iterate_succ']
    exact (hT n (Nat.lt_succ_self n)).comp
      (ih (fun k hk => hT k (Nat.lt_trans hk (Nat.lt_succ_self n))))

end
end BFGS.LocalCycle
