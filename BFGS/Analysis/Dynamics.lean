import Mathlib

/-!
# Homogeneous dynamics: the scale-decay part of the BFGS argument

These are reusable lemmas, not a formalization of the entire counterexample.
In particular, the invariant normalized neighborhood and the uniform phase
bounds are explicit hypotheses.  They must still be obtained from the
specific differentiable return map and its certified Lyapunov inequality.
-/

namespace BFGS

open Filter Topology

section Scalar

/-- A nonnegative multiplicative recurrence with factors bounded by `q` is
bounded by the geometric sequence with ratio `q`. -/
theorem scale_le_geometric (a b : ℕ → ℝ) (q : ℝ)
    (ha : 0 ≤ a 0) (hq : 0 ≤ q)
    (hrec : ∀ n, a (n + 1) = a n * b n)
    (hb : ∀ n, 0 ≤ b n ∧ b n ≤ q) :
    ∀ n, 0 ≤ a n ∧ a n ≤ a 0 * q ^ n := by
  intro n
  induction n with
  | zero => simpa using And.intro ha (le_refl (a 0))
  | succ n ih =>
    constructor
    · rw [hrec]
      exact mul_nonneg ih.1 (hb n).1
    · calc
        a (n + 1) = a n * b n := hrec n
        _ ≤ (a 0 * q ^ n) * q :=
          mul_le_mul ih.2 (hb n).2 (hb n).1
            (mul_nonneg ha (pow_nonneg hq n))
        _ = a 0 * q ^ (n + 1) := by rw [pow_succ]; ring

end Scalar

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Bounded normalized phases and geometrically shrinking scales imply
convergence to zero.  This permits the phase index to vary with `n`. -/
theorem scaled_phases_tendsto_zero
    (a b : ℕ → ℝ) (z : ℕ → E) (q M : ℝ)
    (ha : 0 ≤ a 0) (hq₀ : 0 ≤ q) (hq₁ : q < 1)
    (_hM : 0 ≤ M)
    (hrec : ∀ n, a (n + 1) = a n * b n)
    (hb : ∀ n, 0 ≤ b n ∧ b n ≤ q)
    (hz : ∀ n, ‖z n‖ ≤ M) :
    Tendsto (fun n => a n • z n) atTop (𝓝 0) := by
  have hbound := scale_le_geometric a b q ha hq₀ hrec hb
  have hp : Tendsto (fun n : ℕ => q ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq₀ hq₁
  refine squeeze_zero_norm (a := fun n => (a 0 * q ^ n) * M) (fun n => ?_) ?_
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hbound n).1]
    exact mul_le_mul (hbound n).2 (hz n) (norm_nonneg _)
      (mul_nonneg ha (pow_nonneg hq₀ n))
  · simpa using (tendsto_const_nhds.mul hp).mul_const M

omit [NormedSpace ℝ E] in
/-- A bound that decreases once per block controls the entire sequence,
including all intermediate phases. -/
theorem geometric_block_bound_tendsto_zero
    (x : ℕ → E) (q M : ℝ) (m : ℕ)
    (hq₀ : 0 ≤ q) (hq₁ : q < 1) (hm : 0 < m)
    (hbound : ∀ n, ‖x n‖ ≤ M * q ^ (n / m)) :
    Tendsto x atTop (𝓝 0) := by
  have hdiv : Tendsto (fun n : ℕ => n / m) atTop atTop := by
    apply Filter.tendsto_atTop.2
    intro N
    exact Filter.eventually_atTop.2
      ⟨N * m, fun n hn => (Nat.le_div_iff_mul_le hm).2 hn⟩
  have hp : Tendsto (fun n : ℕ => q ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq₀ hq₁
  refine squeeze_zero_norm hbound ?_
  simpa using (hp.comp hdiv).const_mul M

omit [NormedSpace ℝ E] in
/-- A local radial contraction leaves its ball invariant.  Applying this
with the norm induced by the certified positive-definite Lyapunov form
gives the normalized invariant neighborhood. -/
theorem mapsTo_ball_of_radial_contraction
    (G : E → E) (c : E) (r L : ℝ) (hL : L ≤ 1)
    (hcontract : ∀ z ∈ Metric.ball c r, dist (G z) c ≤ L * dist z c) :
    Set.MapsTo G (Metric.ball c r) (Metric.ball c r) := by
  intro z hz
  apply lt_of_le_of_lt (hcontract z hz)
  exact lt_of_le_of_lt (mul_le_of_le_one_left dist_nonneg hL) hz

omit [NormedSpace ℝ E] in
/-- An invariant ball supplies a uniform bound for the normalized orbit. -/
theorem norm_le_of_mem_ball (z c : E) (r : ℝ)
    (hz : z ∈ Metric.ball c r) : ‖z‖ ≤ ‖c‖ + r := by
  have hdist : ‖z - c‖ < r := by simpa only [Metric.mem_ball, dist_eq_norm] using hz
  calc
    ‖z‖ = ‖(z - c) + c‖ := by rw [sub_add_cancel]
    _ ≤ ‖z - c‖ + ‖c‖ := norm_add_le _ _
    _ ≤ ‖c‖ + r := by linarith

/-- Pointwise Fréchet differentiability at a fixed point is enough for a
local radial contraction when the derivative has operator norm below one.
No continuity of the derivative or pairwise Lipschitz estimate is assumed. -/
theorem radial_contraction_of_derivative
    (G : E → E) (A : E →L[ℝ] E) (c : E)
    (hderiv : HasFDerivAt G A c) (hfixed : G c = c) (hA : ‖A‖ < 1) :
    ∃ r > 0, ∃ L : ℝ, 0 ≤ L ∧ L < 1 ∧
      ∀ z ∈ Metric.ball c r, dist (G z) c ≤ L * dist z c := by
  obtain ⟨L, hAL, hL⟩ := exists_between hA
  have hε : 0 < L - ‖A‖ := sub_pos.mpr hAL
  obtain ⟨r, hr, hrem⟩ := Metric.eventually_nhds_iff.mp (hderiv.isLittleO.bound hε)
  refine ⟨r, hr, L, le_trans (norm_nonneg _) hAL.le, hL, ?_⟩
  intro z hz
  rw [dist_eq_norm, dist_eq_norm]
  calc
    ‖G z - c‖ = ‖(G z - G c - A (z - c)) + A (z - c)‖ := by
      rw [sub_add_cancel, hfixed]
    _ ≤ ‖G z - G c - A (z - c)‖ + ‖A (z - c)‖ := norm_add_le _ _
    _ ≤ (L - ‖A‖) * ‖z - c‖ + ‖A‖ * ‖z - c‖ :=
      add_le_add (hrem hz) (A.le_opNorm _)
    _ = L * ‖z - c‖ := by ring

end Normed

section Homogeneous

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Realization of normalized coordinates by a positively homogeneous map.
The theorem makes the scale factorization and the chart recurrence explicit. -/
theorem homogeneous_orbit_identity
    (T : E → E) (a : ℕ → ℝ) (z : ℕ → E) (μ : E → ℝ)
    (ha : ∀ n, 0 ≤ a n)
    (hhom : ∀ (t : ℝ), 0 ≤ t → ∀ x, T (t • x) = t • T x)
    (hfactor : ∀ n, T (z n) = μ (z n) • z (n + 1))
    (hscale : ∀ n, a (n + 1) = a n * μ (z n)) :
    ∀ n, T^[n] (a 0 • z 0) = a n • z n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, hhom _ (ha n), hfactor, ← mul_smul,
      ← hscale]

/-- The actual block iterates converge when their normalized representatives
are bounded and the scale factors are uniformly smaller than one. -/
theorem homogeneous_blocks_tendsto_zero
    (T : E → E) (a : ℕ → ℝ) (z : ℕ → E) (μ : E → ℝ)
    (q M : ℝ) (ha : 0 ≤ a 0) (hq₀ : 0 ≤ q) (hq₁ : q < 1)
    (hM : 0 ≤ M)
    (hhom : ∀ (t : ℝ), 0 ≤ t → ∀ x, T (t • x) = t • T x)
    (hfactor : ∀ n, T (z n) = μ (z n) • z (n + 1))
    (hscale : ∀ n, a (n + 1) = a n * μ (z n))
    (hμ : ∀ n, 0 ≤ μ (z n) ∧ μ (z n) ≤ q)
    (hz : ∀ n, ‖z n‖ ≤ M) :
    Tendsto (fun n => T^[n] (a 0 • z 0)) atTop (𝓝 0) := by
  have hbound := scale_le_geometric a (fun n => μ (z n)) q ha hq₀ hscale hμ
  have hid := homogeneous_orbit_identity T a z μ (fun n => (hbound n).1)
    hhom hfactor hscale
  simp_rw [hid]
  exact scaled_phases_tendsto_zero a (fun n => μ (z n)) z q M ha hq₀ hq₁ hM
    hscale hμ hz

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- An invariant normalized neighborhood contains its entire normalized orbit.
Openness and contraction are deliberately not hidden in this elementary lemma. -/
theorem normalized_orbit_mem (G : E → E) (U : Set E) (z : E)
    (hz : z ∈ U) (hU : Set.MapsTo G U U) :
    ∀ n, G^[n] z ∈ U := by
  intro n
  induction n with
  | zero => exact hz
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact hU ih

/-- The accumulated scale along a normalized orbit. -/
def orbitScale (G : E → E) (μ : E → ℝ) (τ : ℝ) (z : E) : ℕ → ℝ
  | 0 => τ
  | n + 1 => orbitScale G μ τ z n * μ (G^[n] z)

/-- Every iterate of a positively homogeneous map is positively homogeneous. -/
theorem iterate_posHomogeneous (T : E → E)
    (hhom : ∀ (t : ℝ), 0 ≤ t → ∀ x, T (t • x) = t • T x) (n : ℕ) :
    ∀ (t : ℝ), 0 ≤ t → ∀ x, T^[n] (t • x) = t • T^[n] x := by
  intro t ht x
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, hhom t ht, Function.iterate_succ_apply']

/-- An invariant normalized block map with uniformly bounded intermediate
phases yields convergence of every one-step iterate, not just the block
subsequence.  In the counterexample the block length is four. -/
theorem homogeneous_block_basin_converges
    (T G : E → E) (μ : E → ℝ) (U : Set E) (q M : ℝ) (m : ℕ)
    (hm : 0 < m) (hq₀ : 0 ≤ q) (hq₁ : q < 1)
    (hhom : ∀ (t : ℝ), 0 ≤ t → ∀ x, T (t • x) = t • T x)
    (hU : Set.MapsTo G U U)
    (hfactor : ∀ z ∈ U, T^[m] z = μ z • G z)
    (hμ : ∀ z ∈ U, 0 ≤ μ z ∧ μ z ≤ q)
    (hphase : ∀ i < m, ∀ z ∈ U, ‖T^[i] z‖ ≤ M)
    (τ : ℝ) (hτ : 0 ≤ τ) (z : E) (hz : z ∈ U) :
    Tendsto (fun n => T^[n] (τ • z)) atTop (𝓝 0) := by
  let a := orbitScale G μ τ z
  have hmem := normalized_orbit_mem G U z hz hU
  have hμseq : ∀ n, 0 ≤ μ (G^[n] z) ∧ μ (G^[n] z) ≤ q :=
    fun n => hμ _ (hmem n)
  have hscale : ∀ n, a (n + 1) = a n * μ (G^[n] z) := fun _ => rfl
  have habound := scale_le_geometric a (fun n => μ (G^[n] z)) q hτ hq₀
    hscale hμseq
  have hfactorseq : ∀ n, T^[m] (G^[n] z) = μ (G^[n] z) • G^[n + 1] z := by
    intro n
    simpa only [Function.iterate_succ_apply'] using hfactor _ (hmem n)
  have hid : ∀ n, (T^[m])^[n] (τ • z) = a n • G^[n] z :=
    homogeneous_orbit_identity (T^[m]) a (fun n => G^[n] z) μ
      (fun n => (habound n).1) (iterate_posHomogeneous T hhom m) hfactorseq hscale
  apply geometric_block_bound_tendsto_zero _ q (τ * M) m hq₀ hq₁ hm
  intro n
  have hfull : T^[n] (τ • z) = a (n / m) • T^[n % m] (G^[n / m] z) := by
    calc
      T^[n] (τ • z) = T^[n % m + m * (n / m)] (τ • z) := by
        rw [Nat.mod_add_div]
      _ = T^[n % m] ((T^[m])^[n / m] (τ • z)) := by
        rw [Function.iterate_add_apply, Function.iterate_mul]
      _ = a (n / m) • T^[n % m] (G^[n / m] z) := by
        rw [hid, iterate_posHomogeneous T hhom _ _ (habound _).1]
  rw [hfull, norm_smul, Real.norm_eq_abs, abs_of_nonneg (habound _).1]
  calc
    a (n / m) * ‖T^[n % m] (G^[n / m] z)‖ ≤ (τ * q ^ (n / m)) * M :=
      mul_le_mul (habound _).2
        (hphase _ (Nat.mod_lt n hm) _ (hmem _)) (norm_nonneg _)
        (mul_nonneg hτ (pow_nonneg hq₀ _))
    _ = (τ * M) * q ^ (n / m) := by ring

/-- Convergence from every scaled point in an invariant normalized set.
The scalar and normalized recurrences are constructed here, rather than
assumed as an additional orbit decomposition. -/
theorem homogeneous_invariant_basin_converges
    (T G : E → E) (μ : E → ℝ) (U : Set E) (q M : ℝ)
    (hq₀ : 0 ≤ q) (hq₁ : q < 1) (hM : 0 ≤ M)
    (hhom : ∀ (t : ℝ), 0 ≤ t → ∀ x, T (t • x) = t • T x)
    (hU : Set.MapsTo G U U)
    (hfactor : ∀ z ∈ U, T z = μ z • G z)
    (hμ : ∀ z ∈ U, 0 ≤ μ z ∧ μ z ≤ q)
    (hbound : ∀ z ∈ U, ‖z‖ ≤ M)
    (τ : ℝ) (hτ : 0 ≤ τ) (z : E) (hz : z ∈ U) :
    Tendsto (fun n => T^[n] (τ • z)) atTop (𝓝 0) := by
  have hmem := normalized_orbit_mem G U z hz hU
  apply homogeneous_blocks_tendsto_zero T (orbitScale G μ τ z)
    (fun n => G^[n] z) μ q M hτ hq₀ hq₁ hM hhom
  · intro n
    simpa only [Function.iterate_succ_apply'] using hfactor _ (hmem n)
  · intro n
    rfl
  · intro n
    exact hμ _ (hmem n)
  · intro n
    exact hbound _ (hmem n)

/-- The local normalized contraction version of the scale-decay theorem.
The hypotheses are the analytic outputs that a certified return-map
derivative must establish for the particular BFGS construction. -/
theorem homogeneous_contraction_ball_converges
    (T G : E → E) (μ : E → ℝ) (c : E) (r L q : ℝ)
    (hr : 0 < r) (hL : L < 1) (hq₀ : 0 ≤ q) (hq₁ : q < 1)
    (hhom : ∀ (t : ℝ), 0 ≤ t → ∀ x, T (t • x) = t • T x)
    (hcontract : ∀ z ∈ Metric.ball c r, dist (G z) c ≤ L * dist z c)
    (hfactor : ∀ z ∈ Metric.ball c r, T z = μ z • G z)
    (hμ : ∀ z ∈ Metric.ball c r, 0 ≤ μ z ∧ μ z ≤ q)
    (τ : ℝ) (hτ : 0 ≤ τ) (z : E) (hz : z ∈ Metric.ball c r) :
    Tendsto (fun n => T^[n] (τ • z)) atTop (𝓝 0) := by
  exact homogeneous_invariant_basin_converges T G μ (Metric.ball c r)
    q (‖c‖ + r) hq₀ hq₁ (add_nonneg (norm_nonneg _) hr.le) hhom
    (mapsTo_ball_of_radial_contraction G c r L hL.le hcontract) hfactor hμ
    (fun w hw => norm_le_of_mem_ball w c r hw) τ hτ z hz

end Homogeneous

end BFGS
