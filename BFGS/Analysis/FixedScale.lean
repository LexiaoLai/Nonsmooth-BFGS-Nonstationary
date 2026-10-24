import BFGS.Analysis.Dynamics

/-!
# Normalization by the exact cycle contraction

The normalized map is `r⁻¹ • T^[m]` on the full state space. Its iterates
are exactly the original block iterates divided by `r^j`. No state coordinate
is used as a divisor. These identities transfer phase safety and convergence
from an invariant neighborhood of the normalized map to the original orbit.
-/

namespace BFGS.FixedScale
noncomputable section
open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- One full block, normalized by the fixed exact contraction factor. -/
def returnMap (T : E → E) (m : ℕ) (r : ℝ) (z : E) : E :=
  r⁻¹ • T^[m] z

theorem block_factor (T : E → E) (m : ℕ) (r : ℝ) (hr : r ≠ 0) (z : E) :
    T^[m] z = r • returnMap T m r z := by
  simp [returnMap, smul_smul, hr]

/-- Positive homogeneity is preserved by the fixed normalization. -/
theorem returnMap_posHomogeneous (T : E → E) (m : ℕ) (r : ℝ)
    (hhom : ∀ t : ℝ, 0 ≤ t → ∀ z, T (t • z) = t • T z) :
    ∀ t : ℝ, 0 ≤ t → ∀ z,
      returnMap T m r (t • z) = t • returnMap T m r z := by
  intro t ht z
  rw [returnMap, iterate_posHomogeneous T hhom m t ht, returnMap, smul_smul,
    smul_smul, mul_comm]

/-- An exact shrinking cycle becomes a fixed point of the normalized map. -/
theorem returnMap_fixed (T : E → E) (m : ℕ) (r : ℝ) (hr : r ≠ 0)
    (z : E) (hcycle : T^[m] z = r • z) : returnMap T m r z = z := by
  simp [returnMap, hcycle, smul_smul, hr]

/-- The original block states are `r^j` times the normalized states. -/
theorem iterate_blocks (T : E → E) (m : ℕ) (r : ℝ) (hr : 0 < r)
    (hhom : ∀ t : ℝ, 0 ≤ t → ∀ z, T (t • z) = t • T z)
    (z : E) (j : ℕ) :
    T^[m * j] z = r^j • (returnMap T m r)^[j] z := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Nat.mul_succ, Nat.add_comm, Function.iterate_add_apply, ih,
      iterate_posHomogeneous T hhom m (r^j) (pow_nonneg hr.le j),
      block_factor T m r hr.ne', smul_smul, pow_succ,
      Function.iterate_succ_apply']

/-- The manuscript's normalized states: `ξ^j = (r^j)⁻¹ • ω^{mj}`. -/
theorem normalized_iterate (T : E → E) (m : ℕ) (r : ℝ) (hr : 0 < r)
    (hhom : ∀ t : ℝ, 0 ≤ t → ∀ z, T (t • z) = t • T z)
    (z : E) (j : ℕ) :
    (returnMap T m r)^[j] z = (r^j)⁻¹ • T^[m * j] z := by
  rw [iterate_blocks T m r hr hhom]
  simp [smul_smul, pow_ne_zero j hr.ne']

/-- Block decomposition including the intermediate phases. -/
theorem iterate_phases (T : E → E) (m : ℕ) (r : ℝ) (hr : 0 < r)
    (hhom : ∀ t : ℝ, 0 ≤ t → ∀ z, T (t • z) = t • T z)
    (z : E) (n : ℕ) :
    T^[n] z = r^(n/m) • T^[n%m] ((returnMap T m r)^[n/m] z) := by
  calc
    T^[n] z = T^[n%m + m*(n/m)] z := by rw [Nat.mod_add_div]
    _ = T^[n%m] (T^[m*(n/m)] z) := Function.iterate_add_apply _ _ _ _
    _ = r^(n/m) • T^[n%m] ((returnMap T m r)^[n/m] z) := by
      rw [iterate_blocks T m r hr hhom,
        iterate_posHomogeneous T hhom (n%m) (r^(n/m)) (pow_nonneg hr.le _)]

theorem iterate_scaled_phases (T : E → E) (m : ℕ) (r : ℝ) (hr : 0 < r)
    (hhom : ∀ t : ℝ, 0 ≤ t → ∀ z, T (t • z) = t • T z)
    (τ : ℝ) (hτ : 0 ≤ τ) (z : E) (n : ℕ) :
    T^[n] (τ • z) = (τ*r^(n/m)) • T^[n%m] ((returnMap T m r)^[n/m] z) := by
  rw [iterate_posHomogeneous T hhom n τ hτ, iterate_phases T m r hr hhom,
    smul_smul]

/-- An invariant neighborhood with bounded intermediate phases yields
convergence of the entire original sequence, not only the block subsequence. -/
theorem basin_converges (T : E → E) (m : ℕ) (r M : ℝ) (U : Set E)
    (hm : 0 < m) (hr : 0 < r) (hr1 : r < 1)
    (hhom : ∀ t : ℝ, 0 ≤ t → ∀ z, T (t • z) = t • T z)
    (hU : Set.MapsTo (returnMap T m r) U U)
    (hphase : ∀ i < m, ∀ w ∈ U, ‖T^[i] w‖ ≤ M)
    (τ : ℝ) (hτ : 0 ≤ τ) (z : E) (hz : z ∈ U) :
    Tendsto (fun n => T^[n] (τ • z)) atTop (𝓝 0) := by
  apply geometric_block_bound_tendsto_zero _ r (τ*M) m hr.le hr1 hm
  intro n
  rw [iterate_scaled_phases T m r hr hhom τ hτ, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hτ (pow_nonneg hr.le _))]
  calc
    (τ*r^(n/m))*‖T^[n%m] ((returnMap T m r)^[n/m] z)‖ ≤
        (τ*r^(n/m))*M := by
      apply mul_le_mul_of_nonneg_left
      · exact hphase _ (Nat.mod_lt n hm) _
          (normalized_orbit_mem _ U z hz hU (n/m))
      · positivity
    _ = (τ*M)*r^(n/m) := by ring

/-- Any phase property stable under the permitted scales holds at every
original iterate. This is used for the line-search and smoothness conditions. -/
theorem basin_all_iterates (T : E → E) (m : ℕ) (r b τ : ℝ)
    (U : Set E) (P : E → Prop) (hm : 0 < m) (hr : 0 < r) (hr1 : r ≤ 1)
    (hτ : 0 < τ) (hτb : τ < b)
    (hhom : ∀ t : ℝ, 0 ≤ t → ∀ z, T (t • z) = t • T z)
    (hU : Set.MapsTo (returnMap T m r) U U)
    (hphase : ∀ σ, 0 < σ → σ < b → ∀ i < m, ∀ w ∈ U, P (σ • T^[i] w))
    (z : E) (hz : z ∈ U) : ∀ n, P (T^[n] (τ • z)) := by
  intro n
  rw [iterate_scaled_phases T m r hr hhom τ hτ.le]
  apply hphase (τ*r^(n/m)) (mul_pos hτ (pow_pos hr _)) _
    (n%m) (Nat.mod_lt n hm) _ (normalized_orbit_mem _ U z hz hU (n/m))
  exact (mul_le_of_le_one_right hτ.le (pow_le_one₀ hr.le hr1)).trans_lt hτb

/-- The direct initial-state version, for phase properties preserved by
every positive scale at most one. -/
theorem basin_all_iterates_le_one (T : E → E) (m : ℕ) (r : ℝ)
    (U : Set E) (P : E → Prop) (hm : 0 < m) (hr : 0 < r) (hr1 : r ≤ 1)
    (hhom : ∀ t : ℝ, 0 ≤ t → ∀ z, T (t • z) = t • T z)
    (hU : Set.MapsTo (returnMap T m r) U U)
    (hphase : ∀ σ : ℝ, 0 < σ → σ ≤ 1 → ∀ i < m, ∀ w ∈ U, P (σ • T^[i] w))
    (z : E) (hz : z ∈ U) : ∀ n, P (T^[n] z) := by
  intro n
  rw [iterate_phases T m r hr hhom]
  exact hphase (r^(n/m)) (pow_pos hr _) (pow_le_one₀ hr.le hr1)
    (n%m) (Nat.mod_lt n hm) _ (normalized_orbit_mem _ U z hz hU (n/m))

/-- Bounded normalized phases suffice with the unscaled initial state. -/
theorem basin_converges_from_initial_state (T : E → E) (m : ℕ) (r M : ℝ) (U : Set E)
    (hm : 0 < m) (hr : 0 < r) (hr1 : r < 1)
    (hhom : ∀ t : ℝ, 0 ≤ t → ∀ z, T (t • z) = t • T z)
    (hU : Set.MapsTo (returnMap T m r) U U)
    (hphase : ∀ i < m, ∀ w ∈ U, ‖T^[i] w‖ ≤ M)
    (z : E) (hz : z ∈ U) :
    Tendsto (fun n => T^[n] z) atTop (𝓝 0) := by
  simpa only [one_smul] using
    basin_converges T m r M U hm hr hr1 hhom hU hphase 1 (by norm_num) z hz

end
end BFGS.FixedScale
