import Mathlib

/-!
# A neighborhood attracted to a positive fixed ray

This is the invariant-neighborhood and convergence argument in Step 3 of
Lemma 2.12 of the manuscript. The hypotheses are the
one-step bounds (2.31). No differentiability is needed
here: the derivative argument supplies these bounds separately.

The first coordinate records position along the fixed ray; the second
coordinate is transverse to it. A weighted diamond controls both the total
drift of the first coordinate and the geometric decay of the second.
-/

namespace BFGS.Analysis

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E]

/-- The neighborhood used in the proof of Lemma 2.12. -/
def rayNeighborhood (ε M : ℝ) : Set (ℝ × E) :=
  {z | |z.1 - 1| + M * ‖z.2‖ < ε}

theorem rayNeighborhood_isOpen (ε M : ℝ) :
    IsOpen (rayNeighborhood (E := E) ε M) := by
  exact isOpen_lt
    ((continuous_fst.sub continuous_const).abs.add
      (continuous_const.mul continuous_snd.norm)) continuous_const

theorem rayNeighborhood_center (ε M : ℝ) (hε : 0 < ε) :
    (1, (0 : E)) ∈ rayNeighborhood ε M := by
  simpa [rayNeighborhood] using hε

/-- The weighted diamond lies inside the cylinder where the step bounds hold. -/
theorem rayNeighborhood_subset_cylinder (ε δ M : ℝ)
    (hM : 0 < M) (hwidth : ε ≤ M * δ) :
    rayNeighborhood (E := E) ε M ⊆
      {z | |z.1 - 1| ≤ ε ∧ ‖z.2‖ ≤ δ} := by
  intro z hz
  change |z.1 - 1| + M * ‖z.2‖ < ε at hz
  have hnorm : 0 ≤ M * ‖z.2‖ := mul_nonneg hM.le (norm_nonneg _)
  have hsecond : M * ‖z.2‖ < M * δ := by
    have := abs_nonneg (z.1 - 1)
    linarith
  exact ⟨by linarith, ((mul_lt_mul_iff_right₀ hM).mp hsecond).le⟩

/-- The weighted-diamond argument of Lemma 2.12, including convergence to a
point on the positive ray. The lower bound on the limit is retained explicitly. -/
theorem rayNeighborhood_attraction
    (F : ℝ × E → ℝ × E) (ε δ γ C M : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1)
    (hγ : 0 ≤ γ) (hγ1 : γ < 1) (hC : 0 ≤ C) (hM : 0 < M)
    (hweight : C + M * γ ≤ M) (hwidth : ε ≤ M * δ)
    (hstep : ∀ z : ℝ × E, |z.1 - 1| ≤ ε → ‖z.2‖ ≤ δ →
      ‖(F z).2‖ ≤ γ * ‖z.2‖ ∧ |(F z).1 - z.1| ≤ C * ‖z.2‖) :
    IsOpen (rayNeighborhood (E := E) ε M) ∧
    (1, (0 : E)) ∈ rayNeighborhood ε M ∧
    rayNeighborhood (E := E) ε M ⊆ {z | |z.1 - 1| ≤ ε ∧ ‖z.2‖ ≤ δ} ∧
    Set.MapsTo F (rayNeighborhood ε M) (rayNeighborhood ε M) ∧
    ∀ z ∈ rayNeighborhood (E := E) ε M,
      ∃ a : ℝ, 1 - ε ≤ a ∧ 0 < a ∧
        Tendsto (fun n : ℕ => F^[n] z) atTop (𝓝 (a, (0 : E))) := by
  have hcyl := rayNeighborhood_subset_cylinder (E := E) ε δ M hM hwidth
  have hinv : Set.MapsTo F (rayNeighborhood ε M) (rayNeighborhood ε M) := by
    intro z hz
    obtain ⟨ha, hu⟩ := hcyl hz
    obtain ⟨hu', ha'⟩ := hstep z ha hu
    have habs : |(F z).1 - 1| ≤ |(F z).1 - z.1| + |z.1 - 1| := by
      calc
        |(F z).1 - 1| = |((F z).1 - z.1) + (z.1 - 1)| := by congr 1; ring
        _ ≤ |(F z).1 - z.1| + |z.1 - 1| := abs_add_le _ _
    change |(F z).1 - 1| + M * ‖(F z).2‖ < ε
    change |z.1 - 1| + M * ‖z.2‖ < ε at hz
    calc
      |(F z).1 - 1| + M * ‖(F z).2‖
          ≤ |z.1 - 1| + (C + M * γ) * ‖z.2‖ := by
            nlinarith [mul_le_mul_of_nonneg_left hu' hM.le]
      _ ≤ |z.1 - 1| + M * ‖z.2‖ := by
        gcongr
      _ < ε := hz
  refine ⟨rayNeighborhood_isOpen ε M, rayNeighborhood_center ε M hε,
    hcyl, hinv, ?_⟩
  intro z hz
  have hmem : ∀ n : ℕ, F^[n] z ∈ rayNeighborhood ε M := by
    intro n
    induction n with
    | zero => simpa using hz
    | succ n ih => simpa only [Function.iterate_succ_apply'] using hinv ih
  have hbounds (n : ℕ) := hstep (F^[n] z) (hcyl (hmem n)).1 (hcyl (hmem n)).2
  have hgeom : ∀ n : ℕ, ‖(F^[n] z).2‖ ≤ γ ^ n * ‖z.2‖ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      calc
        ‖(F (F^[n] z)).2‖ ≤ γ * ‖(F^[n] z).2‖ := (hbounds n).1
        _ ≤ γ * (γ ^ n * ‖z.2‖) := mul_le_mul_of_nonneg_left ih hγ
        _ = γ ^ (n + 1) * ‖z.2‖ := by rw [pow_succ]; ring
  have hscalar : CauchySeq (fun n : ℕ => (F^[n] z).1) := by
    apply cauchySeq_of_le_geometric γ (C * ‖z.2‖) hγ1
    intro n
    rw [Real.dist_eq, abs_sub_comm, Function.iterate_succ_apply']
    calc
      |(F (F^[n] z)).1 - (F^[n] z).1| ≤ C * ‖(F^[n] z).2‖ := (hbounds n).2
      _ ≤ C * (γ ^ n * ‖z.2‖) := mul_le_mul_of_nonneg_left (hgeom n) hC
      _ = (C * ‖z.2‖) * γ ^ n := by ring
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete hscalar
  have halower : 1 - ε ≤ a := by
    apply ge_of_tendsto' ha
    intro n
    have h := (abs_le.mp (hcyl (hmem n)).1).1
    linarith
  have hzero : Tendsto (fun n : ℕ => (F^[n] z).2) atTop (𝓝 (0 : E)) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hpower := (tendsto_pow_atTop_nhds_zero_of_lt_one hγ hγ1).mul_const ‖z.2‖
    apply squeeze_zero (fun n => norm_nonneg _) hgeom
    simpa using hpower
  refine ⟨a, halower, by linarith, ?_⟩
  simpa using ha.prodMk_nhds hzero

/-- Existence form of Lemma 2.12 from the two one-step estimates. The chosen
neighborhood is a weighted diamond, so no second nested neighborhood is needed. -/
theorem exists_ray_attraction_neighborhood
    (F : ℝ × E → ℝ × E) (ε δ γ C : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ)
    (hγ : 0 ≤ γ) (hγ1 : γ < 1) (hC : 0 ≤ C)
    (hstep : ∀ z : ℝ × E, |z.1 - 1| ≤ ε → ‖z.2‖ ≤ δ →
      ‖(F z).2‖ ≤ γ * ‖z.2‖ ∧ |(F z).1 - z.1| ≤ C * ‖z.2‖) :
    ∃ U : Set (ℝ × E), IsOpen U ∧ (1, (0 : E)) ∈ U ∧
      U ⊆ {z | |z.1 - 1| ≤ ε ∧ ‖z.2‖ ≤ δ} ∧ Set.MapsTo F U U ∧
      ∀ z ∈ U, ∃ a : ℝ, 0 < a ∧
        Tendsto (fun n : ℕ => F^[n] z) atTop (𝓝 (a, (0 : E))) := by
  let M := max 1 (max (C / (1 - γ)) (ε / δ))
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hCM : C / (1 - γ) ≤ M :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hεM : ε / δ ≤ M :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hweight : C + M * γ ≤ M := by
    have := (div_le_iff₀ (sub_pos.mpr hγ1)).mp hCM
    nlinarith
  have hwidth : ε ≤ M * δ := (div_le_iff₀ hδ).mp hεM
  obtain ⟨hopen, hcenter, hsubset, hinv, hconv⟩ :=
    rayNeighborhood_attraction F ε δ γ C M hε hε1 hγ hγ1 hC hM hweight hwidth hstep
  refine ⟨rayNeighborhood ε M, hopen, hcenter, hsubset, hinv, ?_⟩
  intro z hz
  obtain ⟨a, _, ha, hlim⟩ := hconv z hz
  exact ⟨a, ha, hlim⟩

end BFGS.Analysis
