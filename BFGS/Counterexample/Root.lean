import Mathlib

/-!
# Lemma 2.3: the admissible scalar root

The quartic and both rational intervals are those in
the accompanying manuscript and its certificate appendix.
All endpoint values and bounds below are proved by exact arithmetic in Lean.
-/
namespace BFGS.Counterexample
noncomputable section

/-- The scalar closure polynomial of the four-step construction. -/
def quartic (b : ℝ) : ℝ :=
  777924 * b ^ 4 - 576632 * b ^ 3 - 587665 * b ^ 2 + 352256 * b + 65536

/-- The derivative, kept explicit to expose the monotonicity certificate. -/
def quarticDeriv (b : ℝ) : ℝ :=
  3111696 * b ^ 3 - 1729896 * b ^ 2 - 1175330 * b + 352256

theorem quartic_hasDerivAt (b : ℝ) : HasDerivAt quartic (quarticDeriv b) b := by
  have h := ((((((hasDerivAt_id b).pow 4).const_mul (777924 : ℝ)).sub
    (((hasDerivAt_id b).pow 3).const_mul (576632 : ℝ))).sub
    (((hasDerivAt_id b).pow 2).const_mul (587665 : ℝ))).add
    ((hasDerivAt_id b).const_mul (352256 : ℝ))).add_const (65536 : ℝ)
  convert h using 1 <;>
    first | rfl | (norm_num [quartic, quarticDeriv, id_eq]; ring)

theorem quartic_continuous : Continuous quartic := by
  unfold quartic
  fun_prop

theorem quartic_broad_lower_value :
    quartic (9178 / 10000) = -360567061886079 / 156250000000000 := by
  norm_num [quartic]

theorem quartic_broad_upper_value :
    quartic (9179 / 10000) = 49786738620570561 / 2500000000000000 := by
  norm_num [quartic]

theorem quartic_broad_lower_neg : quartic (9178 / 10000) < -2 := by
  rw [quartic_broad_lower_value]
  norm_num

theorem quartic_broad_upper_pos : 19 < quartic (9179 / 10000) := by
  rw [quartic_broad_upper_value]
  norm_num

theorem quartic_narrow_lower_value :
    quartic (91781039164 / 10 ^ 11) =
      -92800728762779521514562900663010959 /
        97656250000000000000000000000000000000000 := by
  norm_num [quartic]

theorem quartic_narrow_upper_value :
    quartic (91781039165 / 10 ^ 11) =
      50822457583876920300538092853408401 /
        40000000000000000000000000000000000000000 := by
  norm_num [quartic]

theorem quartic_narrow_lower_neg : quartic (91781039164 / 10 ^ 11) < 0 := by
  rw [quartic_narrow_lower_value]
  norm_num

theorem quartic_narrow_upper_pos : 0 < quartic (91781039165 / 10 ^ 11) := by
  rw [quartic_narrow_upper_value]
  norm_num

/-- The manuscript's exact lower bound for the derivative throughout the broad box. -/
theorem quarticDeriv_broad_lower (b : ℝ)
    (hb : b ∈ Set.Icc (9178 / 10000 : ℝ) (9179 / 10000)) :
    200000 < quarticDeriv b := by
  have hb0 : 0 ≤ b := by linarith [hb.1]
  have hcub := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 9178 / 10000) hb.1 3
  have hsq := pow_le_pow_left₀ hb0 hb.2 2
  have hbound : (200000 : ℝ) <
      3111696 * (9178 / 10000 : ℝ) ^ 3 -
        1729896 * (9179 / 10000 : ℝ) ^ 2 -
          1175330 * (9179 / 10000 : ℝ) + 352256 := by norm_num
  dsimp [quarticDeriv]
  nlinarith [hb.2]

theorem quartic_strictMonoOn :
    StrictMonoOn quartic (Set.Icc (9178 / 10000 : ℝ) (9179 / 10000)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) quartic_continuous.continuousOn
  intro b hb
  rw [(quartic_hasDerivAt b).deriv]
  have h := quarticDeriv_broad_lower b (interior_subset hb)
  linarith

/-- The refined interval contains an actual real zero, strictly inside its endpoints. -/
theorem exists_root_narrow :
    ∃ b : ℝ, b ∈ Set.Ioo (91781039164 / 10 ^ 11 : ℝ)
      (91781039165 / 10 ^ 11) ∧ quartic b = 0 := by
  exact intermediate_value_Ioo (by norm_num) quartic_continuous.continuousOn
    ⟨quartic_narrow_lower_neg, quartic_narrow_upper_pos⟩

/-- The construction's real parameter, chosen from the proved root existence. -/
def root : ℝ := Classical.choose exists_root_narrow

theorem root_mem_narrow_open :
    root ∈ Set.Ioo (91781039164 / 10 ^ 11 : ℝ) (91781039165 / 10 ^ 11) :=
  (Classical.choose_spec exists_root_narrow).1

theorem root_mem_narrow :
    root ∈ Set.Icc (91781039164 / 10 ^ 11 : ℝ) (91781039165 / 10 ^ 11) :=
  Set.Ioo_subset_Icc_self root_mem_narrow_open

theorem root_quartic : quartic root = 0 :=
  (Classical.choose_spec exists_root_narrow).2

theorem root_mem_broad :
    root ∈ Set.Ioo (9178 / 10000 : ℝ) (9179 / 10000) := by
  have h := root_mem_narrow
  constructor <;> linarith [h.1, h.2]

theorem root_half_lt : (1 / 2 : ℝ) < root := by linarith [root_mem_broad.1]

theorem root_pos : 0 < root := by linarith [root_half_lt]

theorem root_ne_zero : root ≠ 0 := ne_of_gt root_pos

theorem root_unique (b : ℝ)
    (hb : b ∈ Set.Icc (9178 / 10000 : ℝ) (9179 / 10000))
    (hz : quartic b = 0) : b = root :=
  quartic_strictMonoOn.injOn hb (Set.Ioo_subset_Icc_self root_mem_broad)
    (hz.trans root_quartic.symm)

/-- The existence and uniqueness statement appearing in the manuscript. -/
theorem existsUnique_root_broad :
    ∃! b : ℝ, b ∈ Set.Ioo (9178 / 10000 : ℝ) (9179 / 10000) ∧ quartic b = 0 :=
  ⟨root, ⟨root_mem_broad, root_quartic⟩,
    fun b hb => root_unique b (Set.Ioo_subset_Icc_self hb.1) hb.2⟩

end
end BFGS.Counterexample
