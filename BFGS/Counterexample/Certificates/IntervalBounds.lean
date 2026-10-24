import BFGS.Counterexample.Certificates.IntervalTrace35
import BFGS.Counterexample.Root

/-! Scalar enclosures and the explicit 0.78 row-sum bound. -/
namespace BFGS.Counterexample.Trace
noncomputable section
open BFGS RationalInterval
set_option maxHeartbeats 0
set_option maxRecDepth 100000

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.vecHead Matrix.vecTail
private theorem fin4_succ_two : (Fin.succ (2 : Fin 3) : Fin 4) = 3 := rfl
attribute [local simp] fin4_succ_two

theorem root_mem_interval : rootInterval.Contains root := by
  convert root_mem_narrow using 1; norm_num [rootInterval, RationalInterval.Contains]

private theorem lower_of_contains {I : RationalInterval} {x : ℝ} {a : ℚ}
    (h : I.Contains x) (ha : a < I.lo) : (a : ℝ) < x :=
  lt_of_lt_of_le (by exact_mod_cast ha) h.1

private theorem upper_of_contains {I : RationalInterval} {x : ℝ} {a : ℚ}
    (h : I.Contains x) (ha : I.hi < a) : x < (a : ℝ) :=
  lt_of_le_of_lt h.2 (by exact_mod_cast ha)

private theorem upper_le_of_contains {I : RationalInterval} {x : ℝ} {a : ℚ}
    (h : I.Contains x) (ha : I.hi ≤ a) : x ≤ (a : ℝ) :=
  le_trans h.2 (by exact_mod_cast ha)

private theorem lower_le_of_contains {I : RationalInterval} {x : ℝ} {a : ℚ}
    (h : I.Contains x) (ha : a ≤ I.lo) : (a : ℝ) ≤ x :=
  le_trans (by exact_mod_cast ha) h.1

private theorem absolute_of_contains {I : RationalInterval} {x : ℝ} {a : ℚ}
    (h : I.Contains x) (ha : -a ≤ I.lo ∧ I.hi ≤ a) : |x| ≤ (a : ℝ) := by
  apply abs_le.mpr
  exact ⟨le_trans (by exact_mod_cast ha.1) h.1, le_trans h.2 (by exact_mod_cast ha.2)⟩

theorem norm_positive_0 (b : ℝ) (hb : rootInterval.Contains b) :
    (0 : ℝ) < n178 b := by
  have h := lower_of_contains (a := (0 : ℚ)) (b178 b hb) (by norm_num [i178])
  norm_num at h
  exact h

theorem norm_bound_0 (b : ℝ) (hb : rootInterval.Contains b) :
    n178 b < (8 : ℝ) := by
  have h := upper_of_contains (a := (8 : ℚ)) (b178 b hb) (by norm_num [i178])
  norm_num at h
  exact h

theorem norm_positive_1 (b : ℝ) (hb : rootInterval.Contains b) :
    (0 : ℝ) < n192 b := by
  have h := lower_of_contains (a := (0 : ℚ)) (b192 b hb) (by norm_num [i192])
  norm_num at h
  exact h

theorem norm_bound_1 (b : ℝ) (hb : rootInterval.Contains b) :
    n192 b < (8 : ℝ) := by
  have h := upper_of_contains (a := (8 : ℚ)) (b192 b hb) (by norm_num [i192])
  norm_num at h
  exact h

theorem norm_positive_2 (b : ℝ) (hb : rootInterval.Contains b) :
    (0 : ℝ) < n206 b := by
  have h := lower_of_contains (a := (0 : ℚ)) (b206 b hb) (by norm_num [i206])
  norm_num at h
  exact h

theorem norm_bound_2 (b : ℝ) (hb : rootInterval.Contains b) :
    n206 b < (8 : ℝ) := by
  have h := upper_of_contains (a := (8 : ℚ)) (b206 b hb) (by norm_num [i206])
  norm_num at h
  exact h

theorem norm_positive_3 (b : ℝ) (hb : rootInterval.Contains b) :
    (0 : ℝ) < n220 b := by
  have h := lower_of_contains (a := (0 : ℚ)) (b220 b hb) (by norm_num [i220])
  norm_num at h
  exact h

theorem norm_bound_3 (b : ℝ) (hb : rootInterval.Contains b) :
    n220 b < (8 : ℝ) := by
  have h := upper_of_contains (a := (8 : ℚ)) (b220 b hb) (by norm_num [i220])
  norm_num at h
  exact h

theorem norm_positive_4 (b : ℝ) (hb : rootInterval.Contains b) :
    (0 : ℝ) < n301 b := by
  have h := lower_of_contains (a := (0 : ℚ)) (b301 b hb) (by norm_num [i301])
  norm_num at h
  exact h

theorem norm_bound_4 (b : ℝ) (hb : rootInterval.Contains b) :
    n301 b < (8 : ℝ) := by
  have h := upper_of_contains (a := (8 : ℚ)) (b301 b hb) (by norm_num [i301])
  norm_num at h
  exact h

theorem coordinate_sign_0 (b : ℝ) (hb : rootInterval.Contains b) :
    (0 : ℝ) < n244 b := by
  have h := lower_of_contains (a := (0 : ℚ)) (b244 b hb) (by norm_num [i244])
  norm_num at h
  exact h

theorem slope_lower_0 (b : ℝ) (hb : rootInterval.Contains b) :
    (1 / 50 : ℝ) < n241 b := by
  have h := lower_of_contains (a := (1 / 50 : ℚ)) (b241 b hb) (by norm_num [i241])
  norm_num at h
  exact h

theorem slope_upper_0 (b : ℝ) (hb : rootInterval.Contains b) :
    n241 b ≤ (1 : ℝ) := by
  have h := upper_le_of_contains (a := (1 : ℚ)) (b241 b hb) (by norm_num [i241])
  norm_num at h
  exact h

theorem curvature_positive_0 (b : ℝ) (hb : rootInterval.Contains b) :
    (0 : ℝ) < n64 b := by
  have h := lower_of_contains (a := (0 : ℚ)) (b64 b hb) (by norm_num [i64])
  norm_num at h
  exact h

theorem armijo_positive_0 (b : ℝ) (hb : rootInterval.Contains b) :
    (1 / 50 : ℝ) < n339 b := by
  have h := lower_of_contains (a := (1 / 50 : ℚ)) (b339 b hb) (by norm_num [i339])
  norm_num at h
  exact h

theorem wolfe_positive_0 (b : ℝ) (hb : rootInterval.Contains b) :
    (0 : ℝ) < n359 b := by
  have h := lower_of_contains (a := (0 : ℚ)) (b359 b hb) (by norm_num [i359])
  norm_num at h
  exact h

theorem second_data_bound_0 (b : ℝ) (hb : rootInterval.Contains b) :
    |n254 b| ≤ (5 : ℝ) := by
  have h := absolute_of_contains (a := (5 : ℚ)) (b254 b hb) (by norm_num [i254])
  norm_num at h
  exact h

theorem coordinate_sign_1 (b : ℝ) (hb : rootInterval.Contains b) :
    (0 : ℝ) < n257 b := by
  have h := lower_of_contains (a := (0 : ℚ)) (b257 b hb) (by norm_num [i257])
  norm_num at h
  exact h

theorem slope_lower_1 (b : ℝ) (hb : rootInterval.Contains b) :
    (1 / 50 : ℝ) < n15 b := by
  have h := lower_of_contains (a := (1 / 50 : ℚ)) (b15 b hb) (by norm_num [i15])
  norm_num at h
  exact h

theorem slope_upper_1 (b : ℝ) (hb : rootInterval.Contains b) :
    n15 b ≤ (1 : ℝ) := by
  have h := upper_le_of_contains (a := (1 : ℚ)) (b15 b hb) (by norm_num [i15])
  norm_num at h
  exact h

theorem curvature_positive_1 (b : ℝ) (hb : rootInterval.Contains b) :
    (0 : ℝ) < n323 b := by
  have h := lower_of_contains (a := (0 : ℚ)) (b323 b hb) (by norm_num [i323])
  norm_num at h
  exact h

theorem armijo_positive_1 (b : ℝ) (hb : rootInterval.Contains b) :
    (1 / 50 : ℝ) < n343 b := by
  have h := lower_of_contains (a := (1 / 50 : ℚ)) (b343 b hb) (by norm_num [i343])
  norm_num at h
  exact h

theorem wolfe_positive_1 (b : ℝ) (hb : rootInterval.Contains b) :
    (0 : ℝ) < n364 b := by
  have h := lower_of_contains (a := (0 : ℚ)) (b364 b hb) (by norm_num [i364])
  norm_num at h
  exact h

theorem second_data_bound_1 (b : ℝ) (hb : rootInterval.Contains b) :
    |n266 b| ≤ (5 : ℝ) := by
  have h := absolute_of_contains (a := (5 : ℚ)) (b266 b hb) (by norm_num [i266])
  norm_num at h
  exact h

theorem coordinate_sign_2 (b : ℝ) (hb : rootInterval.Contains b) :
    n269 b < (0 : ℝ) := by
  have h := upper_of_contains (a := (0 : ℚ)) (b269 b hb) (by norm_num [i269])
  norm_num at h
  exact h

theorem slope_lower_2 (b : ℝ) (hb : rootInterval.Contains b) :
    (1 / 50 : ℝ) < n275 b := by
  have h := lower_of_contains (a := (1 / 50 : ℚ)) (b275 b hb) (by norm_num [i275])
  norm_num at h
  exact h

theorem slope_upper_2 (b : ℝ) (hb : rootInterval.Contains b) :
    n275 b ≤ (1 : ℝ) := by
  have h := upper_le_of_contains (a := (1 : ℚ)) (b275 b hb) (by norm_num [i275])
  norm_num at h
  exact h

theorem curvature_positive_2 (b : ℝ) (hb : rootInterval.Contains b) :
    (0 : ℝ) < n329 b := by
  have h := lower_of_contains (a := (0 : ℚ)) (b329 b hb) (by norm_num [i329])
  norm_num at h
  exact h

theorem armijo_positive_2 (b : ℝ) (hb : rootInterval.Contains b) :
    (1 / 50 : ℝ) < n350 b := by
  have h := lower_of_contains (a := (1 / 50 : ℚ)) (b350 b hb) (by norm_num [i350])
  norm_num at h
  exact h

theorem wolfe_positive_2 (b : ℝ) (hb : rootInterval.Contains b) :
    (0 : ℝ) < n373 b := by
  have h := lower_of_contains (a := (0 : ℚ)) (b373 b hb) (by norm_num [i373])
  norm_num at h
  exact h

theorem second_data_bound_2 (b : ℝ) (hb : rootInterval.Contains b) :
    |n282 b| ≤ (5 : ℝ) := by
  have h := absolute_of_contains (a := (5 : ℚ)) (b282 b hb) (by norm_num [i282])
  norm_num at h
  exact h

theorem coordinate_sign_3 (b : ℝ) (hb : rootInterval.Contains b) :
    n285 b < (0 : ℝ) := by
  have h := upper_of_contains (a := (0 : ℚ)) (b285 b hb) (by norm_num [i285])
  norm_num at h
  exact h

theorem slope_lower_3 (b : ℝ) (hb : rootInterval.Contains b) :
    (1 / 50 : ℝ) < n291 b := by
  have h := lower_of_contains (a := (1 / 50 : ℚ)) (b291 b hb) (by norm_num [i291])
  norm_num at h
  exact h

theorem slope_upper_3 (b : ℝ) (hb : rootInterval.Contains b) :
    n291 b ≤ (1 : ℝ) := by
  have h := upper_le_of_contains (a := (1 : ℚ)) (b291 b hb) (by norm_num [i291])
  norm_num at h
  exact h

theorem curvature_positive_3 (b : ℝ) (hb : rootInterval.Contains b) :
    (0 : ℝ) < n335 b := by
  have h := lower_of_contains (a := (0 : ℚ)) (b335 b hb) (by norm_num [i335])
  norm_num at h
  exact h

theorem armijo_positive_3 (b : ℝ) (hb : rootInterval.Contains b) :
    (1 / 50 : ℝ) < n357 b := by
  have h := lower_of_contains (a := (1 / 50 : ℚ)) (b357 b hb) (by norm_num [i357])
  norm_num at h
  exact h

theorem wolfe_positive_3 (b : ℝ) (hb : rootInterval.Contains b) :
    (0 : ℝ) < n381 b := by
  have h := lower_of_contains (a := (0 : ℚ)) (b381 b hb) (by norm_num [i381])
  norm_num at h
  exact h

theorem second_data_bound_3 (b : ℝ) (hb : rootInterval.Contains b) :
    |n298 b| ≤ (5 : ℝ) := by
  have h := absolute_of_contains (a := (5 : ℚ)) (b298 b hb) (by norm_num [i298])
  norm_num at h
  exact h

theorem gap_positive_plus_0 (b : ℝ) (hb : rootInterval.Contains b) :
    (1 : ℝ) < n383 b := by
  have h := lower_of_contains (a := (1 : ℚ)) (b383 b hb) (by norm_num [i383])
  norm_num at h
  exact h

theorem secant_lower_plus_0 (b : ℝ) (hb : rootInterval.Contains b) :
    (1 / 2 : ℝ) < n386 b := by
  have h := lower_of_contains (a := (1 / 2 : ℚ)) (b386 b hb) (by norm_num [i386])
  norm_num at h
  exact h

theorem secant_upper_plus_0 (b : ℝ) (hb : rootInterval.Contains b) :
    n386 b < (2 : ℝ) := by
  have h := upper_of_contains (a := (2 : ℚ)) (b386 b hb) (by norm_num [i386])
  norm_num at h
  exact h

theorem gap_positive_plus_1 (b : ℝ) (hb : rootInterval.Contains b) :
    (1 : ℝ) < n388 b := by
  have h := lower_of_contains (a := (1 : ℚ)) (b388 b hb) (by norm_num [i388])
  norm_num at h
  exact h

theorem secant_lower_plus_1 (b : ℝ) (hb : rootInterval.Contains b) :
    (1 / 2 : ℝ) < n392 b := by
  have h := lower_of_contains (a := (1 / 2 : ℚ)) (b392 b hb) (by norm_num [i392])
  norm_num at h
  exact h

theorem secant_upper_plus_1 (b : ℝ) (hb : rootInterval.Contains b) :
    n392 b < (2 : ℝ) := by
  have h := upper_of_contains (a := (2 : ℚ)) (b392 b hb) (by norm_num [i392])
  norm_num at h
  exact h

theorem gap_positive_plus_2 (b : ℝ) (hb : rootInterval.Contains b) :
    (1 : ℝ) < n394 b := by
  have h := lower_of_contains (a := (1 : ℚ)) (b394 b hb) (by norm_num [i394])
  norm_num at h
  exact h

theorem secant_lower_plus_2 (b : ℝ) (hb : rootInterval.Contains b) :
    (1 / 2 : ℝ) < n396 b := by
  have h := lower_of_contains (a := (1 / 2 : ℚ)) (b396 b hb) (by norm_num [i396])
  norm_num at h
  exact h

theorem secant_upper_plus_2 (b : ℝ) (hb : rootInterval.Contains b) :
    n396 b < (2 : ℝ) := by
  have h := upper_of_contains (a := (2 : ℚ)) (b396 b hb) (by norm_num [i396])
  norm_num at h
  exact h

theorem bridge_plus_0_L (b : ℝ) (hb : rootInterval.Contains b) :
    (0 : ℝ) ≤ n419 b := by
  have h := lower_le_of_contains (a := (0 : ℚ)) (b419 b hb) (by norm_num [i419])
  norm_num at h
  exact h

theorem bridge_plus_0_R (b : ℝ) (hb : rootInterval.Contains b) :
    n420 b ≤ (0 : ℝ) := by
  have h := upper_le_of_contains (a := (0 : ℚ)) (b420 b hb) (by norm_num [i420])
  norm_num at h
  exact h

theorem bridge_plus_0_remaining (b : ℝ) (hb : rootInterval.Contains b) :
    (0 : ℝ) < n429 b := by
  have h := lower_of_contains (a := (0 : ℚ)) (b429 b hb) (by norm_num [i429])
  norm_num at h
  exact h

theorem bridge_plus_1_L (b : ℝ) (hb : rootInterval.Contains b) :
    (0 : ℝ) ≤ n437 b := by
  have h := lower_le_of_contains (a := (0 : ℚ)) (b437 b hb) (by norm_num [i437])
  norm_num at h
  exact h

theorem bridge_plus_1_R (b : ℝ) (hb : rootInterval.Contains b) :
    n441 b ≤ (0 : ℝ) := by
  have h := upper_le_of_contains (a := (0 : ℚ)) (b441 b hb) (by norm_num [i441])
  norm_num at h
  exact h

theorem bridge_plus_1_remaining (b : ℝ) (hb : rootInterval.Contains b) :
    (0 : ℝ) < n457 b := by
  have h := lower_of_contains (a := (0 : ℚ)) (b457 b hb) (by norm_num [i457])
  norm_num at h
  exact h

theorem bridge_plus_2_L (b : ℝ) (hb : rootInterval.Contains b) :
    (0 : ℝ) ≤ n466 b := by
  have h := lower_le_of_contains (a := (0 : ℚ)) (b466 b hb) (by norm_num [i466])
  norm_num at h
  exact h

theorem bridge_plus_2_R (b : ℝ) (hb : rootInterval.Contains b) :
    n470 b ≤ (0 : ℝ) := by
  have h := upper_le_of_contains (a := (0 : ℚ)) (b470 b hb) (by norm_num [i470])
  norm_num at h
  exact h

theorem bridge_plus_2_remaining (b : ℝ) (hb : rootInterval.Contains b) :
    (0 : ℝ) < n480 b := by
  have h := lower_of_contains (a := (0 : ℚ)) (b480 b hb) (by norm_num [i480])
  norm_num at h
  exact h

theorem bridge_plus_3_L (b : ℝ) (hb : rootInterval.Contains b) :
    (0 : ℝ) ≤ n487 b := by
  have h := lower_le_of_contains (a := (0 : ℚ)) (b487 b hb) (by norm_num [i487])
  norm_num at h
  exact h

theorem bridge_plus_3_R (b : ℝ) (hb : rootInterval.Contains b) :
    n488 b ≤ (0 : ℝ) := by
  have h := upper_le_of_contains (a := (0 : ℚ)) (b488 b hb) (by norm_num [i488])
  norm_num at h
  exact h

theorem bridge_plus_3_remaining (b : ℝ) (hb : rootInterval.Contains b) :
    (0 : ℝ) < n499 b := by
  have h := lower_of_contains (a := (0 : ℚ)) (b499 b hb) (by norm_num [i499])
  norm_num at h
  exact h

theorem bridge_plus_4_L (b : ℝ) (hb : rootInterval.Contains b) :
    (0 : ℝ) ≤ n419 b := by
  have h := lower_le_of_contains (a := (0 : ℚ)) (b419 b hb) (by norm_num [i419])
  norm_num at h
  exact h

theorem bridge_plus_4_R (b : ℝ) (hb : rootInterval.Contains b) :
    n420 b ≤ (0 : ℝ) := by
  have h := upper_le_of_contains (a := (0 : ℚ)) (b420 b hb) (by norm_num [i420])
  norm_num at h
  exact h

theorem bridge_plus_4_remaining (b : ℝ) (hb : rootInterval.Contains b) :
    (0 : ℝ) < n429 b := by
  have h := lower_of_contains (a := (0 : ℚ)) (b429 b hb) (by norm_num [i429])
  norm_num at h
  exact h

theorem gap_positive_minus_0 (b : ℝ) (hb : rootInterval.Contains b) :
    (1 : ℝ) < n397 b := by
  have h := lower_of_contains (a := (1 : ℚ)) (b397 b hb) (by norm_num [i397])
  norm_num at h
  exact h

theorem secant_lower_minus_0 (b : ℝ) (hb : rootInterval.Contains b) :
    (1 / 2 : ℝ) < n400 b := by
  have h := lower_of_contains (a := (1 / 2 : ℚ)) (b400 b hb) (by norm_num [i400])
  norm_num at h
  exact h

theorem secant_upper_minus_0 (b : ℝ) (hb : rootInterval.Contains b) :
    n400 b < (2 : ℝ) := by
  have h := upper_of_contains (a := (2 : ℚ)) (b400 b hb) (by norm_num [i400])
  norm_num at h
  exact h

theorem gap_positive_minus_1 (b : ℝ) (hb : rootInterval.Contains b) :
    (1 : ℝ) < n402 b := by
  have h := lower_of_contains (a := (1 : ℚ)) (b402 b hb) (by norm_num [i402])
  norm_num at h
  exact h

theorem secant_lower_minus_1 (b : ℝ) (hb : rootInterval.Contains b) :
    (1 / 2 : ℝ) < n406 b := by
  have h := lower_of_contains (a := (1 / 2 : ℚ)) (b406 b hb) (by norm_num [i406])
  norm_num at h
  exact h

theorem secant_upper_minus_1 (b : ℝ) (hb : rootInterval.Contains b) :
    n406 b < (2 : ℝ) := by
  have h := upper_of_contains (a := (2 : ℚ)) (b406 b hb) (by norm_num [i406])
  norm_num at h
  exact h

theorem gap_positive_minus_2 (b : ℝ) (hb : rootInterval.Contains b) :
    (1 : ℝ) < n408 b := by
  have h := lower_of_contains (a := (1 : ℚ)) (b408 b hb) (by norm_num [i408])
  norm_num at h
  exact h

theorem secant_lower_minus_2 (b : ℝ) (hb : rootInterval.Contains b) :
    (1 / 2 : ℝ) < n412 b := by
  have h := lower_of_contains (a := (1 / 2 : ℚ)) (b412 b hb) (by norm_num [i412])
  norm_num at h
  exact h

theorem secant_upper_minus_2 (b : ℝ) (hb : rootInterval.Contains b) :
    n412 b < (2 : ℝ) := by
  have h := upper_of_contains (a := (2 : ℚ)) (b412 b hb) (by norm_num [i412])
  norm_num at h
  exact h

theorem bridge_minus_0_L (b : ℝ) (hb : rootInterval.Contains b) :
    (0 : ℝ) ≤ n419 b := by
  have h := lower_le_of_contains (a := (0 : ℚ)) (b419 b hb) (by norm_num [i419])
  norm_num at h
  exact h

theorem bridge_minus_0_R (b : ℝ) (hb : rootInterval.Contains b) :
    n420 b ≤ (0 : ℝ) := by
  have h := upper_le_of_contains (a := (0 : ℚ)) (b420 b hb) (by norm_num [i420])
  norm_num at h
  exact h

theorem bridge_minus_0_remaining (b : ℝ) (hb : rootInterval.Contains b) :
    (0 : ℝ) < n429 b := by
  have h := lower_of_contains (a := (0 : ℚ)) (b429 b hb) (by norm_num [i429])
  norm_num at h
  exact h

theorem bridge_minus_1_L (b : ℝ) (hb : rootInterval.Contains b) :
    (0 : ℝ) ≤ n507 b := by
  have h := lower_le_of_contains (a := (0 : ℚ)) (b507 b hb) (by norm_num [i507])
  norm_num at h
  exact h

theorem bridge_minus_1_R (b : ℝ) (hb : rootInterval.Contains b) :
    n511 b ≤ (0 : ℝ) := by
  have h := upper_le_of_contains (a := (0 : ℚ)) (b511 b hb) (by norm_num [i511])
  norm_num at h
  exact h

theorem bridge_minus_1_remaining (b : ℝ) (hb : rootInterval.Contains b) :
    (0 : ℝ) < n518 b := by
  have h := lower_of_contains (a := (0 : ℚ)) (b518 b hb) (by norm_num [i518])
  norm_num at h
  exact h

theorem bridge_minus_2_L (b : ℝ) (hb : rootInterval.Contains b) :
    (0 : ℝ) ≤ n529 b := by
  have h := lower_le_of_contains (a := (0 : ℚ)) (b529 b hb) (by norm_num [i529])
  norm_num at h
  exact h

theorem bridge_minus_2_R (b : ℝ) (hb : rootInterval.Contains b) :
    n533 b ≤ (0 : ℝ) := by
  have h := upper_le_of_contains (a := (0 : ℚ)) (b533 b hb) (by norm_num [i533])
  norm_num at h
  exact h

theorem bridge_minus_2_remaining (b : ℝ) (hb : rootInterval.Contains b) :
    (0 : ℝ) < n550 b := by
  have h := lower_of_contains (a := (0 : ℚ)) (b550 b hb) (by norm_num [i550])
  norm_num at h
  exact h

theorem bridge_minus_3_L (b : ℝ) (hb : rootInterval.Contains b) :
    (0 : ℝ) ≤ n558 b := by
  have h := lower_le_of_contains (a := (0 : ℚ)) (b558 b hb) (by norm_num [i558])
  norm_num at h
  exact h

theorem bridge_minus_3_R (b : ℝ) (hb : rootInterval.Contains b) :
    n561 b ≤ (0 : ℝ) := by
  have h := upper_le_of_contains (a := (0 : ℚ)) (b561 b hb) (by norm_num [i561])
  norm_num at h
  exact h

theorem bridge_minus_3_remaining (b : ℝ) (hb : rootInterval.Contains b) :
    (0 : ℝ) < n575 b := by
  have h := lower_of_contains (a := (0 : ℚ)) (b575 b hb) (by norm_num [i575])
  norm_num at h
  exact h

theorem bridge_minus_4_L (b : ℝ) (hb : rootInterval.Contains b) :
    (0 : ℝ) ≤ n419 b := by
  have h := lower_le_of_contains (a := (0 : ℚ)) (b419 b hb) (by norm_num [i419])
  norm_num at h
  exact h

theorem bridge_minus_4_R (b : ℝ) (hb : rootInterval.Contains b) :
    n420 b ≤ (0 : ℝ) := by
  have h := upper_le_of_contains (a := (0 : ℚ)) (b420 b hb) (by norm_num [i420])
  norm_num at h
  exact h

theorem bridge_minus_4_remaining (b : ℝ) (hb : rootInterval.Contains b) :
    (0 : ℝ) < n429 b := by
  have h := lower_of_contains (a := (0 : ℚ)) (b429 b hb) (by norm_num [i429])
  norm_num at h
  exact h

def conjugatedTransverse (b : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![n3098 b, n3109 b, n3120 b, n3131 b;
  n3138 b, n3145 b, n3152 b, n3159 b;
  n3166 b, n3173 b, n3180 b, n3187 b;
  n3194 b, n3201 b, n3208 b, n3215 b]

def entryBound : Matrix (Fin 4) (Fin 4) ℝ :=
  !![133 / 1000, 41 / 250, 49 / 1000, 11 / 1000;
  6 / 25, 91 / 1000, 47 / 500, 3 / 200;
  21 / 500, 3 / 500, 521 / 1000, 207 / 1000;
  3 / 125, 1 / 500, 211 / 1000, 239 / 500]

theorem entry_abs_0_0 (b : ℝ) (hb : rootInterval.Contains b) :
    |n3098 b| ≤ (133 / 1000 : ℝ) := by
  have h := absolute_of_contains (a := (133 / 1000 : ℚ)) (b3098 b hb) (by norm_num [i3098])
  norm_num at h
  exact h

theorem entry_abs_0_1 (b : ℝ) (hb : rootInterval.Contains b) :
    |n3109 b| ≤ (41 / 250 : ℝ) := by
  have h := absolute_of_contains (a := (41 / 250 : ℚ)) (b3109 b hb) (by norm_num [i3109])
  norm_num at h
  exact h

theorem entry_abs_0_2 (b : ℝ) (hb : rootInterval.Contains b) :
    |n3120 b| ≤ (49 / 1000 : ℝ) := by
  have h := absolute_of_contains (a := (49 / 1000 : ℚ)) (b3120 b hb) (by norm_num [i3120])
  norm_num at h
  exact h

theorem entry_abs_0_3 (b : ℝ) (hb : rootInterval.Contains b) :
    |n3131 b| ≤ (11 / 1000 : ℝ) := by
  have h := absolute_of_contains (a := (11 / 1000 : ℚ)) (b3131 b hb) (by norm_num [i3131])
  norm_num at h
  exact h

theorem entry_abs_1_0 (b : ℝ) (hb : rootInterval.Contains b) :
    |n3138 b| ≤ (6 / 25 : ℝ) := by
  have h := absolute_of_contains (a := (6 / 25 : ℚ)) (b3138 b hb) (by norm_num [i3138])
  norm_num at h
  exact h

theorem entry_abs_1_1 (b : ℝ) (hb : rootInterval.Contains b) :
    |n3145 b| ≤ (91 / 1000 : ℝ) := by
  have h := absolute_of_contains (a := (91 / 1000 : ℚ)) (b3145 b hb) (by norm_num [i3145])
  norm_num at h
  exact h

theorem entry_abs_1_2 (b : ℝ) (hb : rootInterval.Contains b) :
    |n3152 b| ≤ (47 / 500 : ℝ) := by
  have h := absolute_of_contains (a := (47 / 500 : ℚ)) (b3152 b hb) (by norm_num [i3152])
  norm_num at h
  exact h

theorem entry_abs_1_3 (b : ℝ) (hb : rootInterval.Contains b) :
    |n3159 b| ≤ (3 / 200 : ℝ) := by
  have h := absolute_of_contains (a := (3 / 200 : ℚ)) (b3159 b hb) (by norm_num [i3159])
  norm_num at h
  exact h

theorem entry_abs_2_0 (b : ℝ) (hb : rootInterval.Contains b) :
    |n3166 b| ≤ (21 / 500 : ℝ) := by
  have h := absolute_of_contains (a := (21 / 500 : ℚ)) (b3166 b hb) (by norm_num [i3166])
  norm_num at h
  exact h

theorem entry_abs_2_1 (b : ℝ) (hb : rootInterval.Contains b) :
    |n3173 b| ≤ (3 / 500 : ℝ) := by
  have h := absolute_of_contains (a := (3 / 500 : ℚ)) (b3173 b hb) (by norm_num [i3173])
  norm_num at h
  exact h

theorem entry_abs_2_2 (b : ℝ) (hb : rootInterval.Contains b) :
    |n3180 b| ≤ (521 / 1000 : ℝ) := by
  have h := absolute_of_contains (a := (521 / 1000 : ℚ)) (b3180 b hb) (by norm_num [i3180])
  norm_num at h
  exact h

theorem entry_abs_2_3 (b : ℝ) (hb : rootInterval.Contains b) :
    |n3187 b| ≤ (207 / 1000 : ℝ) := by
  have h := absolute_of_contains (a := (207 / 1000 : ℚ)) (b3187 b hb) (by norm_num [i3187])
  norm_num at h
  exact h

theorem entry_abs_3_0 (b : ℝ) (hb : rootInterval.Contains b) :
    |n3194 b| ≤ (3 / 125 : ℝ) := by
  have h := absolute_of_contains (a := (3 / 125 : ℚ)) (b3194 b hb) (by norm_num [i3194])
  norm_num at h
  exact h

theorem entry_abs_3_1 (b : ℝ) (hb : rootInterval.Contains b) :
    |n3201 b| ≤ (1 / 500 : ℝ) := by
  have h := absolute_of_contains (a := (1 / 500 : ℚ)) (b3201 b hb) (by norm_num [i3201])
  norm_num at h
  exact h

theorem entry_abs_3_2 (b : ℝ) (hb : rootInterval.Contains b) :
    |n3208 b| ≤ (211 / 1000 : ℝ) := by
  have h := absolute_of_contains (a := (211 / 1000 : ℚ)) (b3208 b hb) (by norm_num [i3208])
  norm_num at h
  exact h

theorem entry_abs_3_3 (b : ℝ) (hb : rootInterval.Contains b) :
    |n3215 b| ≤ (239 / 500 : ℝ) := by
  have h := absolute_of_contains (a := (239 / 500 : ℚ)) (b3215 b hb) (by norm_num [i3215])
  norm_num at h
  exact h

theorem conjugated_entry_bound (b : ℝ) (hb : rootInterval.Contains b)
    (i j : Fin 4) : |conjugatedTransverse b i j| ≤ entryBound i j := by
  fin_cases i <;> fin_cases j
  · exact entry_abs_0_0 b hb
  · exact entry_abs_0_1 b hb
  · exact entry_abs_0_2 b hb
  · exact entry_abs_0_3 b hb
  · exact entry_abs_1_0 b hb
  · exact entry_abs_1_1 b hb
  · exact entry_abs_1_2 b hb
  · exact entry_abs_1_3 b hb
  · exact entry_abs_2_0 b hb
  · exact entry_abs_2_1 b hb
  · exact entry_abs_2_2 b hb
  · exact entry_abs_2_3 b hb
  · exact entry_abs_3_0 b hb
  · exact entry_abs_3_1 b hb
  · exact entry_abs_3_2 b hb
  · exact entry_abs_3_3 b hb

theorem conjugated_row_bound (b : ℝ) (hb : rootInterval.Contains b) (i : Fin 4) :
    ∑ j, |conjugatedTransverse b i j| ≤ (![357,440,776,715] : Fin 4 → ℝ) i / 1000 := by
  have h0 := conjugated_entry_bound b hb i 0
  have h1 := conjugated_entry_bound b hb i 1
  have h2 := conjugated_entry_bound b hb i 2
  have h3 := conjugated_entry_bound b hb i 3
  fin_cases i <;> norm_num [entryBound, Fin.sum_univ_succ] at * <;> linarith

theorem conjugated_rows_le (b : ℝ) (hb : rootInterval.Contains b) (i : Fin 4) :
    ∑ j, |conjugatedTransverse b i j| ≤ (78 / 100 : ℝ) := by
  have h := conjugated_row_bound b hb i
  fin_cases i <;> norm_num at h ⊢ <;> linarith

theorem conjugated_mulVec_bound (b : ℝ) (hb : rootInterval.Contains b) (v : Fin 4 → ℝ) :
    ‖(conjugatedTransverse b).mulVec v‖ ≤ (78 / 100 : ℝ) * ‖v‖ := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (by norm_num) (norm_nonneg v))).2
  intro i
  rw [Real.norm_eq_abs]
  change |∑ j, conjugatedTransverse b i j * v j| ≤ _
  calc
    _ ≤ ∑ j, |conjugatedTransverse b i j * v j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |conjugatedTransverse b i j| * ‖v‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm v j
    _ = (∑ j, |conjugatedTransverse b i j|) * ‖v‖ := (Finset.sum_mul _ _ _).symm
    _ ≤ (78 / 100 : ℝ) * ‖v‖ :=
      mul_le_mul_of_nonneg_right (conjugated_rows_le b hb i) (norm_nonneg v)

theorem root_conjugated_mulVec_bound (v : Fin 4 → ℝ) :
    ‖(conjugatedTransverse root).mulVec v‖ ≤ (78 / 100 : ℝ) * ‖v‖ :=
  conjugated_mulVec_bound root root_mem_interval v

end
end BFGS.Counterexample.Trace
