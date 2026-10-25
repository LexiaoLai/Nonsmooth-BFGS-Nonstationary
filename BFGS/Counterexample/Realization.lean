import BFGS.Counterexample.Analysis
import BFGS.Counterexample.TraceBridge
import BFGS.Counterexample.Certificates.IntervalBounds
import BFGS.Counterexample.DerivativeCore
import BFGS.Analysis.SemialgebraicObjective

/-! Lemma 2.10: realization of the exact cycle. -/
namespace BFGS.Counterexample.Realization
noncomputable section
open Algorithm Trace Filter Topology
open scoped ContDiff
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.vecHead Matrix.vecTail

def firstPhase (br : Fin 2) : Fin 4 := if br = 0 then 2 else 0
def lastPhase (br : Fin 2) : Fin 4 := if br = 0 then 3 else 1

def nodeT (br : Fin 2) : ℕ → ℝ
  | 0 => -2 | 1 => -1 | 2 => phaseNodeT root (firstPhase br)
  | 3 => phaseNodeT root (lastPhase br) | 4 => 6 | _ => 7

def nodeEta (br : Fin 2) : ℕ → ℝ
  | 0 => -2 | 1 => -1 | 2 => phaseNodeEta root (firstPhase br)
  | 3 => phaseNodeEta root (lastPhase br) | 4 => 6 | _ => 7

def nodeD (br : Fin 2) : ℕ → ℝ
  | 2 => phaseNodeD root (firstPhase br)
  | 3 => phaseNodeD root (lastPhase br) | _ => 1

def nodeK (br : Fin 2) : ℕ → ℝ
  | 2 => phaseNodeK root (firstPhase br)
  | 3 => phaseNodeK root (lastPhase br) | _ => 0

private theorem interval_condition {a c A B : ℝ}
    (hgap : 1 < c-a) (hsec : (1/2 : ℝ) < (B-A)/(c-a)) :
    a < c ∧ (1/100 : ℝ)*(c-a) < B-A := by
  have hgap0 : 0 < c-a := by linarith
  have hs := (lt_div_iff₀ hgap0).mp hsec
  constructor <;> nlinarith

private theorem nodeStep (br : Fin 2) (i : ℕ) (hi : i < 5) :
    nodeT br i < nodeT br (i+1) ∧ (1/100 : ℝ) < nodeD br i ∧
    (1/100 : ℝ) < nodeD br (i+1) ∧
    (1/100 : ℝ)*(nodeT br (i+1)-nodeT br i) < nodeEta br (i+1)-nodeEta br i := by
  fin_cases br
  · interval_cases i
    · norm_num [nodeT,nodeEta,nodeD,firstPhase,lastPhase]
    · have hg := gap_positive_minus_0 root root_mem_interval
      have hs := secant_lower_minus_0 root root_mem_interval
      have hd0 := slope_lower_2 root root_mem_interval
      have hd1 := slope_lower_3 root root_mem_interval
      simp only [n397, n398, n399, n400, n15, div_eq_mul_inv, one_mul] at hg hs
      have hi := interval_condition (a := -1) (c := n272 root) (A := -1) (B := n273 root)
        (by simpa [sub_eq_add_neg] using hg)
        (by simpa [sub_eq_add_neg, div_eq_mul_inv] using hs)
      norm_num [nodeT,nodeEta,nodeD,firstPhase,lastPhase,
        ← traceNodeT_eq root root_half_lt root_quartic,
        ← traceNodeEta_eq root root_half_lt root_quartic,
        ← traceNodeD_eq root root_half_lt root_quartic,
        traceNodeT,traceNodeEta,traceNodeD,n15] at ⊢
      exact ⟨hi.1, by linarith, by linarith [hi.2]⟩
    · have hg := gap_positive_minus_1 root root_mem_interval
      have hs := secant_lower_minus_1 root root_mem_interval
      have hd0 := slope_lower_2 root root_mem_interval
      have hd1 := slope_lower_3 root root_mem_interval
      simp only [n401, n402, n403, n404, n405, n406, n15, div_eq_mul_inv, one_mul] at hg hs
      have hi := interval_condition (a := n272 root) (c := n288 root) (A := n273 root) (B := n289 root)
        (by simpa [sub_eq_add_neg] using hg)
        (by simpa [sub_eq_add_neg, div_eq_mul_inv] using hs)
      norm_num [nodeT,nodeEta,nodeD,firstPhase,lastPhase,
        ← traceNodeT_eq root root_half_lt root_quartic,
        ← traceNodeEta_eq root root_half_lt root_quartic,
        ← traceNodeD_eq root root_half_lt root_quartic,
        traceNodeT,traceNodeEta,traceNodeD,n15] at ⊢
      exact ⟨hi.1, by linarith, by linarith, by linarith [hi.2]⟩
    · have hg := gap_positive_minus_2 root root_mem_interval
      have hs := secant_lower_minus_2 root root_mem_interval
      have hd0 := slope_lower_2 root root_mem_interval
      have hd1 := slope_lower_3 root root_mem_interval
      simp only [n382, n407, n408, n409, n410, n411, n412, n15, div_eq_mul_inv, one_mul] at hg hs
      have hi := interval_condition (a := n288 root) (c := 6) (A := n289 root) (B := 6)
        (by simpa [sub_eq_add_neg] using hg)
        (by simpa [sub_eq_add_neg, div_eq_mul_inv] using hs)
      norm_num [nodeT,nodeEta,nodeD,firstPhase,lastPhase,
        ← traceNodeT_eq root root_half_lt root_quartic,
        ← traceNodeEta_eq root root_half_lt root_quartic,
        ← traceNodeD_eq root root_half_lt root_quartic,
        traceNodeT,traceNodeEta,traceNodeD,n15] at ⊢
      exact ⟨hi.1, by linarith, by linarith [hi.2]⟩
    · norm_num [nodeT,nodeEta,nodeD,firstPhase,lastPhase]
  · interval_cases i
    · norm_num [nodeT,nodeEta,nodeD,firstPhase,lastPhase]
    · have hg := gap_positive_plus_0 root root_mem_interval
      have hs := secant_lower_plus_0 root root_mem_interval
      have hd0 := slope_lower_0 root root_mem_interval
      have hd1 := slope_lower_1 root root_mem_interval
      simp only [n383, n384, n385, n386, n15, div_eq_mul_inv, one_mul] at hg hs
      have hi := interval_condition (a := -1) (c := n246 root) (A := -1) (B := n247 root)
        (by simpa [sub_eq_add_neg] using hg)
        (by simpa [sub_eq_add_neg, div_eq_mul_inv] using hs)
      norm_num [nodeT,nodeEta,nodeD,firstPhase,lastPhase,
        ← traceNodeT_eq root root_half_lt root_quartic,
        ← traceNodeEta_eq root root_half_lt root_quartic,
        ← traceNodeD_eq root root_half_lt root_quartic,
        traceNodeT,traceNodeEta,traceNodeD,n15] at ⊢
      exact ⟨hi.1, by linarith, by linarith [hi.2]⟩
    · have hg := gap_positive_plus_1 root root_mem_interval
      have hs := secant_lower_plus_1 root root_mem_interval
      have hd0 := slope_lower_0 root root_mem_interval
      have hd1 := slope_lower_1 root root_mem_interval
      simp only [n387, n388, n389, n390, n391, n392, n15, div_eq_mul_inv, one_mul] at hg hs
      have hi := interval_condition (a := n246 root) (c := n259 root) (A := n247 root) (B := n259 root)
        (by simpa [sub_eq_add_neg] using hg)
        (by simpa [sub_eq_add_neg, div_eq_mul_inv] using hs)
      norm_num [nodeT,nodeEta,nodeD,firstPhase,lastPhase,
        ← traceNodeT_eq root root_half_lt root_quartic,
        ← traceNodeEta_eq root root_half_lt root_quartic,
        ← traceNodeD_eq root root_half_lt root_quartic,
        traceNodeT,traceNodeEta,traceNodeD,n15] at ⊢
      exact ⟨hi.1, by linarith, by linarith [hi.2]⟩
    · have hg := gap_positive_plus_2 root root_mem_interval
      have hs := secant_lower_plus_2 root root_mem_interval
      have hd0 := slope_lower_0 root root_mem_interval
      have hd1 := slope_lower_1 root root_mem_interval
      simp only [n382, n393, n394, n395, n396, n15, div_eq_mul_inv, one_mul] at hg hs
      have hi := interval_condition (a := n259 root) (c := 6) (A := n259 root) (B := 6)
        (by simpa [sub_eq_add_neg] using hg)
        (by simpa [sub_eq_add_neg, div_eq_mul_inv] using hs)
      norm_num [nodeT,nodeEta,nodeD,firstPhase,lastPhase,
        ← traceNodeT_eq root root_half_lt root_quartic,
        ← traceNodeEta_eq root root_half_lt root_quartic,
        ← traceNodeD_eq root root_half_lt root_quartic,
        traceNodeT,traceNodeEta,traceNodeD,n15] at ⊢
      exact ⟨hi.1, by linarith [hi.2]⟩
    · norm_num [nodeT,nodeEta,nodeD,firstPhase,lastPhase]

/-- The supplement's deterministic least-degree polynomial realization of
the manuscript's interpolation data. -/
def profileData (br : Fin 2) :=
  canonicalProfile 5 (nodeT br) (nodeEta br) (nodeD br) (nodeK br) (1/100)
    (by norm_num [nodeD]) rfl rfl (nodeStep br)

def profile (br : Fin 2) : C2Profile := (profileData br).val

theorem profile_spec (br : Fin 2) : PiecewisePolynomial (profile br).value ∧
    (∀ i ≤ 5, MatchesJet (profile br) (nodeT br i) (nodeEta br i) (nodeD br i) (nodeK br i)) ∧
    (∀ t, (1/100 : ℝ) ≤ (profile br).slope t) ∧ HasIdentityTails (profile br) := by
  have h := (profileData br).property
  refine ⟨h.1,h.2.1,h.2.2.1,hasIdentityTails_of_two_tails (profile br) (a := -2) (b := 7) ?_ ?_⟩
  · intro t ht
    simpa [nodeT,nodeEta,nodeD,profile] using h.2.2.2.1 t ht
  · intro t ht
    simpa [nodeT,nodeEta,nodeD,profile] using h.2.2.2.2 t ht

def f : Vec → ℝ := shearObjective (1/20) (profile 0) (profile 1)
def g : Vec → Vec := shearGradient (1/20) (profile 0) (profile 1)
def hessian : Vec → (Vec →L[ℝ] Vec) := shearHessian (1/20) (profile 0) (profile 1)

theorem f_lipschitz : ∃ K : NNReal, LipschitzWith K f :=
  shearObjective_lipschitz _ _ _ (profile_spec 0).2.2.2 (profile_spec 1).2.2.2

theorem f_continuous : Continuous f := by
  obtain ⟨K,hK⟩ := f_lipschitz
  exact hK.continuous

theorem f_pos_homogeneous (r : ℝ) (hr : 0 < r) (x : Vec) : f (r • x) = r*f x :=
  shearObjective_pos_homogeneous _ _ _ r hr x

theorem g_scale (r : ℝ) (hr : 0 < r) (x : Vec) : g (r • x) = g x :=
  physicalAngularGradient_scale _ _ _ _ x r hr

theorem f_zero : f 0 = 0 := shearObjective_zero _ _ _

theorem f_nonstationary (x : Vec) : 0 ∉ clarkeSubdifferential f x :=
  shearObjective_nonstationary _ (1/100) _ _ (by norm_num) (by norm_num)
    (profile_spec 0).2.2.1 (profile_spec 1).2.2.1 x

theorem f_contDiffAt (x : Vec) (hx : x ≠ 0) : ContDiffAt ℝ 2 f x :=
  shearObjective_contDiffAt _ _ _ (profile_spec 0).2.2.2 (profile_spec 1).2.2.2 x hx

theorem f_gradient (x : Vec) (hx : dot (shearRow (1/20)) x ≠ 0) : IsGradientAt f (g x) x :=
  shearObjective_gradient _ _ _ x hx

theorem g_derivative (x : Vec) (hx : dot (shearRow (1/20)) x ≠ 0) :
    HasFDerivAt g (hessian x) x := shearGradient_derivative _ _ _ x hx

def phaseBranch : Fin 4 → Fin 2 := ![1,1,0,0]
def phaseIndex : Fin 4 → ℕ := ![2,3,2,3]

theorem profile_phase_jet (i : Fin 4) :
    MatchesJet (profile (phaseBranch i)) (phaseNodeT root i)
      (phaseNodeEta root i) (phaseNodeD root i) (phaseNodeK root i) := by
  fin_cases i
  · exact (profile_spec 1).2.1 2 (by norm_num)
  · exact (profile_spec 1).2.1 3 (by norm_num)
  · exact (profile_spec 0).2.1 2 (by norm_num)
  · exact (profile_spec 0).2.1 3 (by norm_num)

theorem phaseCoordinate_eq_dot (i : Fin 4) : phaseCoordinate root i =
    dot (shearRow (1/20)) (phasePoint root i.castSucc) := by
  simp only [phaseCoordinate, shearRow_dot]
  ring

theorem phase_sign (i : Fin 4) :
    if i.val < 2 then 0 < phaseCoordinate root i else phaseCoordinate root i < 0 := by
  rw [← traceCoordinate_eq root root_half_lt root_quartic]
  fin_cases i
  · exact coordinate_sign_0 root root_mem_interval
  · exact coordinate_sign_1 root root_mem_interval
  · exact coordinate_sign_2 root root_mem_interval
  · exact coordinate_sign_3 root root_mem_interval

theorem phaseAbsCoordinate_eq_abs (i : Fin 4) :
    phaseAbsCoordinate root i = |phaseCoordinate root i| := by
  have hs := phase_sign i
  unfold phaseAbsCoordinate
  split_ifs with hi
  · rw [if_pos hi] at hs
    exact (abs_of_pos hs).symm
  · rw [if_neg hi] at hs
    exact (abs_of_neg hs).symm

theorem phase_off_axis (i : Fin 4) : dot (shearRow (1/20)) (phasePoint root i.castSucc) ≠ 0 := by
  rw [← phaseCoordinate_eq_dot]
  have hs := phase_sign i
  split_ifs at hs
  · exact hs.ne'
  · exact hs.ne

theorem profile_choice (i : Fin 4) :
    (if dot (shearRow (1/20)) (phasePoint root i.castSucc) < 0 then profile 0 else profile 1) =
      profile (phaseBranch i) := by
  rw [← phaseCoordinate_eq_dot]
  have hs := phase_sign i
  fin_cases i
  · change (if phaseCoordinate root 0 < 0 then profile 0 else profile 1) = profile 1
    exact if_neg (not_lt.mpr (show 0 < phaseCoordinate root 0 from hs).le)
  · change (if phaseCoordinate root 1 < 0 then profile 0 else profile 1) = profile 1
    exact if_neg (not_lt.mpr (show 0 < phaseCoordinate root 1 from hs).le)
  · change (if phaseCoordinate root 2 < 0 then profile 0 else profile 1) = profile 0
    exact if_pos (show phaseCoordinate root 2 < 0 from hs)
  · change (if phaseCoordinate root 3 < 0 then profile 0 else profile 1) = profile 0
    exact if_pos (show phaseCoordinate root 3 < 0 from hs)

theorem f_phase (i : Fin 4) : f (phasePoint root i.castSucc) = phaseValue root i.castSucc := by
  apply shearObjective_value_of_jet _ _ _ _ _ (phase_off_axis i)
  rw [profile_choice]
  simpa only [phaseNodeT, phaseNodeEta, phaseAbsCoordinate_eq_abs, phaseCoordinate_eq_dot]
    using (profile_phase_jet i).1

theorem g_phase (i : Fin 4) : g (phasePoint root i.castSucc) = phaseGradient root i.castSucc := by
  apply shearGradient_eq_of_jet _ _ _ _ _ (phase_off_axis i)
  · rw [profile_choice]
    simpa only [phaseNodeT,phaseNodeEta,phaseValue,phaseAbsCoordinate_eq_abs,phaseCoordinate_eq_dot]
      using (profile_phase_jet i).1
  · rw [profile_choice]
    simpa only [phaseNodeT,phaseNodeD,shearDirection_dot,phaseAbsCoordinate_eq_abs,phaseCoordinate_eq_dot]
      using (profile_phase_jet i).2.1

theorem phaseHessian_symmetric (i : Fin 5) :
    ∀ z w, dot z (symmetricMap (phaseHessian root i) w) =
      dot (symmetricMap (phaseHessian root i) z) w := by
  intro z w
  simp only [symmetricMap_apply,Sym2.mulV,dot]
  ring

theorem pointHessian_kernel (beta : ℝ) (x : Vec) : (pointHessian beta x).mulV x = 0 := by
  apply Prod.ext <;> simp only [pointHessian,Sym2.mulV,Prod.fst_zero,Prod.snd_zero]
  all_goals ring

theorem phaseHessian_kernel (i : Fin 4) :
    symmetricMap (phaseHessian root i.castSucc) (phasePoint root i.castSucc) = 0 := by
  fin_cases i <;> exact pointHessian_kernel _ _

theorem hessian_phase (i : Fin 4) :
    hessian (phasePoint root i.castSucc) = symmetricMap (phaseHessian root i.castSucc) := by
  apply shearHessian_eq_of_jet _ _ _ _ _ (phase_off_axis i)
    (phaseHessian_symmetric _) (phaseHessian_kernel i)
  rw [profile_choice]
  simpa only [phaseNodeT,phaseNodeK,phaseAbsCoordinate_eq_abs,phaseCoordinate_eq_dot,
    shearDirection,symmetricMap_apply] using (profile_phase_jet i).2.2

theorem g_hasFDerivAt_phase (i : Fin 4) :
    HasFDerivAt g (symmetricMap (phaseHessian root i.castSucc)) (phasePoint root i.castSucc) := by
  rw [← hessian_phase i]
  exact g_derivative _ (phase_off_axis i)

theorem phase_off_axis_all (i : Fin 5) : dot (shearRow (1/20)) (phasePoint root i) ≠ 0 := by
  fin_cases i
  · exact phase_off_axis 0
  · exact phase_off_axis 1
  · exact phase_off_axis 2
  · exact phase_off_axis 3
  · change dot (shearRow (1/20)) (r • x0 root) ≠ 0
    rw [dot_smul_right]
    exact mul_ne_zero r_pos.ne' (phase_off_axis 0)

theorem f_phase_all (i : Fin 5) : f (phasePoint root i) = phaseValue root i := by
  fin_cases i
  · exact f_phase 0
  · exact f_phase 1
  · exact f_phase 2
  · exact f_phase 3
  · change f (r • x0 root) = dot g0 (r • x0 root)
    rw [f_pos_homogeneous _ r_pos, dot_smul_right]
    exact congrArg (fun t : ℝ => r*t) (f_phase 0)

theorem g_phase_all (i : Fin 5) : g (phasePoint root i) = phaseGradient root i := by
  fin_cases i
  · exact g_phase 0
  · exact g_phase 1
  · exact g_phase 2
  · exact g_phase 3
  · change g (r • x0 root) = g0
    rw [g_scale _ r_pos]
    exact g_phase 0

theorem hessian_scale (t : ℝ) (ht : 0 < t) (x : Vec) :
    hessian (t • x) = t⁻¹ • hessian x :=
  physicalAngularHessian_scale _ _ _ _ x t ht

theorem symmetricMap_scale (H : Sym2) (t : ℝ) :
    symmetricMap (H.scale t) = t • symmetricMap H := by
  apply ContinuousLinearMap.ext
  intro v
  apply Prod.ext <;> simp [symmetricMap,Sym2.scale] <;> ring

theorem hessian_phase_all (i : Fin 5) :
    hessian (phasePoint root i) = symmetricMap (phaseHessian root i) := by
  fin_cases i
  · exact hessian_phase 0
  · exact hessian_phase 1
  · exact hessian_phase 2
  · exact hessian_phase 3
  · change hessian (r • x0 root) = symmetricMap ((pointHessian (19/10) (x0 root)).scale (1/r))
    rw [hessian_scale _ r_pos, symmetricMap_scale, one_div]
    exact congrArg (fun L : Vec →L[ℝ] Vec => r⁻¹ • L) (hessian_phase 0)

theorem g_hasFDerivAt_phase_all (i : Fin 5) :
    HasFDerivAt g (symmetricMap (phaseHessian root i)) (phasePoint root i) := by
  rw [← hessian_phase_all i]
  exact g_derivative _ (phase_off_axis_all i)

theorem f_piecewiseRational : Semialgebraic.PiecewiseRationalOn Set.univ
    (fun z : Semialgebraic.Space 3 => f (z 0,z 1)) :=
  Semialgebraic.physicalAngular_piecewiseRational (profile 0) (profile 1)
    (profile_spec 0).1 (profile_spec 1).1 (shearRow (1/20)) verticalRow

theorem f_semialgebraic : Semialgebraic.IsSemialgebraicFunction f := by
  simpa only [Semialgebraic.IsSemialgebraicFunction, Set.mem_univ, true_and] using
    f_piecewiseRational.graph (Semialgebraic.Poly.coord (2 : Fin 3))

end
end BFGS.Counterexample.Realization
