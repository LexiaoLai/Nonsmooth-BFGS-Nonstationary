import BFGS.Counterexample.TraceBridge
import BFGS.Counterexample.Certificates.IntervalBounds
import BFGS.Counterexample.Neighborhood
import BFGS.Counterexample.Realization

/-! The actual cycle dynamics and finite phase safety certificate
for the root and cycle used in the manuscript. -/
namespace BFGS.Counterexample.PhaseDynamics
noncomputable section
open BFGS.Algorithm BFGS.StateSpace CycleDynamics
set_option maxHeartbeats 0
set_option maxRecDepth 10000
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.vecHead Matrix.vecTail
@[local simp] private theorem vector_five_four {α : Type*} (a b c d e : α) :
    (![a,b,c,d,e] : Fin 5 → α) 4 = e := rfl
@[local simp] private theorem castSucc_two : (2 : Fin 4).castSucc = (2 : Fin 5) := rfl
@[local simp] private theorem castSucc_three : (3 : Fin 4).castSucc = (3 : Fin 5) := rfl

/-- A literal state of the four-step cycle. -/
def state (b : ℝ) (i : Fin 5) : State := pack (phasePoint b i) (phaseMetric b i)

def center : TransverseSpace := ![(x0 root).1,(x0 root).2,1/2,root/4+1/8]

def smoothSet : Set Vec := {x | x.1-x.2/20 ≠ 0}

@[simp] theorem state_point (b : ℝ) (i : Fin 5) : point (state b i) = phasePoint b i :=
  point_pack _ _

@[simp] theorem state_metric (b : ℝ) (i : Fin 5) : metric (state b i) = phaseMetric b i :=
  metric_pack _ _

theorem embed_center : embed center = state root 0 := by
  ext i
  fin_cases i <;> rfl

theorem phasePoint_next (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) (i : Fin 4) :
    phasePoint b i.succ = phasePoint b i.castSucc + phaseStep b i := by
  fin_cases i
  · simpa [phasePoint,phaseStep,phaseMetric,phaseGradient,s0] using position0 b hb hp
  · simpa [phasePoint,phaseStep,phaseMetric,phaseGradient,s1] using position1 b hb hp
  · simpa [phasePoint,phaseStep,phaseMetric,phaseGradient,s2] using position2 b hb hp
  · simpa [phasePoint,phaseStep,phaseMetric,phaseGradient,s3] using position3 b hb hp

theorem phaseMetric_next (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) (i : Fin 4) :
    phaseMetric b i.succ = update (phaseMetric b i.castSucc) (phaseStep b i)
      (phaseGradient b i.succ-phaseGradient b i.castSucc) := by
  fin_cases i
  · simpa [phaseMetric,phaseStep,phaseGradient,s0,y0] using update0 b hb hp
  · simpa [phaseMetric,phaseStep,phaseGradient,s1,y1] using update1 b hb hp
  · simpa [phaseMetric,phaseStep,phaseGradient,s2,y2] using update2 b hb hp
  · simpa [phaseMetric,phaseStep,phaseGradient,s3,y3] using update3 b hb hp

theorem phaseMetric_positive (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) (i : Fin 5) :
    (phaseMetric b i).Positive := by
  obtain ⟨h0,h1,h2,h3,h4⟩ := metrics_positive b hb hp
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem phaseCurvature_positive (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) (i : Fin 4) :
    0 < phaseCurvature b i := by
  obtain ⟨h0,h1,h2,h3⟩ := curvature_positive b hb hp
  fin_cases i
  · simpa [phaseCurvature,phaseStep,phaseMetric,phaseGradient,s0,y0] using h0
  · simpa [phaseCurvature,phaseStep,phaseMetric,phaseGradient,s1,y1] using h1
  · simpa [phaseCurvature,phaseStep,phaseMetric,phaseGradient,s2,y2] using h2
  · simpa [phaseCurvature,phaseStep,phaseMetric,phaseGradient,s3,y3] using h3

theorem state_direction (b : ℝ) (g : Vec → Vec)
    (hgradient : ∀ i : Fin 5, g (phasePoint b i) = phaseGradient b i) (i : Fin 4) :
    direction g (state b i.castSucc) = phaseStep b i := by
  simp only [direction,state_point,state_metric,hgradient,phaseStep]

theorem state_next_point (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) (g : Vec → Vec)
    (hgradient : ∀ i : Fin 5, g (phasePoint b i) = phaseGradient b i) (i : Fin 4) :
    point (state b i.castSucc)+direction g (state b i.castSucc) = phasePoint b i.succ := by
  rw [state_point,state_direction b g hgradient,← phasePoint_next b hb hp]

theorem state_cycleStep (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) (g : Vec → Vec)
    (hgradient : ∀ i : Fin 5, g (phasePoint b i) = phaseGradient b i) (i : Fin 4) :
    cycleStep g (state b i.castSucc) = state b i.succ := by
  simp only [cycleStep,acceptedStep,one_smul,
    state_point,state_metric,hgradient,state_direction b g hgradient]
  rw [← phasePoint_next b hb hp i, hgradient, ← phaseMetric_next b hb hp]
  rfl

theorem state_curvature (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) (g : Vec → Vec)
    (hgradient : ∀ i : Fin 5, g (phasePoint b i) = phaseGradient b i) (i : Fin 4) :
    curvature g 1 (state b i.castSucc) = phaseCurvature b i := by
  simp only [curvature,one_smul,state_point,hgradient,state_direction b g hgradient]
  rw [← phasePoint_next b hb hp i, hgradient]
  rfl

theorem state_curvature_ne (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) (g : Vec → Vec)
    (hgradient : ∀ i : Fin 5, g (phasePoint b i) = phaseGradient b i) (i : Fin 4) :
    curvature g 1 (state b i.castSucc) ≠ 0 := by
  rw [state_curvature b hb hp g hgradient]
  exact (phaseCurvature_positive b hb hp i).ne'

theorem state_closes (b : ℝ) : state b 4 = r • state b 0 := by
  change pack (x4 b) (H4 b) = r • pack (x0 b) (H0 b)
  exact pack_scale r (x0 b) (H0 b)

theorem state_iterate (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) (g : Vec → Vec)
    (hgradient : ∀ i : Fin 5, g (phasePoint b i) = phaseGradient b i) (i : Fin 5) :
    (cycleStep g)^[i.val] (state b 0) = state b i := by
  have h0 := state_cycleStep b hb hp g hgradient 0
  have h1 := state_cycleStep b hb hp g hgradient 1
  have h2 := state_cycleStep b hb hp g hgradient 2
  have h3 := state_cycleStep b hb hp g hgradient 3
  change cycleStep g (state b 0) = state b 1 at h0
  change cycleStep g (state b 1) = state b 2 at h1
  change cycleStep g (state b 2) = state b 3 at h2
  change cycleStep g (state b 3) = state b 4 at h3
  fin_cases i <;> simp only [Function.iterate_succ_apply',Function.iterate_zero_apply,h0,h1,h2,h3] <;> rfl

theorem phaseNormSquared_bounds (i : Fin 5) :
    0 < phaseNormSquared root i ∧ phaseNormSquared root i < 8 := by
  rw [← traceNormSquared_eq root root_half_lt root_quartic]
  fin_cases i
  · exact ⟨Trace.norm_positive_0 root Trace.root_mem_interval,
      Trace.norm_bound_0 root Trace.root_mem_interval⟩
  · exact ⟨Trace.norm_positive_1 root Trace.root_mem_interval,
      Trace.norm_bound_1 root Trace.root_mem_interval⟩
  · exact ⟨Trace.norm_positive_2 root Trace.root_mem_interval,
      Trace.norm_bound_2 root Trace.root_mem_interval⟩
  · exact ⟨Trace.norm_positive_3 root Trace.root_mem_interval,
      Trace.norm_bound_3 root Trace.root_mem_interval⟩
  · exact ⟨Trace.norm_positive_4 root Trace.root_mem_interval,
      Trace.norm_bound_4 root Trace.root_mem_interval⟩

theorem phasePoint_bound (i : Fin 5) : ‖phasePoint root i‖ < 4 := by
  have h := (phaseNormSquared_bounds i).2
  dsimp [phaseNormSquared,dot] at h
  rw [Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs,max_lt_iff,abs_lt,abs_lt]
  constructor <;> constructor <;>
    nlinarith [sq_nonneg ((phasePoint root i).1),sq_nonneg ((phasePoint root i).2)]

theorem phasePoint_ne_zero (i : Fin 5) : phasePoint root i ≠ 0 := by
  intro hz
  have h := (phaseNormSquared_bounds i).1
  simp [phaseNormSquared,hz,dot] at h

theorem phaseCoordinate_ne (i : Fin 4) : phaseCoordinate root i ≠ 0 := by
  rw [← traceCoordinate_eq root root_half_lt root_quartic]
  fin_cases i
  · exact (Trace.coordinate_sign_0 root Trace.root_mem_interval).ne'
  · exact (Trace.coordinate_sign_1 root Trace.root_mem_interval).ne'
  · exact (Trace.coordinate_sign_2 root Trace.root_mem_interval).ne
  · exact (Trace.coordinate_sign_3 root Trace.root_mem_interval).ne

theorem phasePoint_mem_smoothSet (i : Fin 5) : phasePoint root i ∈ smoothSet := by
  fin_cases i
  · exact phaseCoordinate_ne 0
  · exact phaseCoordinate_ne 1
  · exact phaseCoordinate_ne 2
  · exact phaseCoordinate_ne 3
  · have h0 := phaseCoordinate_ne 0
    change (x0 root).1-(x0 root).2/20 ≠ 0 at h0
    have he := mul_ne_zero r_pos.ne' h0
    change (x4 root).1-(x4 root).2/20 ≠ 0
    convert he using 1
    simp only [x4,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
    ring

theorem smoothSet_open : IsOpen smoothSet := by
  change IsOpen ((fun x : Vec => x.1-x.2/20) ⁻¹' {a : ℝ | a ≠ 0})
  exact isOpen_ne.preimage (continuous_fst.sub (continuous_snd.div_const 20))

theorem phaseArmijo_positive (i : Fin 4) : 0 < phaseArmijo root i := by
  rw [← traceArmijo_eq root root_half_lt root_quartic]
  fin_cases i
  · exact lt_trans (by norm_num) (Trace.armijo_positive_0 root Trace.root_mem_interval)
  · exact lt_trans (by norm_num) (Trace.armijo_positive_1 root Trace.root_mem_interval)
  · exact lt_trans (by norm_num) (Trace.armijo_positive_2 root Trace.root_mem_interval)
  · exact lt_trans (by norm_num) (Trace.armijo_positive_3 root Trace.root_mem_interval)

theorem phaseWolfe_positive (i : Fin 4) : 0 < phaseWolfe root i := by
  rw [← traceWolfe_eq root root_half_lt root_quartic]
  fin_cases i
  · exact Trace.wolfe_positive_0 root Trace.root_mem_interval
  · exact Trace.wolfe_positive_1 root Trace.root_mem_interval
  · exact Trace.wolfe_positive_2 root Trace.root_mem_interval
  · exact Trace.wolfe_positive_3 root Trace.root_mem_interval

theorem state_armijoMargin (f : Vec → ℝ) (g : Vec → Vec)
    (hvalue : ∀ i : Fin 5, f (phasePoint root i) = phaseValue root i)
    (hgradient : ∀ i : Fin 5, g (phasePoint root i) = phaseGradient root i) (i : Fin 4) :
    CycleDynamics.armijoMargin f g (3/100) (state root i.castSucc) = phaseArmijo root i := by
  unfold CycleDynamics.armijoMargin
  rw [state_next_point root root_half_lt root_quartic g hgradient]
  simp only [state_point,state_direction root g hgradient,hvalue,hgradient,phaseArmijo]

theorem state_wolfeMargin (g : Vec → Vec)
    (hgradient : ∀ i : Fin 5, g (phasePoint root i) = phaseGradient root i) (i : Fin 4) :
    CycleDynamics.wolfeMargin g (3/5) (state root i.castSucc) = phaseWolfe root i := by
  unfold CycleDynamics.wolfeMargin
  rw [state_next_point root root_half_lt root_quartic g hgradient]
  simp only [state_point,state_direction root g hgradient,hgradient,
    phaseWolfe,dot,Prod.fst_sub,Prod.snd_sub,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
  ring

/-- Every numerical premise in the local safety statement is discharged. The
remaining hypotheses identify the values and gradients of the realized function. -/
theorem phaseCertificate_of_data (f : Vec → ℝ) (g : Vec → Vec)
    (hvalue : ∀ i : Fin 5, f (phasePoint root i) = phaseValue root i)
    (hgradient : ∀ i : Fin 5, g (phasePoint root i) = phaseGradient root i) (i : Fin 4) :
    PhaseCertificate f g (3/100) (3/5) smoothSet 4 (state root i.castSucc) := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [state_point]
    exact phasePoint_mem_smoothSet i.castSucc
  · rw [state_next_point root root_half_lt root_quartic g hgradient]
    exact phasePoint_mem_smoothSet i.succ
  · rw [state_metric]
    exact phaseMetric_positive root root_half_lt root_quartic i.castSucc
  · rw [state_armijoMargin f g hvalue hgradient]
    exact phaseArmijo_positive i
  · rw [state_wolfeMargin g hgradient]
    exact phaseWolfe_positive i
  · rw [state_point]
    exact phasePoint_bound i.castSucc
  · rw [state_next_point root root_half_lt root_quartic g hgradient]
    exact phasePoint_bound i.succ
  · exact state_curvature_ne root root_half_lt root_quartic g hgradient i

theorem cycle_of_data (g : Vec → Vec)
    (hgradient : ∀ i : Fin 5, g (phasePoint root i) = phaseGradient root i) :
    (cycleStep g)^[4] (embed center) = r • embed center := by
  rw [embed_center]
  exact (state_iterate root root_half_lt root_quartic g hgradient 4).trans (state_closes root)

theorem iterate_certificates_of_data (f : Vec → ℝ) (g : Vec → Vec)
    (hvalue : ∀ i : Fin 5, f (phasePoint root i) = phaseValue root i)
    (hgradient : ∀ i : Fin 5, g (phasePoint root i) = phaseGradient root i) (i : Fin 4) :
    PhaseCertificate f g (3/100) (3/5) smoothSet 4
      ((cycleStep g)^[i.val] (embed center)) := by
  rw [embed_center]
  have hi : (cycleStep g)^[i.val] (state root 0) = state root i.castSucc :=
    state_iterate root root_half_lt root_quartic g hgradient i.castSucc
  rw [hi]
  exact phaseCertificate_of_data f g hvalue hgradient i

/-- The realized objective satisfies every endpoint safety condition for all
four phases, with no remaining algebraic or numerical premise. -/
theorem phase_certificate (i : Fin 4) :
    PhaseCertificate Realization.f Realization.g (3/100) (3/5) smoothSet 4
      (state root i.castSucc) :=
  phaseCertificate_of_data Realization.f Realization.g
    Realization.f_phase_all Realization.g_phase_all i

theorem actual_cycleStep (i : Fin 4) :
    cycleStep Realization.g (state root i.castSucc) = state root i.succ :=
  state_cycleStep root root_half_lt root_quartic Realization.g Realization.g_phase_all i

theorem actual_cycle :
    (cycleStep Realization.g)^[4] (embed center) = r • embed center :=
  cycle_of_data Realization.g Realization.g_phase_all

theorem actual_iterate (i : Fin 5) :
    (cycleStep Realization.g)^[i.val] (embed center) = state root i := by
  rw [embed_center]
  exact state_iterate root root_half_lt root_quartic Realization.g Realization.g_phase_all i

theorem actual_iterate_certificates (i : Fin 4) :
    PhaseCertificate Realization.f Realization.g (3/100) (3/5) smoothSet 4
      ((cycleStep Realization.g)^[i.val] (embed center)) :=
  iterate_certificates_of_data Realization.f Realization.g
    Realization.f_phase_all Realization.g_phase_all i

theorem actual_g_differentiable (x : Vec) (hx : x ∈ smoothSet) :
    DifferentiableAt ℝ Realization.g x := by
  apply (Realization.g_derivative x _).differentiableAt
  simpa only [smoothSet,Set.mem_ofPred_eq,shearRow_dot,div_eq_mul_inv,one_mul,mul_comm] using hx

theorem actual_gradient (x : Vec) (hx : x ∈ smoothSet) :
    IsGradientAt Realization.f (Realization.g x) x := by
  apply Realization.f_gradient
  simpa only [smoothSet,Set.mem_ofPred_eq,shearRow_dot,div_eq_mul_inv,one_mul,mul_comm] using hx

theorem actual_phase_accepted (i : Fin 4) :
    StepAccepted Realization.f Realization.g (3/100) (3/5) (state root i.castSucc) :=
  StepAccepted.of_margins _ _ _ _ _ (phase_certificate i).armijo_margin
    (phase_certificate i).wolfe_margin

theorem actual_phase_bfgsStep (fuel : ℕ) (i : Fin 4) :
    bfgsStep Realization.f Realization.g (3/100) (3/5) (fuel+1)
      (state root i.castSucc) = some (state root i.succ) := by
  rw [bfgsStep_eq_cycleStep _ _ _ _ _ _ (actual_phase_accepted i), actual_cycleStep i]

/-- A compact unconditional collection of the root, actual cycle, and safety
claims. This theorem does not assume a certificate record from outside Lean. -/
theorem cycle_certificate :
    quartic root = 0 ∧
    root ∈ Set.Icc (91781039164 / 10 ^ 11 : ℝ) (91781039165 / 10 ^ 11) ∧
    (∀ i : Fin 5, (phaseMetric root i).Positive ∧ phaseNormSquared root i < 8) ∧
    (cycleStep Realization.g)^[4] (embed center) = r • embed center ∧
    (∀ i : Fin 4, PhaseCertificate Realization.f Realization.g
      (3/100) (3/5) smoothSet 4 ((cycleStep Realization.g)^[i.val] (embed center))) ∧
    (∀ fuel : ℕ, ∀ i : Fin 4,
      bfgsStep Realization.f Realization.g (3/100) (3/5) (fuel+1)
        (state root i.castSucc) = some (state root i.succ)) :=
  ⟨root_quartic, root_mem_narrow,
    fun i => ⟨phaseMetric_positive root root_half_lt root_quartic i,
      (phaseNormSquared_bounds i).2⟩,
    actual_cycle, actual_iterate_certificates, actual_phase_bfgsStep⟩

end
end BFGS.Counterexample.PhaseDynamics
