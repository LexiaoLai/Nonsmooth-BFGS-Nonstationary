import BFGS.Counterexample.DerivativeLinear
import BFGS.Counterexample.Certificates.DerivativeMatrices
import BFGS.Counterexample.Certificates.DerivativeTrace0
import BFGS.Counterexample.Certificates.DerivativeTrace1
import BFGS.Counterexample.Certificates.DerivativeTrace2
import BFGS.Counterexample.Certificates.DerivativeTrace3
import BFGS.Counterexample.PhaseDynamics

/-! Exact identification of the certified five-dimensional Jacobian with
the derivative of the actual four unit BFGS steps. -/
namespace BFGS.Counterexample
noncomputable section
open BFGS.Algorithm Trace CycleDynamics
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.cons_val_four Matrix.vecHead Matrix.vecTail

theorem traceJacobian_column (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0)
    (i : Fin 4) (j : Fin 5) :
    expandedStep (traceMetric b i.castSucc) (traceGradient b i.castSucc)
      (traceGradient b i.succ) (symmetricMap (traceHessian b i.castSucc))
      (symmetricMap (traceHessian b i.succ)) (Pi.single j 1) =
      fun k => traceJacobian b i k j := by
  fin_cases i <;> fin_cases j
  · change expandedStep (traceMetric b 0) (traceGradient b 0)
      (traceGradient b 1) (symmetricMap (traceHessian b 0))
      (symmetricMap (traceHessian b 1)) (Pi.single (0:Fin 5) 1) =
      fun k => traceJacobian b 0 k 0
    have he := jacobian0_column0 b hb hp
    have hv : (Pi.single (0:Fin 5) 1 : State) = ![1,0,0,0,0] := by
      ext k
      fin_cases k <;> norm_num [Pi.single_apply,Fin.ext_iff]
    rw [hv]
    refine he.trans ?_
    ext k
    fin_cases k <;> rfl
  · change expandedStep (traceMetric b 0) (traceGradient b 0)
      (traceGradient b 1) (symmetricMap (traceHessian b 0))
      (symmetricMap (traceHessian b 1)) (Pi.single (1:Fin 5) 1) =
      fun k => traceJacobian b 0 k 1
    have he := jacobian0_column1 b hb hp
    have hv : (Pi.single (1:Fin 5) 1 : State) = ![0,1,0,0,0] := by
      ext k
      fin_cases k <;> norm_num [Pi.single_apply,Fin.ext_iff]
    rw [hv]
    refine he.trans ?_
    ext k
    fin_cases k <;> rfl
  · change expandedStep (traceMetric b 0) (traceGradient b 0)
      (traceGradient b 1) (symmetricMap (traceHessian b 0))
      (symmetricMap (traceHessian b 1)) (Pi.single (2:Fin 5) 1) =
      fun k => traceJacobian b 0 k 2
    have he := jacobian0_column2 b hb hp
    have hv : (Pi.single (2:Fin 5) 1 : State) = ![0,0,1,0,0] := by
      ext k
      fin_cases k <;> norm_num [Pi.single_apply,Fin.ext_iff]
    rw [hv]
    refine he.trans ?_
    ext k
    fin_cases k <;> rfl
  · change expandedStep (traceMetric b 0) (traceGradient b 0)
      (traceGradient b 1) (symmetricMap (traceHessian b 0))
      (symmetricMap (traceHessian b 1)) (Pi.single (3:Fin 5) 1) =
      fun k => traceJacobian b 0 k 3
    have he := jacobian0_column3 b hb hp
    have hv : (Pi.single (3:Fin 5) 1 : State) = ![0,0,0,1,0] := by
      ext k
      fin_cases k <;> norm_num [Pi.single_apply,Fin.ext_iff]
    rw [hv]
    refine he.trans ?_
    ext k
    fin_cases k <;> rfl
  · change expandedStep (traceMetric b 0) (traceGradient b 0)
      (traceGradient b 1) (symmetricMap (traceHessian b 0))
      (symmetricMap (traceHessian b 1)) (Pi.single (4:Fin 5) 1) =
      fun k => traceJacobian b 0 k 4
    have he := jacobian0_column4 b hb hp
    have hv : (Pi.single (4:Fin 5) 1 : State) = ![0,0,0,0,1] := by
      ext k
      fin_cases k <;> norm_num [Pi.single_apply,Fin.ext_iff]
    rw [hv]
    refine he.trans ?_
    ext k
    fin_cases k <;> rfl
  · change expandedStep (traceMetric b 1) (traceGradient b 1)
      (traceGradient b 2) (symmetricMap (traceHessian b 1))
      (symmetricMap (traceHessian b 2)) (Pi.single (0:Fin 5) 1) =
      fun k => traceJacobian b 1 k 0
    have he := jacobian1_column0 b hb hp
    have hv : (Pi.single (0:Fin 5) 1 : State) = ![1,0,0,0,0] := by
      ext k
      fin_cases k <;> norm_num [Pi.single_apply,Fin.ext_iff]
    rw [hv]
    refine he.trans ?_
    ext k
    fin_cases k <;> rfl
  · change expandedStep (traceMetric b 1) (traceGradient b 1)
      (traceGradient b 2) (symmetricMap (traceHessian b 1))
      (symmetricMap (traceHessian b 2)) (Pi.single (1:Fin 5) 1) =
      fun k => traceJacobian b 1 k 1
    have he := jacobian1_column1 b hb hp
    have hv : (Pi.single (1:Fin 5) 1 : State) = ![0,1,0,0,0] := by
      ext k
      fin_cases k <;> norm_num [Pi.single_apply,Fin.ext_iff]
    rw [hv]
    refine he.trans ?_
    ext k
    fin_cases k <;> rfl
  · change expandedStep (traceMetric b 1) (traceGradient b 1)
      (traceGradient b 2) (symmetricMap (traceHessian b 1))
      (symmetricMap (traceHessian b 2)) (Pi.single (2:Fin 5) 1) =
      fun k => traceJacobian b 1 k 2
    have he := jacobian1_column2 b hb hp
    have hv : (Pi.single (2:Fin 5) 1 : State) = ![0,0,1,0,0] := by
      ext k
      fin_cases k <;> norm_num [Pi.single_apply,Fin.ext_iff]
    rw [hv]
    refine he.trans ?_
    ext k
    fin_cases k <;> rfl
  · change expandedStep (traceMetric b 1) (traceGradient b 1)
      (traceGradient b 2) (symmetricMap (traceHessian b 1))
      (symmetricMap (traceHessian b 2)) (Pi.single (3:Fin 5) 1) =
      fun k => traceJacobian b 1 k 3
    have he := jacobian1_column3 b hb hp
    have hv : (Pi.single (3:Fin 5) 1 : State) = ![0,0,0,1,0] := by
      ext k
      fin_cases k <;> norm_num [Pi.single_apply,Fin.ext_iff]
    rw [hv]
    refine he.trans ?_
    ext k
    fin_cases k <;> rfl
  · change expandedStep (traceMetric b 1) (traceGradient b 1)
      (traceGradient b 2) (symmetricMap (traceHessian b 1))
      (symmetricMap (traceHessian b 2)) (Pi.single (4:Fin 5) 1) =
      fun k => traceJacobian b 1 k 4
    have he := jacobian1_column4 b hb hp
    have hv : (Pi.single (4:Fin 5) 1 : State) = ![0,0,0,0,1] := by
      ext k
      fin_cases k <;> norm_num [Pi.single_apply,Fin.ext_iff]
    rw [hv]
    refine he.trans ?_
    ext k
    fin_cases k <;> rfl
  · change expandedStep (traceMetric b 2) (traceGradient b 2)
      (traceGradient b 3) (symmetricMap (traceHessian b 2))
      (symmetricMap (traceHessian b 3)) (Pi.single (0:Fin 5) 1) =
      fun k => traceJacobian b 2 k 0
    have he := jacobian2_column0 b hb hp
    have hv : (Pi.single (0:Fin 5) 1 : State) = ![1,0,0,0,0] := by
      ext k
      fin_cases k <;> norm_num [Pi.single_apply,Fin.ext_iff]
    rw [hv]
    refine he.trans ?_
    ext k
    fin_cases k <;> rfl
  · change expandedStep (traceMetric b 2) (traceGradient b 2)
      (traceGradient b 3) (symmetricMap (traceHessian b 2))
      (symmetricMap (traceHessian b 3)) (Pi.single (1:Fin 5) 1) =
      fun k => traceJacobian b 2 k 1
    have he := jacobian2_column1 b hb hp
    have hv : (Pi.single (1:Fin 5) 1 : State) = ![0,1,0,0,0] := by
      ext k
      fin_cases k <;> norm_num [Pi.single_apply,Fin.ext_iff]
    rw [hv]
    refine he.trans ?_
    ext k
    fin_cases k <;> rfl
  · change expandedStep (traceMetric b 2) (traceGradient b 2)
      (traceGradient b 3) (symmetricMap (traceHessian b 2))
      (symmetricMap (traceHessian b 3)) (Pi.single (2:Fin 5) 1) =
      fun k => traceJacobian b 2 k 2
    have he := jacobian2_column2 b hb hp
    have hv : (Pi.single (2:Fin 5) 1 : State) = ![0,0,1,0,0] := by
      ext k
      fin_cases k <;> norm_num [Pi.single_apply,Fin.ext_iff]
    rw [hv]
    refine he.trans ?_
    ext k
    fin_cases k <;> rfl
  · change expandedStep (traceMetric b 2) (traceGradient b 2)
      (traceGradient b 3) (symmetricMap (traceHessian b 2))
      (symmetricMap (traceHessian b 3)) (Pi.single (3:Fin 5) 1) =
      fun k => traceJacobian b 2 k 3
    have he := jacobian2_column3 b hb hp
    have hv : (Pi.single (3:Fin 5) 1 : State) = ![0,0,0,1,0] := by
      ext k
      fin_cases k <;> norm_num [Pi.single_apply,Fin.ext_iff]
    rw [hv]
    refine he.trans ?_
    ext k
    fin_cases k <;> rfl
  · change expandedStep (traceMetric b 2) (traceGradient b 2)
      (traceGradient b 3) (symmetricMap (traceHessian b 2))
      (symmetricMap (traceHessian b 3)) (Pi.single (4:Fin 5) 1) =
      fun k => traceJacobian b 2 k 4
    have he := jacobian2_column4 b hb hp
    have hv : (Pi.single (4:Fin 5) 1 : State) = ![0,0,0,0,1] := by
      ext k
      fin_cases k <;> norm_num [Pi.single_apply,Fin.ext_iff]
    rw [hv]
    refine he.trans ?_
    ext k
    fin_cases k <;> rfl
  · change expandedStep (traceMetric b 3) (traceGradient b 3)
      (traceGradient b 4) (symmetricMap (traceHessian b 3))
      (symmetricMap (traceHessian b 4)) (Pi.single (0:Fin 5) 1) =
      fun k => traceJacobian b 3 k 0
    have he := jacobian3_column0 b hb hp
    have hv : (Pi.single (0:Fin 5) 1 : State) = ![1,0,0,0,0] := by
      ext k
      fin_cases k <;> norm_num [Pi.single_apply,Fin.ext_iff]
    rw [hv]
    refine he.trans ?_
    ext k
    fin_cases k <;> rfl
  · change expandedStep (traceMetric b 3) (traceGradient b 3)
      (traceGradient b 4) (symmetricMap (traceHessian b 3))
      (symmetricMap (traceHessian b 4)) (Pi.single (1:Fin 5) 1) =
      fun k => traceJacobian b 3 k 1
    have he := jacobian3_column1 b hb hp
    have hv : (Pi.single (1:Fin 5) 1 : State) = ![0,1,0,0,0] := by
      ext k
      fin_cases k <;> norm_num [Pi.single_apply,Fin.ext_iff]
    rw [hv]
    refine he.trans ?_
    ext k
    fin_cases k <;> rfl
  · change expandedStep (traceMetric b 3) (traceGradient b 3)
      (traceGradient b 4) (symmetricMap (traceHessian b 3))
      (symmetricMap (traceHessian b 4)) (Pi.single (2:Fin 5) 1) =
      fun k => traceJacobian b 3 k 2
    have he := jacobian3_column2 b hb hp
    have hv : (Pi.single (2:Fin 5) 1 : State) = ![0,0,1,0,0] := by
      ext k
      fin_cases k <;> norm_num [Pi.single_apply,Fin.ext_iff]
    rw [hv]
    refine he.trans ?_
    ext k
    fin_cases k <;> rfl
  · change expandedStep (traceMetric b 3) (traceGradient b 3)
      (traceGradient b 4) (symmetricMap (traceHessian b 3))
      (symmetricMap (traceHessian b 4)) (Pi.single (3:Fin 5) 1) =
      fun k => traceJacobian b 3 k 3
    have he := jacobian3_column3 b hb hp
    have hv : (Pi.single (3:Fin 5) 1 : State) = ![0,0,0,1,0] := by
      ext k
      fin_cases k <;> norm_num [Pi.single_apply,Fin.ext_iff]
    rw [hv]
    refine he.trans ?_
    ext k
    fin_cases k <;> rfl
  · change expandedStep (traceMetric b 3) (traceGradient b 3)
      (traceGradient b 4) (symmetricMap (traceHessian b 3))
      (symmetricMap (traceHessian b 4)) (Pi.single (4:Fin 5) 1) =
      fun k => traceJacobian b 3 k 4
    have he := jacobian3_column4 b hb hp
    have hv : (Pi.single (4:Fin 5) 1 : State) = ![0,0,0,0,1] := by
      ext k
      fin_cases k <;> norm_num [Pi.single_apply,Fin.ext_iff]
    rw [hv]
    refine he.trans ?_
    ext k
    fin_cases k <;> rfl

/-- Local Jacobians of the genuine unit BFGS map, with no derivative assumed
beyond the prescribed gradient derivatives at the two endpoints. -/
theorem cycleStep_hasFDerivAt_trace (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0)
    (G : Vec → Vec)
    (hgradient : ∀ i : Fin 5, G (phasePoint b i) = phaseGradient b i)
    (hhessian : ∀ i : Fin 5,
      HasFDerivAt G (symmetricMap (phaseHessian b i)) (phasePoint b i)) (i : Fin 4) :
    HasFDerivAt (cycleStep G) (matrixLinearMap (traceJacobian b i))
      (PhaseDynamics.state b i.castSucc) := by
  have h0 : HasFDerivAt G (symmetricMap (phaseHessian b i.castSucc))
      (point (PhaseDynamics.state b i.castSucc)) := by
    simpa [PhaseDynamics.state] using hhessian i.castSucc
  have h1 : HasFDerivAt G (symmetricMap (phaseHessian b i.succ))
      (point (PhaseDynamics.state b i.castSucc)+direction G (PhaseDynamics.state b i.castSucc)) := by
    rw [PhaseDynamics.state_next_point b hb hp G hgradient i]
    exact hhessian i.succ
  obtain ⟨L,hL,hδ⟩ := expandedStep_is_derivative G (PhaseDynamics.state b i.castSucc)
    _ _ h0 h1 (PhaseDynamics.state_curvature_ne b hb hp G hgradient i)
  have hLmat : L = matrixLinearMap (traceJacobian b i) := by
    apply matrixLinearMap_eq_of_basis
    intro j
    rw [hδ,PhaseDynamics.state_next_point b hb hp G hgradient i]
    simp only [PhaseDynamics.state,point_pack,metric_pack,hgradient]
    rw [← traceMetric_eq b hb hp,← traceGradient_eq b hb hp,← traceHessian_eq b hb hp]
    exact traceJacobian_column b hb hp i j
  rw [hLmat] at hL
  exact hL

/-- The unscaled derivative of the four unit BFGS steps. -/
def traceFullDifferential (b : ℝ) : State →L[ℝ] State :=
  matrixLinearMap (traceJacobian b 3 *
    (traceJacobian b 2 * (traceJacobian b 1 * traceJacobian b 0)))

theorem traceFullDifferential_eq (b : ℝ) :
    traceFullDifferential b = matrixLinearMap (r • traceReturnDerivative b) := by
  rw [traceReturnDerivative_eq,smul_smul]
  norm_num [r,traceFullDifferential]

/-- The returned numeric matrix is the genuine four-step derivative divided
by the cycle contraction factor r. -/
theorem four_cycleSteps_hasFDerivAt_trace (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0)
    (G : Vec → Vec)
    (hgradient : ∀ i : Fin 5, G (phasePoint b i) = phaseGradient b i)
    (hhessian : ∀ i : Fin 5,
      HasFDerivAt G (symmetricMap (phaseHessian b i)) (phasePoint b i)) :
    HasFDerivAt ((cycleStep G)^[4]) (traceFullDifferential b) (PhaseDynamics.state b 0) := by
  let T := cycleStep G
  let L := fun i : Fin 4 => matrixLinearMap (traceJacobian b i)
  have h0 : HasFDerivAt T (L 0) (PhaseDynamics.state b 0) :=
    cycleStep_hasFDerivAt_trace b hb hp G hgradient hhessian 0
  have h1 : HasFDerivAt T (L 1) (T (PhaseDynamics.state b 0)) := by
    rw [show T (PhaseDynamics.state b 0) = PhaseDynamics.state b 1 from
      PhaseDynamics.state_cycleStep b hb hp G hgradient 0]
    exact cycleStep_hasFDerivAt_trace b hb hp G hgradient hhessian 1
  have h2 : HasFDerivAt T (L 2) ((T ∘ T) (PhaseDynamics.state b 0)) := by
    change HasFDerivAt T (L 2) (T (T (PhaseDynamics.state b 0)))
    rw [show T (PhaseDynamics.state b 0) = PhaseDynamics.state b 1 from
      PhaseDynamics.state_cycleStep b hb hp G hgradient 0,
      show T (PhaseDynamics.state b 1) = PhaseDynamics.state b 2 from
      PhaseDynamics.state_cycleStep b hb hp G hgradient 1]
    exact cycleStep_hasFDerivAt_trace b hb hp G hgradient hhessian 2
  have h3 : HasFDerivAt T (L 3) ((T ∘ (T ∘ T)) (PhaseDynamics.state b 0)) := by
    change HasFDerivAt T (L 3) (T (T (T (PhaseDynamics.state b 0))))
    rw [show T (PhaseDynamics.state b 0) = PhaseDynamics.state b 1 from
      PhaseDynamics.state_cycleStep b hb hp G hgradient 0,
      show T (PhaseDynamics.state b 1) = PhaseDynamics.state b 2 from
      PhaseDynamics.state_cycleStep b hb hp G hgradient 1,
      show T (PhaseDynamics.state b 2) = PhaseDynamics.state b 3 from
      PhaseDynamics.state_cycleStep b hb hp G hgradient 2]
    exact cycleStep_hasFDerivAt_trace b hb hp G hgradient hhessian 3
  have h := h3.comp (PhaseDynamics.state b 0)
    (h2.comp (PhaseDynamics.state b 0) (h1.comp (PhaseDynamics.state b 0) h0))
  dsimp [L] at h
  rw [matrixLinearMap_comp,matrixLinearMap_comp,matrixLinearMap_comp] at h
  simpa [T,traceFullDifferential,Function.comp_def,Function.iterate_succ_apply'] using h

end
end BFGS.Counterexample
