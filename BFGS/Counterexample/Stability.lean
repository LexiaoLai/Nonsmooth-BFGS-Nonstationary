import BFGS.Counterexample.Derivative
import BFGS.Counterexample.Certificates.IntervalBounds
import BFGS.Counterexample.ReturnBridge
import BFGS.Counterexample.StateCoordinates
import BFGS.Analysis.FixedScale
import BFGS.Analysis.RayAttraction

/-! Proposition A.1 and Lemma 2.12.
The return map is `r⁻¹ T⁴` on the full state space, exactly as in the paper.
The matrix bound controls displacement from its positive ray of fixed points. -/
namespace BFGS.Counterexample.Stability
noncomputable section
open BFGS.Algorithm BFGS.StateSpace CycleDynamics Filter Topology
set_option maxHeartbeats 0

/-- The manuscript's invertible transverse coordinate matrix `S`. -/
def coordinates : TransverseSpace ≃L[ℝ] TransverseSpace :=
  matrixCoordinates transverseConjugator transverseConjugatorInv
    transverseConjugator_right_inverse transverseConjugator_left_inverse

/-- The cycle state `ω_*`. -/
def baseState : State := embed PhaseDynamics.center

/-- Equation (2.26): the full state is divided by the fixed
cycle factor `r`, never by one of its coordinates. -/
def fixedReturn : State → State := FixedScale.returnMap (cycleStep Realization.g) 4 r

/-- Linear coordinates `(ω₃, S R(ω − ω₃ω_*))`. -/
def stateCoordinates : State ≃L[ℝ] ℝ × TransverseSpace :=
  weightedStateCoordinates PhaseDynamics.center coordinates

/-- The same return map in the preceding linear coordinates. -/
def rayMap (z : ℝ × TransverseSpace) : ℝ × TransverseSpace :=
  stateCoordinates (fixedReturn (stateCoordinates.symm z))

theorem fixedReturn_fixed : fixedReturn baseState = baseState :=
  FixedScale.returnMap_fixed _ _ _ r_pos.ne' _ PhaseDynamics.actual_cycle

theorem fixedReturn_homogeneous (t : ℝ) (ht : 0 ≤ t) (z : State) :
    fixedReturn (t • z) = t • fixedReturn z :=
  FixedScale.returnMap_posHomogeneous _ _ _
    (acceptedStep_posHomogeneous _ _ Realization.g_scale) t ht z

theorem rayMap_fixed : rayMap (1,0) = (1,0) := by
  have he : stateCoordinates baseState = (1,0) := weightedStateCoordinates_base _ _
  rw [rayMap,← he,stateCoordinates.symm_apply_apply,fixedReturn_fixed]

theorem rayMap_homogeneous (t : ℝ) (ht : 0 < t) (z : ℝ × TransverseSpace) :
    rayMap (t • z) = t • rayMap z := by
  simp only [rayMap,map_smul,fixedReturn_homogeneous t ht.le]

/-- The certified five-dimensional derivative is `D(r⁻¹ T⁴)(ω_*)`. -/
theorem fixedReturn_hasFDerivAt :
    HasFDerivAt fixedReturn (matrixLinearMap (traceReturnDerivative root)) baseState := by
  have h := four_cycleSteps_hasFDerivAt_trace root root_half_lt root_quartic
    Realization.g Realization.g_phase_all Realization.g_hasFDerivAt_phase_all
  rw [← PhaseDynamics.embed_center] at h
  have hs := h.const_smul r⁻¹
  rw [traceFullDifferential_eq,matrixLinearMap_smul,smul_smul,inv_mul_cancel₀ r_pos.ne',one_smul] at hs
  exact hs

/-- `R(ω − ω₃ω_*)`, viewed as a linear map. -/
def transverseProjection : State →L[ℝ] TransverseSpace :=
  ContinuousLinearMap.pi fun i =>
    ContinuousLinearMap.proj (keep i) - PhaseDynamics.center i • ContinuousLinearMap.proj 2

@[simp] theorem transverseProjection_apply (z : State) (i : Fin 4) :
    transverseProjection z i = z (keep i)-PhaseDynamics.center i*z 2 := rfl

theorem stateCoordinates_second (z : State) :
    (stateCoordinates z).2 = coordinates (transverseProjection z) := by
  change coordinates (fun i => z (keep i)-z 2*PhaseDynamics.center i) =
    coordinates (transverseProjection z)
  congr 1
  funext i
  change z (keep i)-z 2*PhaseDynamics.center i =
    z (keep i)-PhaseDynamics.center i*z 2
  ring

theorem projected_derivative :
    transverseProjection.comp ((matrixLinearMap (traceReturnDerivative root)).comp
      embedDifferential) = matrixLinearMap (traceTransverse root) := by
  apply matrixLinearMap_eq_of_basis
  intro j
  funext i
  rw [ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply,embedDifferential_basis]
  simp only [transverseProjection_apply,matrixLinearMap_apply,Matrix.mulVec_single,
    MulOpposite.op_one,one_smul,Matrix.col_apply]
  have hc : traceBaseState root (keep i) = PhaseDynamics.center i := by
    rw [traceBaseState_eq root root_half_lt root_quartic]
    change PhaseDynamics.state root 0 (keep i) = PhaseDynamics.center i
    rw [← PhaseDynamics.embed_center,embed_keep]
  change traceReturnDerivative root (keep i) (keep j) -
    PhaseDynamics.center i*traceReturnDerivative root 2 (keep j) = _
  simp only [traceTransverse,show transverseKeep = keep from rfl,hc]

def contractionDerivative : TransverseSpace →L[ℝ] TransverseSpace :=
  matrixLinearMap (Trace.conjugatedTransverse root)

theorem conjugated_matrix_eq :
    transverseConjugator * traceTransverse root * transverseConjugatorInv =
      Trace.conjugatedTransverse root := by
  rw [← traceConjugatedTransverse_eq]
  rfl

theorem contractionDerivative_norm : ‖contractionDerivative‖ ≤ (78:ℝ)/100 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro v
  exact Trace.root_conjugated_mulVec_bound v

/-- The transverse slice derivative is the certified matrix `S A S⁻¹`. -/
theorem transverse_slice_hasFDerivAt :
    HasFDerivAt (fun u : TransverseSpace => (rayMap (1,u)).2) contractionDerivative 0 := by
  let E := embedDifferential.comp coordinates.symm.toContinuousLinearMap
  have hinner : HasFDerivAt (fun u : TransverseSpace => baseState+E u) E 0 := by
    simpa using (hasFDerivAt_const baseState (0 : TransverseSpace)).add E.hasFDerivAt
  have hF : HasFDerivAt fixedReturn (matrixLinearMap (traceReturnDerivative root))
      (baseState+E 0) := by simpa using fixedReturn_hasFDerivAt
  have h := coordinates.toContinuousLinearMap.hasFDerivAt.comp 0
    (transverseProjection.hasFDerivAt.comp 0 (hF.comp 0 hinner))
  change HasFDerivAt (fun u => coordinates (transverseProjection (fixedReturn (baseState+E u))))
    (coordinates.toContinuousLinearMap.comp (transverseProjection.comp
      ((matrixLinearMap (traceReturnDerivative root)).comp E))) 0 at h
  have he : coordinates.toContinuousLinearMap.comp (transverseProjection.comp
      ((matrixLinearMap (traceReturnDerivative root)).comp E)) = contractionDerivative := by
    change coordinates.toContinuousLinearMap.comp
      ((transverseProjection.comp ((matrixLinearMap (traceReturnDerivative root)).comp
        embedDifferential)).comp coordinates.symm.toContinuousLinearMap) = contractionDerivative
    rw [projected_derivative]
    change (matrixLinearMap transverseConjugator).comp
      ((matrixLinearMap (traceTransverse root)).comp (matrixLinearMap transverseConjugatorInv)) = _
    rw [matrixLinearMap_comp,matrixLinearMap_comp,← Matrix.mul_assoc,conjugated_matrix_eq]
    rfl
  rw [he] at h
  convert h using 1
  funext u
  rw [rayMap,stateCoordinates_second]
  congr 3
  change (weightedStateCoordinates PhaseDynamics.center coordinates).symm (1,u) = _
  simp [weightedStateCoordinates_symm_apply,baseState,E]

theorem scalar_slice_differentiable :
    DifferentiableAt ℝ (fun u : TransverseSpace => (rayMap (1,u)).1) 0 := by
  have hin : DifferentiableAt ℝ (fun u : TransverseSpace => ((1 : ℝ),u)) 0 := by fun_prop
  have hinner := stateCoordinates.symm.differentiableAt.comp (0 : TransverseSpace) hin
  have hbase : stateCoordinates.symm (1,0) = baseState := by
    apply stateCoordinates.injective
    simp [stateCoordinates,baseState]
  have hF : DifferentiableAt ℝ fixedReturn (stateCoordinates.symm (1,0)) := by
    rw [hbase]
    exact fixedReturn_hasFDerivAt.differentiableAt
  exact (stateCoordinates.differentiableAt.comp (0 : TransverseSpace) (hF.comp 0 hinner)).fst

/-- Lemma 2.12: arbitrarily small invariant neighborhoods
of the cycle state, with convergence to its positive fixed ray. -/
theorem fixed_ray_neighborhood (O : Set State) (hO : O ∈ 𝓝 baseState) :
    ∃ U : Set State, IsOpen U ∧ baseState ∈ U ∧ U ⊆ O ∧
      Set.MapsTo fixedReturn U U ∧
      ∀ z ∈ U, ∃ a : ℝ, 0 < a ∧ Tendsto (fun j => fixedReturn^[j] z) atTop (𝓝 (a • baseState)) := by
  let V := stateCoordinates.symm ⁻¹' O
  have hV : V ∈ 𝓝 ((1 : ℝ),(0 : TransverseSpace)) := by
    have he : stateCoordinates.symm (1,0) = baseState := by
      apply stateCoordinates.injective
      simp [stateCoordinates,baseState]
    exact stateCoordinates.symm.continuous.continuousAt.preimage_mem_nhds (by simpa [he] using hO)
  obtain ⟨W,hWo,hWc,hWV,hmap,hconv⟩ :=
    BFGS.Analysis.exists_open_fixed_ray_neighborhood rayMap contractionDerivative rayMap_fixed
      rayMap_homogeneous transverse_slice_hasFDerivAt scalar_slice_differentiable
      (lt_of_le_of_lt contractionDerivative_norm (by norm_num)) V hV
  let U := stateCoordinates ⁻¹' W
  refine ⟨U,hWo.preimage stateCoordinates.continuous,?_,?_,?_,?_⟩
  · change stateCoordinates baseState ∈ W
    rw [show stateCoordinates baseState = (1,0) from weightedStateCoordinates_base _ _]
    exact hWc
  · intro z hz
    have h := hWV hz
    simpa [V] using h
  · intro z hz
    have h := hmap hz
    simpa [U,rayMap] using h
  · intro z hz
    obtain ⟨a,ha,hlim⟩ := hconv (stateCoordinates z) hz
    refine ⟨a,ha,?_⟩
    have h := stateCoordinates.symm.continuous.continuousAt.tendsto.comp hlim
    have hiter (j : ℕ) : stateCoordinates.symm (rayMap^[j] (stateCoordinates z)) = fixedReturn^[j] z := by
      induction j with
      | zero => simp
      | succ j ih => simpa [Function.iterate_succ_apply',rayMap] using congrArg fixedReturn ih
    have htarget : stateCoordinates.symm (a,0) = a • baseState := by
      simp [stateCoordinates,weightedStateCoordinates_symm_apply,baseState]
    change Tendsto (fun j => stateCoordinates.symm (rayMap^[j] (stateCoordinates z)))
      atTop (𝓝 (stateCoordinates.symm (a,0))) at h
    simpa only [hiter,htarget] using h

/-- Finite smoothness and search conditions hold on the invariant neighborhood
used for Theorem 1.1. The neighborhood consists of full states. -/
theorem invariant_basin :
    ∃ U : Set State, IsOpen U ∧ baseState ∈ U ∧
      Set.MapsTo fixedReturn U U ∧
      (∀ w ∈ U, ∀ i : Fin 4,
        PhaseSafe Realization.f Realization.g (3/100) (3/5)
          PhaseDynamics.smoothSet 4 ((cycleStep Realization.g)^[i.val] w)) ∧
      ∃ M : ℝ, 0 ≤ M ∧ ∀ w ∈ U, ∀ i : Fin 4,
        ‖(cycleStep Realization.g)^[i.val] w‖ ≤ M := by
  let T := cycleStep Realization.g
  have hT : ∀ k < 4, ContinuousAt T (T^[k] baseState) := by
    intro k hk
    exact (cycleStep_differentiableAt_of_certificate Realization.f Realization.g
      (3/100) (3/5) PhaseDynamics.smoothSet 4 _ PhaseDynamics.actual_g_differentiable
      (PhaseDynamics.actual_iterate_certificates ⟨k,hk⟩)).continuousAt
  have hphase (i : Fin 4) : ContinuousAt (T^[i.val]) baseState :=
    LocalCycle.iterate_continuousAt_bounded T baseState i.val
      (fun k hk => hT k (Nat.lt_trans hk i.isLt))
  have hsafe (i : Fin 4) : ∀ᶠ w in 𝓝 baseState,
      PhaseSafe Realization.f Realization.g (3/100) (3/5)
        PhaseDynamics.smoothSet 4 (T^[i.val] w) :=
    (hphase i).eventually (phaseSafe_eventually Realization.f Realization.g
      (3/100) (3/5) PhaseDynamics.smoothSet 4 _ Realization.f_continuous
      PhaseDynamics.smoothSet_open PhaseDynamics.actual_g_differentiable
      (PhaseDynamics.actual_iterate_certificates i))
  let M := (∑ i : Fin 4, ‖T^[i.val] baseState‖)+1
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hb (i : Fin 4) : ‖T^[i.val] baseState‖ < M := by
    have h := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 4))) =>
      norm_nonneg (T^[j.val] baseState)) (Finset.mem_univ i)
    dsimp [M]
    linarith
  let O := {w : State | (∀ i : Fin 4, PhaseSafe Realization.f Realization.g
    (3/100) (3/5) PhaseDynamics.smoothSet 4 (T^[i.val] w)) ∧
      (∀ i : Fin 4, ‖T^[i.val] w‖ < M)}
  have hO : O ∈ 𝓝 baseState :=
    (Filter.eventually_all.mpr hsafe).and (Filter.eventually_all.mpr
      (fun i => (hphase i).norm.eventually_lt_const (hb i)))
  obtain ⟨U,hUo,hUc,hsub,hmap,_⟩ := fixed_ray_neighborhood O hO
  exact ⟨U,hUo,hUc,hmap,(fun w hw => (hsub hw).1),M,hM,
    (fun w hw i => ((hsub hw).2 i).le)⟩

end
end BFGS.Counterexample.Stability
