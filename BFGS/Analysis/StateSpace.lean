import BFGS.Analysis.Iteration

/-! Static state coordinates: delete the third coordinate, or insert a fixed
third coordinate or a zero. No state-dependent normalization is used. -/
namespace BFGS.StateSpace
noncomputable section
open Algorithm
abbrev TransverseSpace := Fin 4 → ℝ

def keep : Fin 4 → Fin 5 := ![0,1,3,4]
def embed (y : TransverseSpace) : State := ![y 0,y 1,1,y 2,y 3]
def embedDifferential : TransverseSpace →L[ℝ] State :=
  ContinuousLinearMap.pi ![ContinuousLinearMap.proj 0,ContinuousLinearMap.proj 1,
    0,ContinuousLinearMap.proj 2,ContinuousLinearMap.proj 3]

theorem embed_hasFDerivAt (y : TransverseSpace) : HasFDerivAt embed embedDifferential y := by
  apply hasFDerivAt_pi.2
  intro i
  fin_cases i
  · exact hasFDerivAt_apply 0 y
  · exact hasFDerivAt_apply 1 y
  · exact hasFDerivAt_const 1 y
  · exact hasFDerivAt_apply 2 y
  · exact hasFDerivAt_apply 3 y

@[simp] theorem embed_two (y : TransverseSpace) : embed y 2 = 1 := rfl
@[simp] theorem embed_keep (y : TransverseSpace) (i : Fin 4) : embed y (keep i) = y i := by
  fin_cases i <;> rfl
theorem embedDifferential_basis (j : Fin 4) :
    embedDifferential (Pi.single j 1) = Pi.single (keep j) 1 := by
  ext i
  fin_cases j <;> fin_cases i <;> simp [embedDifferential,keep]

end
end BFGS.StateSpace
