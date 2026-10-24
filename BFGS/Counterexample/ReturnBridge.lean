import BFGS.Counterexample.DerivativeLinear
import BFGS.Analysis.StateSpace

/-! Invertible linear coordinates for the finite matrix certificate. -/
namespace BFGS.Counterexample
noncomputable section
open BFGS.Algorithm BFGS.StateSpace

def matrixCoordinates (S V : Matrix (Fin 4) (Fin 4) ℝ)
    (hleft : V*S = 1) (hright : S*V = 1) : TransverseSpace ≃L[ℝ] TransverseSpace :=
  LinearEquiv.toContinuousLinearEquiv
    { Matrix.mulVecLin S with
      invFun := V.mulVec
      left_inv := by
        intro v
        change V.mulVec (S.mulVec v) = v
        rw [Matrix.mulVec_mulVec,hleft,Matrix.one_mulVec]
      right_inv := by
        intro v
        change S.mulVec (V.mulVec v) = v
        rw [Matrix.mulVec_mulVec,hright,Matrix.one_mulVec] }

@[simp] theorem matrixCoordinates_clm (S V : Matrix (Fin 4) (Fin 4) ℝ)
    (hleft : V*S = 1) (hright : S*V = 1) :
    (matrixCoordinates S V hleft hright).toContinuousLinearMap = matrixLinearMap S := rfl

@[simp] theorem matrixCoordinates_symm_clm (S V : Matrix (Fin 4) (Fin 4) ℝ)
    (hleft : V*S = 1) (hright : S*V = 1) :
    (matrixCoordinates S V hleft hright).symm.toContinuousLinearMap = matrixLinearMap V := rfl

end
end BFGS.Counterexample
