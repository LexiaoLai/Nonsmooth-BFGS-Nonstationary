import BFGS.Counterexample.DerivativeCore

namespace BFGS.Counterexample
noncomputable section
open BFGS.Algorithm

def matrixLinearMap {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.toLin' A)

@[simp] theorem matrixLinearMap_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (v : Fin n → ℝ) : matrixLinearMap A v = A.mulVec v := rfl

theorem matrixLinearMap_comp {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) :
    (matrixLinearMap A).comp (matrixLinearMap B) = matrixLinearMap (A*B) := by
  ext v i
  simp only [ContinuousLinearMap.comp_apply,matrixLinearMap_apply,Matrix.mulVec_mulVec]

theorem matrixLinearMap_smul {n : ℕ} (a : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    matrixLinearMap (a • A) = a • matrixLinearMap A := by
  ext v i
  simp [matrixLinearMap_apply,Matrix.mulVec, dotProduct, Finset.mul_sum,mul_assoc]

theorem matrixLinearMap_eq_of_basis {n : ℕ} (L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (A : Matrix (Fin n) (Fin n) ℝ)
    (h : ∀ j, L (Pi.single j 1) = fun i => A i j) : L = matrixLinearMap A := by
  apply ContinuousLinearMap.coe_injective
  apply (Pi.basisFun ℝ (Fin n)).ext
  intro j
  change L ((Pi.basisFun ℝ (Fin n)) j) = matrixLinearMap A ((Pi.basisFun ℝ (Fin n)) j)
  rw [Pi.basisFun_apply,h,matrixLinearMap_apply,Matrix.mulVec_single]
  simp [Matrix.col,Matrix.transpose,Matrix.of]
  rfl

end
end BFGS.Counterexample
