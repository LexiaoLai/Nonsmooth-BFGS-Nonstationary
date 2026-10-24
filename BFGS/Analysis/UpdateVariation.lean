import BFGS.Analysis.UpdateDifferential

/-! The explicit directional arithmetic of the actual accepted BFGS step. -/
namespace BFGS.Algorithm.Variation
noncomputable section

@[ext] structure Dual where
  value : ℝ
  tangent : ℝ

namespace Dual
def constant (a : ℝ) : Dual := ⟨a,0⟩
def add (a b : Dual) : Dual := ⟨a.value+b.value,a.tangent+b.tangent⟩
def neg (a : Dual) : Dual := ⟨-a.value,-a.tangent⟩
def sub (a b : Dual) : Dual := add a (neg b)
def mul (a b : Dual) : Dual :=
  ⟨a.value*b.value,a.tangent*b.value+a.value*b.tangent⟩
def inv (a : Dual) : Dual :=
  ⟨1/a.value,-(1/a.value)*(1/a.value)*a.tangent⟩
def div (a b : Dual) : Dual := mul a (inv b)
end Dual

abbrev Pair := Dual × Dual
@[ext] structure Matrix where
  a : Dual
  b : Dual
  d : Dual

def pairOf (x dx : Vec) : Pair := (⟨x.1,dx.1⟩,⟨x.2,dx.2⟩)
def matrixOf (H dH : Sym2) : Matrix :=
  ⟨⟨H.a,dH.a⟩,⟨H.b,dH.b⟩,⟨H.d,dH.d⟩⟩
def pairValue (x : Pair) : Vec := (x.1.value,x.2.value)
def pairTangent (x : Pair) : Vec := (x.1.tangent,x.2.tangent)
def matrixTangent (H : Matrix) : Sym2 := ⟨H.a.tangent,H.b.tangent,H.d.tangent⟩
def pairAdd (a b : Pair) : Pair := (Dual.add a.1 b.1,Dual.add a.2 b.2)
def pairSub (a b : Pair) : Pair := (Dual.sub a.1 b.1,Dual.sub a.2 b.2)
def pairScale (t : ℝ) (a : Pair) : Pair :=
  (Dual.mul (Dual.constant t) a.1,Dual.mul (Dual.constant t) a.2)
def pairDot (a b : Pair) : Dual := Dual.add (Dual.mul a.1 b.1) (Dual.mul a.2 b.2)
def matrixMul (H : Matrix) (x : Pair) : Pair :=
  (Dual.add (Dual.mul H.a x.1) (Dual.mul H.b x.2),
   Dual.add (Dual.mul H.b x.1) (Dual.mul H.d x.2))
def matrixUpdate (H : Matrix) (s y : Pair) : Matrix :=
  let c := pairDot s y
  let h := matrixMul H y
  let b := Dual.div (Dual.add (Dual.constant 1) (Dual.div (pairDot y h) c)) c
  ⟨Dual.add (Dual.sub H.a (Dual.div (Dual.mul (Dual.mul (Dual.constant 2) h.1) s.1) c))
      (Dual.mul (Dual.mul b s.1) s.1),
   Dual.add (Dual.sub H.b (Dual.div (Dual.add (Dual.mul h.1 s.2) (Dual.mul s.1 h.2)) c))
      (Dual.mul (Dual.mul b s.1) s.2),
   Dual.add (Dual.sub H.d (Dual.div (Dual.mul (Dual.mul (Dual.constant 2) h.2) s.2) c))
      (Dual.mul (Dual.mul b s.2) s.2)⟩

def step (α : ℝ) (x : Vec) (H : Sym2) (g₀ g₁ : Vec)
    (K₀ K₁ : Vec →L[ℝ] Vec) (δ : State) : State :=
  let xj := pairOf x (point δ)
  let Hj := matrixOf H (metric δ)
  let gj := pairOf g₀ (K₀ (point δ))
  let sj := pairScale (-α) (matrixMul Hj gj)
  let xpj := pairAdd xj sj
  let yj := pairSub (pairOf g₁ (K₁ (pairTangent xpj))) gj
  pack (pairTangent xpj) (matrixTangent (matrixUpdate Hj sj yj))

variable {z : State}
def eval (a : ScalarJet z) (δ : State) : Dual := ⟨a.value,a.differential δ⟩
def evalPair (a : ScalarJet.Pair z) (δ : State) : Pair := (eval a.1 δ,eval a.2 δ)
def evalMatrix (H : ScalarJet.MatrixJet z) (δ : State) : Matrix :=
  ⟨eval H.a δ,eval H.b δ,eval H.d δ⟩

@[simp] theorem eval_constant (a : ℝ) (δ : State) :
    eval (ScalarJet.constant (z := z) a) δ = Dual.constant a := rfl
@[simp] theorem eval_coordinate (i : Fin 5) (δ : State) :
    eval (ScalarJet.coordinate (z := z) i) δ = ⟨z i,δ i⟩ := rfl
@[simp] theorem eval_add (a b : ScalarJet z) (δ : State) :
    eval (ScalarJet.add a b) δ = Dual.add (eval a δ) (eval b δ) := rfl
@[simp] theorem eval_neg (a : ScalarJet z) (δ : State) :
    eval (ScalarJet.neg a) δ = Dual.neg (eval a δ) := rfl
@[simp] theorem eval_sub (a b : ScalarJet z) (δ : State) :
    eval (ScalarJet.sub a b) δ = Dual.sub (eval a δ) (eval b δ) := rfl
@[simp] theorem eval_mul (a b : ScalarJet z) (δ : State) :
    eval (ScalarJet.mul a b) δ = Dual.mul (eval a δ) (eval b δ) := by
  apply Dual.ext
  · rfl
  · simp [eval,ScalarJet.mul,Dual.mul]; ring
@[simp] theorem eval_inv (a : ScalarJet z) (ha : a.value ≠ 0) (δ : State) :
    eval (ScalarJet.inv a ha) δ = Dual.inv (eval a δ) := by
  apply Dual.ext <;> simp [eval,ScalarJet.inv,Dual.inv,pow_two,mul_inv_rev]
@[simp] theorem eval_div (a b : ScalarJet z) (hb : b.value ≠ 0) (δ : State) :
    eval (ScalarJet.div a b hb) δ = Dual.div (eval a δ) (eval b δ) := by
  simp [ScalarJet.div,Dual.div]

@[simp] theorem evalPair_value (a : ScalarJet.Pair z) (δ : State) :
    pairValue (evalPair a δ) = ScalarJet.pairValue a := rfl
@[simp] theorem evalPair_tangent (a : ScalarJet.Pair z) (δ : State) :
    pairTangent (evalPair a δ) = ScalarJet.pairDifferential a δ := rfl
@[simp] theorem eval_pairAdd (a b : ScalarJet.Pair z) (δ : State) :
    evalPair (ScalarJet.pairAdd a b) δ = pairAdd (evalPair a δ) (evalPair b δ) := rfl
@[simp] theorem eval_pairSub (a b : ScalarJet.Pair z) (δ : State) :
    evalPair (ScalarJet.pairSub a b) δ = pairSub (evalPair a δ) (evalPair b δ) := rfl
@[simp] theorem eval_pairScale (t : ℝ) (a : ScalarJet.Pair z) (δ : State) :
    evalPair (ScalarJet.pairScale t a) δ = pairScale t (evalPair a δ) := by
  apply Prod.ext <;> simp [evalPair,ScalarJet.pairScale,pairScale]
@[simp] theorem eval_pairDot (a b : ScalarJet.Pair z) (δ : State) :
    eval (ScalarJet.pairDot a b) δ = pairDot (evalPair a δ) (evalPair b δ) := by
  simp [ScalarJet.pairDot,pairDot,evalPair]
@[simp] theorem eval_matrixMul (H : ScalarJet.MatrixJet z) (a : ScalarJet.Pair z) (δ : State) :
    evalPair (ScalarJet.matrixMul H a) δ = matrixMul (evalMatrix H δ) (evalPair a δ) := by
  apply Prod.ext <;> simp [ScalarJet.matrixMul,matrixMul,evalPair,evalMatrix]
@[simp] theorem eval_matrixUpdate (H : ScalarJet.MatrixJet z) (s y : ScalarJet.Pair z)
    (hc : (ScalarJet.pairDot s y).value ≠ 0) (δ : State) :
    evalMatrix (ScalarJet.matrixUpdate H s y hc) δ =
      matrixUpdate (evalMatrix H δ) (evalPair s δ) (evalPair y δ) := by
  apply Matrix.ext <;>
    simp only [evalMatrix,ScalarJet.matrixUpdate,eval_add,eval_sub,eval_mul,eval_div,
      eval_constant,eval_pairDot,ScalarJet.matrixMul,matrixMul,matrixUpdate,evalPair,eval_add,eval_mul]

@[simp] theorem eval_applyGradient (g : Vec → Vec) (a : ScalarJet.Pair z)
    (K : Vec →L[ℝ] Vec) (hg : HasFDerivAt g K (ScalarJet.pairValue a)) (δ : State) :
    evalPair (ScalarJet.applyGradient g a K hg) δ =
      pairOf (g (ScalarJet.pairValue a)) (K (pairTangent (evalPair a δ))) := rfl

@[simp] theorem eval_inputPoint (δ : State) :
    evalPair (ScalarJet.inputPoint (z := z)) δ = pairOf (point z) (point δ) := rfl
@[simp] theorem eval_inputMetric (δ : State) :
    evalMatrix (ScalarJet.inputMetric (z := z)) δ = matrixOf (metric z) (metric δ) := rfl

theorem packed_apply (x : ScalarJet.Pair z) (H : ScalarJet.MatrixJet z) (δ : State) :
    ScalarJet.packedDifferential x H δ =
      pack (pairTangent (evalPair x δ)) (matrixTangent (evalMatrix H δ)) := by
  ext i
  fin_cases i <;> rfl

theorem stepDifferential_apply (g : Vec → Vec) (α : ℝ) (K₀ K₁ : Vec →L[ℝ] Vec)
    (hg₀ : HasFDerivAt g K₀ (point z))
    (hg₁ : HasFDerivAt g K₁ (point z+α • direction g z))
    (hc : curvature g α z ≠ 0) (δ : State) :
    ScalarJet.stepDifferential g α K₀ K₁ hg₀ hg₁ hc δ =
      step α (point z) (metric z) (g (point z))
        (g (point z+α • direction g z)) K₀ K₁ δ := by
  rw [ScalarJet.stepDifferential,packed_apply]
  simp only [ScalarJet.updatedMetric,eval_matrixUpdate,ScalarJet.gradientDifference,
    eval_pairSub,eval_applyGradient,ScalarJet.searchPoint_value]
  simp only [ScalarJet.searchPoint,eval_pairAdd,ScalarJet.searchDisplacement,
    eval_pairScale,eval_matrixMul,eval_inputPoint,eval_inputMetric]
  rfl

end
end BFGS.Algorithm.Variation
