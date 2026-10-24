import BFGS.Analysis.Iteration

/-! First-order arithmetic carrying its own Fréchet-derivative proof.
The resulting update differentiates the actual BFGS formula, with the
gradient derivatives supplied as continuous linear maps. -/
namespace BFGS.Algorithm
noncomputable section

structure ScalarJet (z : State) where
  fn : State → ℝ
  value : ℝ
  differential : State →L[ℝ] ℝ
  value_eq : fn z = value
  hasFDerivAt : HasFDerivAt fn differential z

namespace ScalarJet
variable {z : State}

def constant (a : ℝ) : ScalarJet z :=
  ⟨fun _ => a,a,0,rfl,hasFDerivAt_const a z⟩

def coordinate (i : Fin 5) : ScalarJet z :=
  ⟨fun q => q i,z i,ContinuousLinearMap.proj i,rfl,hasFDerivAt_apply i z⟩

def add (a b : ScalarJet z) : ScalarJet z where
  fn q := a.fn q+b.fn q
  value := a.value+b.value
  differential := a.differential+b.differential
  value_eq := by rw [a.value_eq,b.value_eq]
  hasFDerivAt := a.hasFDerivAt.add b.hasFDerivAt

def neg (a : ScalarJet z) : ScalarJet z where
  fn q := -a.fn q
  value := -a.value
  differential := -a.differential
  value_eq := by rw [a.value_eq]
  hasFDerivAt := a.hasFDerivAt.neg

def sub (a b : ScalarJet z) : ScalarJet z := add a (neg b)

def mul (a b : ScalarJet z) : ScalarJet z where
  fn q := a.fn q*b.fn q
  value := a.value*b.value
  differential := a.value • b.differential+b.value • a.differential
  value_eq := by rw [a.value_eq,b.value_eq]
  hasFDerivAt := by
    have h := a.hasFDerivAt.mul b.hasFDerivAt
    rw [a.value_eq,b.value_eq] at h
    exact h

def inv (a : ScalarJet z) (ha : a.value ≠ 0) : ScalarJet z where
  fn q := (a.fn q)⁻¹
  value := a.value⁻¹
  differential := (-(a.value^2)⁻¹) • a.differential
  value_eq := by rw [a.value_eq]
  hasFDerivAt := by
    have hn : a.fn z ≠ 0 := by rwa [a.value_eq]
    simpa only [a.value_eq,Function.comp_def] using
      (hasDerivAt_inv hn).comp_hasFDerivAt z a.hasFDerivAt

def div (a b : ScalarJet z) (hb : b.value ≠ 0) : ScalarJet z := mul a (inv b hb)

abbrev Pair (z : State) := ScalarJet z × ScalarJet z
def pairValue (a : Pair z) : Vec := (a.1.value,a.2.value)
def pairFunction (a : Pair z) (q : State) : Vec := (a.1.fn q,a.2.fn q)
def pairDifferential (a : Pair z) : State →L[ℝ] Vec :=
  a.1.differential.prod a.2.differential

theorem pairValue_eq (a : Pair z) : pairFunction a z = pairValue a := by
  simp [pairFunction,pairValue,a.1.value_eq,a.2.value_eq]

theorem pair_hasFDerivAt (a : Pair z) :
    HasFDerivAt (pairFunction a) (pairDifferential a) z :=
  a.1.hasFDerivAt.prodMk a.2.hasFDerivAt

def applyGradient (g : Vec → Vec) (a : Pair z) (K : Vec →L[ℝ] Vec)
    (hg : HasFDerivAt g K (pairValue a)) : Pair z := by
  have hg' : HasFDerivAt g K (pairFunction a z) := by rwa [pairValue_eq]
  have hcomp := hg'.comp z (pair_hasFDerivAt a)
  exact
    (⟨fun q => (g (pairFunction a q)).1,(g (pairValue a)).1,
      (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (K.comp (pairDifferential a)),
      by rw [pairValue_eq],hcomp.fst⟩,
     ⟨fun q => (g (pairFunction a q)).2,(g (pairValue a)).2,
      (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (K.comp (pairDifferential a)),
      by rw [pairValue_eq],hcomp.snd⟩)

def pairAdd (a b : Pair z) : Pair z := (add a.1 b.1,add a.2 b.2)
def pairSub (a b : Pair z) : Pair z := (sub a.1 b.1,sub a.2 b.2)
def pairScale (t : ℝ) (a : Pair z) : Pair z :=
  (mul (constant t) a.1,mul (constant t) a.2)
def pairDot (a b : Pair z) : ScalarJet z := add (mul a.1 b.1) (mul a.2 b.2)

structure MatrixJet (z : State) where
  a : ScalarJet z
  b : ScalarJet z
  d : ScalarJet z

def matrixMul (H : MatrixJet z) (x : Pair z) : Pair z :=
  (add (mul H.a x.1) (mul H.b x.2),add (mul H.b x.1) (mul H.d x.2))

def matrixUpdate (H : MatrixJet z) (s y : Pair z)
    (hc : (pairDot s y).value ≠ 0) : MatrixJet z :=
  let c := pairDot s y
  let h := matrixMul H y
  let b := div (add (constant 1) (div (pairDot y h) c hc)) c hc
  ⟨add (sub H.a (div (mul (mul (constant 2) h.1) s.1) c hc))
      (mul (mul b s.1) s.1),
   add (sub H.b (div (add (mul h.1 s.2) (mul s.1 h.2)) c hc))
      (mul (mul b s.1) s.2),
   add (sub H.d (div (mul (mul (constant 2) h.2) s.2) c hc))
      (mul (mul b s.2) s.2)⟩

def matrixFunction (H : MatrixJet z) (q : State) : Sym2 :=
  ⟨H.a.fn q,H.b.fn q,H.d.fn q⟩

theorem matrixUpdate_function (H : MatrixJet z) (s y : Pair z)
    (hc : (pairDot s y).value ≠ 0) (q : State) :
    matrixFunction (matrixUpdate H s y hc) q =
      update (matrixFunction H q) (pairFunction s q) (pairFunction y q) := by
  apply Sym2.ext <;>
    simp only [matrixFunction,matrixUpdate,pairDot,matrixMul,add,sub,neg,mul,div,
      inv,constant,pairFunction,update,dot,Sym2.mulV,div_eq_mul_inv,sub_eq_add_neg]

def inputPoint : Pair z := (coordinate 0,coordinate 1)
def inputMetric : MatrixJet z := ⟨coordinate 2,coordinate 3,coordinate 4⟩

def searchDisplacement (g : Vec → Vec) (α : ℝ) (K₀ : Vec →L[ℝ] Vec)
    (hg₀ : HasFDerivAt g K₀ (point z)) : Pair z :=
  pairScale (-α) (matrixMul inputMetric (applyGradient g inputPoint K₀ hg₀))

theorem searchDisplacement_function (g : Vec → Vec) (α : ℝ) (K₀ : Vec →L[ℝ] Vec)
    (hg₀ : HasFDerivAt g K₀ (point z)) (q : State) :
    pairFunction (searchDisplacement g α K₀ hg₀) q = α • direction g q := by
  apply Prod.ext <;>
    simp [pairFunction,searchDisplacement,pairScale,matrixMul,inputMetric,inputPoint,
      applyGradient,coordinate,constant,mul,add,direction,point,metric,Sym2.mulV] <;> ring

def searchPoint (g : Vec → Vec) (α : ℝ) (K₀ : Vec →L[ℝ] Vec)
    (hg₀ : HasFDerivAt g K₀ (point z)) : Pair z :=
  pairAdd inputPoint (searchDisplacement g α K₀ hg₀)

theorem searchPoint_function (g : Vec → Vec) (α : ℝ) (K₀ : Vec →L[ℝ] Vec)
    (hg₀ : HasFDerivAt g K₀ (point z)) (q : State) :
    pairFunction (searchPoint g α K₀ hg₀) q = point q+α • direction g q := by
  change pairFunction (inputPoint (z := z)) q +
    pairFunction (searchDisplacement g α K₀ hg₀) q = _
  rw [searchDisplacement_function]
  rfl

theorem searchPoint_value (g : Vec → Vec) (α : ℝ) (K₀ : Vec →L[ℝ] Vec)
    (hg₀ : HasFDerivAt g K₀ (point z)) :
    pairValue (searchPoint g α K₀ hg₀) = point z+α • direction g z := by
  rw [← pairValue_eq,searchPoint_function]

def gradientDifference (g : Vec → Vec) (α : ℝ) (K₀ K₁ : Vec →L[ℝ] Vec)
    (hg₀ : HasFDerivAt g K₀ (point z))
    (hg₁ : HasFDerivAt g K₁ (point z+α • direction g z)) : Pair z :=
  pairSub (applyGradient g (searchPoint g α K₀ hg₀) K₁
      (by rw [searchPoint_value]; exact hg₁))
    (applyGradient g inputPoint K₀ hg₀)

theorem gradientDifference_function (g : Vec → Vec) (α : ℝ) (K₀ K₁ : Vec →L[ℝ] Vec)
    (hg₀ : HasFDerivAt g K₀ (point z))
    (hg₁ : HasFDerivAt g K₁ (point z+α • direction g z)) (q : State) :
    pairFunction (gradientDifference g α K₀ K₁ hg₀ hg₁) q =
      g (point q+α • direction g q)-g (point q) := by
  change g (pairFunction (searchPoint g α K₀ hg₀) q)-g (point q) = _
  rw [searchPoint_function]

def updatedMetric (g : Vec → Vec) (α : ℝ) (K₀ K₁ : Vec →L[ℝ] Vec)
    (hg₀ : HasFDerivAt g K₀ (point z))
    (hg₁ : HasFDerivAt g K₁ (point z+α • direction g z))
    (hc : curvature g α z ≠ 0) : MatrixJet z :=
  matrixUpdate inputMetric (searchDisplacement g α K₀ hg₀)
    (gradientDifference g α K₀ K₁ hg₀ hg₁) (by
      rw [← (pairDot _ _).value_eq]
      change dot (pairFunction (searchDisplacement g α K₀ hg₀) z)
        (pairFunction (gradientDifference g α K₀ K₁ hg₀ hg₁) z) ≠ 0
      rw [searchDisplacement_function,gradientDifference_function]
      exact hc)

theorem updatedMetric_function (g : Vec → Vec) (α : ℝ) (K₀ K₁ : Vec →L[ℝ] Vec)
    (hg₀ : HasFDerivAt g K₀ (point z))
    (hg₁ : HasFDerivAt g K₁ (point z+α • direction g z))
    (hc : curvature g α z ≠ 0) (q : State) :
    matrixFunction (updatedMetric g α K₀ K₁ hg₀ hg₁ hc) q =
      update (metric q) (α • direction g q)
        (g (point q+α • direction g q)-g (point q)) := by
  unfold updatedMetric
  rw [matrixUpdate_function,searchDisplacement_function,gradientDifference_function]
  rfl

def packedDifferential (x : Pair z) (H : MatrixJet z) : State →L[ℝ] State :=
  ContinuousLinearMap.pi ![x.1.differential,x.2.differential,
    H.a.differential,H.b.differential,H.d.differential]

theorem packed_hasFDerivAt (x : Pair z) (H : MatrixJet z) :
    HasFDerivAt (fun q => pack (pairFunction x q) (matrixFunction H q))
      (packedDifferential x H) z := by
  apply hasFDerivAt_pi.2
  intro i
  fin_cases i
  · exact x.1.hasFDerivAt
  · exact x.2.hasFDerivAt
  · exact H.a.hasFDerivAt
  · exact H.b.hasFDerivAt
  · exact H.d.hasFDerivAt

/-- The differential is given explicitly by scalar arithmetic and the two
gradient derivatives, rather than by an unevaluated `fderiv`. -/
def stepDifferential (g : Vec → Vec) (α : ℝ) (K₀ K₁ : Vec →L[ℝ] Vec)
    (hg₀ : HasFDerivAt g K₀ (point z))
    (hg₁ : HasFDerivAt g K₁ (point z+α • direction g z))
    (hc : curvature g α z ≠ 0) : State →L[ℝ] State :=
  packedDifferential (searchPoint g α K₀ hg₀) (updatedMetric g α K₀ K₁ hg₀ hg₁ hc)

theorem acceptedStep_hasFDerivAt (g : Vec → Vec) (α : ℝ) (K₀ K₁ : Vec →L[ℝ] Vec)
    (hg₀ : HasFDerivAt g K₀ (point z))
    (hg₁ : HasFDerivAt g K₁ (point z+α • direction g z))
    (hc : curvature g α z ≠ 0) :
    HasFDerivAt (acceptedStep g α) (stepDifferential g α K₀ K₁ hg₀ hg₁ hc) z := by
  have h := packed_hasFDerivAt (searchPoint g α K₀ hg₀)
    (updatedMetric g α K₀ K₁ hg₀ hg₁ hc)
  simp only [searchPoint_function,updatedMetric_function] at h
  exact h

end ScalarJet
end
end BFGS.Algorithm
