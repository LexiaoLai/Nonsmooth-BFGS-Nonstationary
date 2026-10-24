import BFGS.Analysis.UpdateVariation

/-! The expanded directional derivative used by the independent verifier
is exactly the derivative of the ordinary unit inverse-BFGS step. -/
namespace BFGS.Counterexample
noncomputable section
open BFGS.Algorithm
set_option maxHeartbeats 0
set_option maxRecDepth 10000

/-- A symmetric matrix acting as a continuous linear map. -/
def symmetricMap (H : BFGS.Algorithm.Sym2) : Vec →L[ℝ] Vec :=
  (H.a • ContinuousLinearMap.fst ℝ ℝ ℝ +
   H.b • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
  (H.b • ContinuousLinearMap.fst ℝ ℝ ℝ +
   H.d • ContinuousLinearMap.snd ℝ ℝ ℝ)

@[simp] theorem symmetricMap_apply (H : BFGS.Algorithm.Sym2) (v : Vec) :
    symmetricMap H v = H.mulV v := by
  rfl

def addSym (A B : BFGS.Algorithm.Sym2) : BFGS.Algorithm.Sym2 :=
  ⟨A.a+B.a,A.b+B.b,A.d+B.d⟩

def outerSym (u : Vec) : BFGS.Algorithm.Sym2 := ⟨u.1*u.1,u.1*u.2,u.2*u.2⟩

def crossSym (u v : Vec) : BFGS.Algorithm.Sym2 :=
  ⟨u.1*v.1+v.1*u.1,u.1*v.2+v.1*u.2,u.2*v.2+v.2*u.2⟩

/-- The expanded differentiated update in verification/verify.py. -/
def expandedUpdate (H dH : BFGS.Algorithm.Sym2) (s y ds dy : Vec) : BFGS.Algorithm.Sym2 :=
  let c := dot s y
  let h := H.mulV y
  let d := dot y h
  let dc := dot ds y+dot s dy
  let dh := dH.mulV y+H.mulV dy
  let dd := 2*dot dy h+dot y (dH.mulV y)
  let N := crossSym h s
  let V := outerSym s
  let dN := addSym (crossSym dh s) (crossSym h ds)
  let dV := crossSym ds s
  addSym (addSym (addSym (addSym dH (dN.scale (-1/c)))
    (N.scale (dc/(c*c))))
    (V.scale ((dc+dd)/(c*c)-2*(c+d)*dc/(c*c*c))))
    (dV.scale ((c+d)/(c*c)))

theorem expandedUpdate_eq (H dH : BFGS.Algorithm.Sym2) (s y ds dy : Vec)
    (hc : dot s y ≠ 0) :
    expandedUpdate H dH s y ds dy =
      Variation.matrixTangent (Variation.matrixUpdate (Variation.matrixOf H dH)
        (Variation.pairOf s ds) (Variation.pairOf y dy)) := by
  apply BFGS.Algorithm.Sym2.ext <;>
    dsimp [expandedUpdate,addSym,outerSym,crossSym,Sym2.scale,Sym2.mulV,dot,
      Variation.matrixTangent,Variation.matrixUpdate,Variation.matrixOf,
      Variation.pairOf,Variation.pairDot,Variation.matrixMul,
      Variation.Dual.add,Variation.Dual.sub,Variation.Dual.neg,Variation.Dual.mul,
      Variation.Dual.div,Variation.Dual.inv,Variation.Dual.constant]
  all_goals
    dsimp [dot] at hc
    generalize he : s.1*y.1+s.2*y.2 = c at *
    field_simp [hc]
    rw [← he]
    ring

/-- The five output coordinates of one unit-step directional derivative. -/
def expandedStep (H : BFGS.Algorithm.Sym2) (g gp : Vec)
    (K Kp : Vec →L[ℝ] Vec) (δ : State) : State :=
  let dx := point δ
  let dH := metric δ
  let s := -H.mulV g
  let y := gp-g
  let dg := K dx
  let ds := -(dH.mulV g+H.mulV dg)
  let dxp := dx+ds
  let dy := Kp dxp-dg
  pack dxp (expandedUpdate H dH s y ds dy)

theorem expandedStep_eq_variation (x : Vec) (H : BFGS.Algorithm.Sym2) (g gp : Vec)
    (K Kp : Vec →L[ℝ] Vec) (δ : State)
    (hc : dot (-H.mulV g) (gp-g) ≠ 0) :
    expandedStep H g gp K Kp δ = Variation.step 1 x H g gp K Kp δ := by
  rw [expandedStep,expandedUpdate_eq H (metric δ) _ _ _ _ hc]
  unfold Variation.step
  have hs : Variation.pairScale (-(1:ℝ))
      (Variation.matrixMul (Variation.matrixOf H (metric δ))
        (Variation.pairOf g (K (point δ)))) =
      Variation.pairOf (-H.mulV g) (-((metric δ).mulV g+H.mulV (K (point δ)))) := by
    apply Prod.ext <;> apply Variation.Dual.ext <;>
      dsimp [Variation.pairScale,Variation.matrixMul,Variation.matrixOf,Variation.pairOf,
        Variation.Dual.mul,Variation.Dual.add,Variation.Dual.constant,Sym2.mulV] <;> ring
  dsimp only
  rw [hs]
  rfl

/-- The verifier's arithmetic is the actual Frechet derivative when the
input and output gradient derivatives are the prescribed Hessians. -/
theorem expandedStep_is_derivative (G : Vec → Vec) (z : State)
    (K Kp : Vec →L[ℝ] Vec)
    (hK : HasFDerivAt G K (point z))
    (hKp : HasFDerivAt G Kp (point z+direction G z))
    (hc : curvature G 1 z ≠ 0) :
    ∃ L : State →L[ℝ] State,
      HasFDerivAt (acceptedStep G 1) L z ∧
      ∀ δ, L δ = expandedStep (metric z) (G (point z))
        (G (point z+direction G z)) K Kp δ := by
  have hKp' : HasFDerivAt G Kp (point z+(1:ℝ) • direction G z) := by simpa using hKp
  refine ⟨ScalarJet.stepDifferential G 1 K Kp hK hKp' hc,
    ScalarJet.acceptedStep_hasFDerivAt G 1 K Kp hK hKp' hc, ?_⟩
  intro δ
  rw [Variation.stepDifferential_apply]
  simp only [one_smul]
  apply (expandedStep_eq_variation _ _ _ _ _ _ _ _).symm
  simpa [curvature,direction] using hc

end
end BFGS.Counterexample
