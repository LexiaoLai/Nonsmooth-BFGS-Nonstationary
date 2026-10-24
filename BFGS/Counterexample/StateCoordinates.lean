import BFGS.Analysis.StateSpace

/-! Linear coordinates for the fixed-ray proof in Section 2.3. These coordinates do not divide by a state coordinate:
they record `ω₃` and the displacement `ω − ω₃ ω_*` from the fixed ray. -/
namespace BFGS.Counterexample
noncomputable section
open Algorithm BFGS.StateSpace

/-- The full five-dimensional state in axial and transverse coordinates. -/
def splitState (c : TransverseSpace) : State ≃L[ℝ] ℝ × TransverseSpace :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun z => (z 2, fun i => z (keep i) - z 2 * c i)
      invFun := fun z => z.1 • embed c + embedDifferential z.2
      map_add' := by
        intro z w
        apply Prod.ext
        · rfl
        · funext i
          change z (keep i) + w (keep i) - (z 2 + w 2) * c i =
            (z (keep i) - z 2 * c i) + (w (keep i) - w 2 * c i)
          ring
      map_smul' := by
        intro a z
        apply Prod.ext
        · rfl
        · funext i
          change a * z (keep i) - (a * z 2) * c i = a * (z (keep i)-z 2*c i)
          ring
      left_inv := by
        intro z
        funext i
        fin_cases i <;> simp [embed,embedDifferential,keep]
      right_inv := by
        rintro ⟨a,u⟩
        apply Prod.ext
        · simp [embed,embedDifferential]
        · funext i
          fin_cases i <;> simp [embed,embedDifferential,keep] }

@[simp] theorem splitState_apply (c : TransverseSpace) (z : State) :
    splitState c z = (z 2, fun i => z (keep i) - z 2 * c i) := rfl

@[simp] theorem splitState_symm_apply (c : TransverseSpace) (z : ℝ × TransverseSpace) :
    (splitState c).symm z = z.1 • embed c + embedDifferential z.2 := rfl

@[simp] theorem splitState_base (c : TransverseSpace) : splitState c (embed c) = (1,0) := by
  apply Prod.ext
  · simp [splitState_apply,embed]
  · funext i
    simp [splitState_apply,embed_keep,embed_two]

/-- The paper's transverse norm is the ordinary maximum norm after applying
`S`. The first coordinate is left unchanged. -/
def weightedStateCoordinates (c : TransverseSpace) (e : TransverseSpace ≃L[ℝ] TransverseSpace) :
    State ≃L[ℝ] ℝ × TransverseSpace :=
  (splitState c).trans ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr e)

@[simp] theorem weightedStateCoordinates_apply (c : TransverseSpace)
    (e : TransverseSpace ≃L[ℝ] TransverseSpace) (z : State) :
    weightedStateCoordinates c e z =
      (z 2, e (fun i => z (keep i)-z 2*c i)) := rfl

@[simp] theorem weightedStateCoordinates_symm_apply (c : TransverseSpace)
    (e : TransverseSpace ≃L[ℝ] TransverseSpace) (z : ℝ × TransverseSpace) :
    (weightedStateCoordinates c e).symm z =
      z.1 • embed c + embedDifferential (e.symm z.2) := rfl

@[simp] theorem weightedStateCoordinates_base (c : TransverseSpace)
    (e : TransverseSpace ≃L[ℝ] TransverseSpace) : weightedStateCoordinates c e (embed c) = (1,0) := by
  change ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr e) (splitState c (embed c)) = _
  rw [splitState_base]
  simp

end
end BFGS.Counterexample
