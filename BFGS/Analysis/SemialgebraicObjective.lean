import BFGS.Analysis.Semialgebraic
import BFGS.Analysis.AngularJets

/-! Semialgebraicity of the concrete angular objective. All divisions are
eliminated on positive-denominator half-planes; finite profile gluing becomes
finite polynomial-sign gluing in physical coordinates. -/
namespace BFGS.Semialgebraic
noncomputable section
open Set Algorithm

variable {n : ℕ}

theorem perspective_piecewiseRational {h : ℝ → ℝ} (hh : PiecewisePolynomial h)
    (a w : Space n → ℝ) (ha : Poly a) (hw : Poly w)
    (S : Set (Space n)) (hS : IsSemialgebraic S)
    (hpos : ∀ x ∈ S, 0 < a x) :
    PiecewiseRationalOn S (fun x => perspective h (a x) (w x)) := by
  induction hh generalizing S with
  | polynomial P =>
    apply PiecewiseRationalOn.single hS
    exact (RationalOn.of_poly ha).mul
      (((RationalOn.of_poly hw).div (RationalOn.of_poly ha)
        (fun x hx => (hpos x hx).ne')).eval P)
  | @glue f g c hf hg ihf ihg =>
    let L : Set (Space n) := {x | w x ≤ c*a x}
    let R : Set (Space n) := {x | c*a x < w x}
    have hL : IsSemialgebraic L := IsSemialgebraic.le hw ((Poly.const c).mul ha)
    have hR : IsSemialgebraic R := IsSemialgebraic.lt ((Poly.const c).mul ha) hw
    have hcover : S = (S ∩ L) ∪ (S ∩ R) := by
      ext x
      simp only [mem_union,mem_inter_iff,L,R,mem_ofPred_eq]
      constructor
      · intro hx; by_cases hwc : w x ≤ c*a x
        · exact Or.inl ⟨hx,hwc⟩
        · exact Or.inr ⟨hx,lt_of_not_ge hwc⟩
      · rintro (h | h) <;> exact h.1
    rw [hcover]
    apply PiecewiseRationalOn.union
    · apply (ihf (S ∩ L) (hS.inter hL) (fun x hx => hpos x hx.1)).congr
      intro x hx
      have ht : w x/a x ≤ c := (div_le_iff₀ (hpos x hx.1)).2 hx.2
      simp [perspective,glueAt,ht]
    · apply (ihg (S ∩ R) (hS.inter hR) (fun x hx => hpos x hx.1)).congr
      intro x hx
      have ht : ¬ w x/a x ≤ c := not_le_of_gt ((lt_div_iff₀ (hpos x hx.1)).2 hx.2)
      simp [perspective,glueAt,ht]

def physicalCoordinate (e : Vec) (z : Space 3) : ℝ := dot e (z 0,z 1)

theorem physicalCoordinate_poly (e : Vec) : Poly (physicalCoordinate e) := by
  exact ((Poly.const e.1).mul (Poly.coord 0)).add
    ((Poly.const e.2).mul (Poly.coord 1))

theorem angularLift_piecewiseRational (hMinus hPlus : ℝ → ℝ)
    (hm : PiecewisePolynomial hMinus) (hp : PiecewisePolynomial hPlus)
    (u w : Space n → ℝ) (hu : Poly u) (hw : Poly w) :
    PiecewiseRationalOn Set.univ (fun z => angularLift hMinus hPlus (u z,w z)) := by
  let S0 : Set (Space n) := {z | u z=0}
  let Sm : Set (Space n) := {z | u z<0}
  let Sp : Set (Space n) := {z | 0<u z}
  have h0 : IsSemialgebraic S0 := IsSemialgebraic.eq hu (Poly.const 0)
  have hmS : IsSemialgebraic Sm := IsSemialgebraic.lt hu (Poly.const 0)
  have hpS : IsSemialgebraic Sp := IsSemialgebraic.lt (Poly.const 0) hu
  have hcover : (Set.univ : Set (Space n)) = S0 ∪ Sm ∪ Sp := by
    ext z
    simp only [mem_univ,mem_union,S0,Sm,Sp,mem_ofPred_eq,true_iff]
    rcases lt_trichotomy (u z) 0 with h | h | h
    · exact Or.inl (Or.inr h)
    · exact Or.inl (Or.inl h)
    · exact Or.inr h
  rw [hcover]
  apply PiecewiseRationalOn.union
  · apply PiecewiseRationalOn.union
    · apply (PiecewiseRationalOn.single h0 (RationalOn.of_poly hw)).congr
      intro z hz
      simp only [S0,mem_ofPred_eq] at hz
      simp [angularLift,hz]
    · have h := perspective_piecewiseRational hm (fun z => -u z) w hu.neg hw Sm hmS
        (fun z hz => neg_pos.mpr hz)
      apply h.congr
      intro z hz
      simp only [Sm,mem_ofPred_eq] at hz
      simp [perspective,angularLift,hz.ne,hz,abs_of_neg hz]
  · have h := perspective_piecewiseRational hp u w hu hw Sp hpS (fun _ hz => hz)
    apply h.congr
    intro z hz
    simp only [Sp,mem_ofPred_eq] at hz
    simp [perspective,angularLift,hz.ne',not_lt_of_ge hz.le,abs_of_pos hz]

theorem physicalAngular_piecewiseRational (hm hp : C2Profile)
    (hmP : PiecewisePolynomial hm.value) (hpP : PiecewisePolynomial hp.value)
    (e v : Vec) : PiecewiseRationalOn Set.univ
      (fun z : Space 3 => physicalAngular hm hp e v (z 0,z 1)) :=
  angularLift_piecewiseRational hm.value hp.value hmP hpP
    (physicalCoordinate e) (physicalCoordinate v)
    (physicalCoordinate_poly e) (physicalCoordinate_poly v)

/-- The graph of a two-variable function in the coordinate order (x₁,x₂,y). -/
def IsSemialgebraicFunction (f : Vec → ℝ) : Prop :=
  IsSemialgebraic {z : Space 3 | f (z 0,z 1)=z 2}


end
end BFGS.Semialgebraic
