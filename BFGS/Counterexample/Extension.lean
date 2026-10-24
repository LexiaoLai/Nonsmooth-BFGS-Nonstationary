import BFGS.Counterexample.Analysis
import BFGS.Analysis.SemialgebraicObjective

/-! The exact locally Lipschitz coercive extension in the current manuscript. -/
namespace BFGS.Counterexample
noncomputable section
open Algorithm Filter Topology

def squaredRadius (x : Vec) : ℝ := x.1^2+x.2^2

def radialExtension (f : Vec → ℝ) (x : Vec) : ℝ :=
  f x+max 0 (squaredRadius x-100)

theorem squaredRadius_continuous : Continuous squaredRadius := by
  unfold squaredRadius
  fun_prop

theorem radialExtension_eq (f : Vec → ℝ) {x : Vec} (hx : squaredRadius x ≤ 100) :
    radialExtension f x = f x := by
  simp [radialExtension, max_eq_left (sub_nonpos.mpr hx)]

theorem radialExtension_eventuallyEq (f : Vec → ℝ) {x : Vec}
    (hx : squaredRadius x < 100) : radialExtension f =ᶠ[𝓝 x] f := by
  filter_upwards [squaredRadius_continuous.continuousAt.eventually_lt_const hx] with y hy
  exact radialExtension_eq f hy.le

theorem radialExtension_gradient (f : Vec → ℝ) (g : Vec) {x : Vec}
    (hx : squaredRadius x < 100) (hg : IsGradientAt f g x) :
    IsGradientAt (radialExtension f) g x :=
  hg.congr_of_eventuallyEq (radialExtension_eventuallyEq f hx)

theorem radialExtension_clarke (f : Vec → ℝ) :
    clarkeSubdifferential (radialExtension f) 0 = clarkeSubdifferential f 0 :=
  clarkeSubdifferential_congr_of_eventuallyEq
    (radialExtension_eventuallyEq f (by norm_num [squaredRadius]))

theorem radialExtension_continuous (f : Vec → ℝ) (hf : Continuous f) :
    Continuous (radialExtension f) :=
  hf.add (continuous_const.max (squaredRadius_continuous.sub continuous_const))

theorem radialExtension_locallyLipschitz (f : Vec → ℝ) (hf : LocallyLipschitz f) :
    LocallyLipschitz (radialExtension f) := by
  have hs : LocallyLipschitz (fun x : Vec => squaredRadius x-100) :=
    (show ContDiff ℝ 1 (fun x : Vec => squaredRadius x-100) by
      unfold squaredRadius; fun_prop).locallyLipschitz
  exact hf.add (hs.const_max 0)

theorem norm_squared_le_squaredRadius (x : Vec) : ‖x‖^2 ≤ squaredRadius x := by
  rw [Prod.norm_def, squaredRadius]
  rcases le_total ‖x.1‖ ‖x.2‖ with h | h
  · rw [max_eq_right h, Real.norm_eq_abs, sq_abs]
    nlinarith [sq_nonneg x.1]
  · rw [max_eq_left h, Real.norm_eq_abs, sq_abs]
    nlinarith [sq_nonneg x.2]

theorem radialExtension_sublevel_bound (f : Vec → ℝ) (L M : ℝ)
    (hL : 0 ≤ L) (hf : ∀ x, -L*‖x‖ ≤ f x) {x : Vec}
    (hx : radialExtension f x ≤ M) : ‖x‖ ≤ L+|M|+101 := by
  have hf' := hf x
  have hs := norm_squared_le_squaredRadius x
  have hmax : squaredRadius x-100 ≤ max 0 (squaredRadius x-100) := le_max_right _ _
  dsimp [radialExtension] at hx
  by_contra hn
  have ht : L+|M|+101 < ‖x‖ := lt_of_not_ge hn
  have hprod := mul_lt_mul_of_pos_right ht (show 0 < ‖x‖ by
    linarith [abs_nonneg M])
  have hM := le_abs_self M
  have hprod' := mul_nonneg (abs_nonneg M) (show 0 ≤ ‖x‖-1 by
    linarith [abs_nonneg M])
  nlinarith

theorem radialExtension_compact_sublevels (f : Vec → ℝ) (K : NNReal)
    (hf : LipschitzWith K f) (hzero : f 0 = 0) (a : ℝ) :
    IsCompact {x | radialExtension f x ≤ a} := by
  apply Metric.isCompact_iff_isClosed_bounded.mpr
  refine ⟨isClosed_le (radialExtension_continuous f hf.continuous) continuous_const, ?_⟩
  apply isBounded_iff_forall_norm_le.2
  refine ⟨(K : ℝ)+|a|+101, ?_⟩
  intro x hx
  apply radialExtension_sublevel_bound f K a K.coe_nonneg _ hx
  intro y
  have h := hf.norm_sub_le y 0
  simp only [hzero, sub_zero, Real.norm_eq_abs] at h
  simpa only [neg_mul] using (neg_le_neg h).trans (neg_abs_le _)

theorem radialExtension_coercive (f : Vec → ℝ) (K : NNReal)
    (hf : LipschitzWith K f) (hzero : f 0 = 0) :
    Tendsto (radialExtension f) (cocompact Vec) atTop := by
  apply Filter.tendsto_atTop.2
  intro a
  filter_upwards [(radialExtension_compact_sublevels f K hf hzero a).compl_mem_cocompact]
    with x hx
  change ¬ radialExtension f x ≤ a at hx
  exact (lt_of_not_ge hx).le

open Semialgebraic in
private theorem piecewise_add_poly {n : ℕ} {S : Set (Space n)} {f g : Space n → ℝ}
    (hf : PiecewiseRationalOn S f) (hg : Poly g) :
    PiecewiseRationalOn S (fun x => f x+g x) := by
  induction hf with
  | single hS hR => exact .single hS (hR.add (.of_poly hg))
  | union hS hT ihS ihT => exact ihS.union ihT

open Semialgebraic in
theorem radialExtension_semialgebraic (f : Vec → ℝ)
    (hf : PiecewiseRationalOn Set.univ (fun z : Space 3 => f (z 0,z 1))) :
    IsSemialgebraicFunction (radialExtension f) := by
  let Q : Space 3 → ℝ := fun z => squaredRadius (z 0,z 1)-100
  have hQ : Poly Q := ((Poly.coord 0).pow 2 |>.add ((Poly.coord 1).pow 2)).sub (Semialgebraic.Poly.const 100)
  have hLo := hf.restrict (IsSemialgebraic.le hQ (Semialgebraic.Poly.const 0))
  have hHi := (piecewise_add_poly hf hQ).restrict (IsSemialgebraic.le (Semialgebraic.Poly.const 0) hQ)
  have hL : PiecewiseRationalOn (Set.univ ∩ {z | Q z ≤ 0})
      (fun z : Space 3 => radialExtension f (z 0,z 1)) := by
    apply hLo.congr
    intro z hz
    have hz' : Q z ≤ 0 := hz.2
    change f (z 0,z 1) = f (z 0,z 1)+max 0 (Q z)
    rw [max_eq_left hz', add_zero]
  have hH : PiecewiseRationalOn (Set.univ ∩ {z | 0 ≤ Q z})
      (fun z : Space 3 => radialExtension f (z 0,z 1)) := by
    apply hHi.congr
    intro z hz
    have hz' : 0 ≤ Q z := hz.2
    change f (z 0,z 1)+Q z = f (z 0,z 1)+max 0 (Q z)
    rw [max_eq_right hz']
  have hcover : (Set.univ ∩ {z | Q z ≤ 0}) ∪ (Set.univ ∩ {z | 0 ≤ Q z}) = Set.univ := by
    ext z
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_univ, true_and, Set.mem_ofPred_eq]
    exact iff_true_intro (le_total (Q z) 0)
  have h := hL.union hH
  rw [hcover] at h
  simpa only [IsSemialgebraicFunction, Set.mem_univ, true_and] using
    h.graph (Poly.coord (2 : Fin 3))

end
end BFGS.Counterexample
