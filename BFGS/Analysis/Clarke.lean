import Mathlib

/-!
# Clarke separation from directional monotonicity

This file uses the standard
joint-limsup definition of the Clarke generalized directional derivative,
with continuous linear functionals as subgradients. In finite-dimensional
Euclidean space these are identified with gradient vectors by the Riesz map.

The results below do not assert existence of the interpolated BFGS objective.
They prove the analytic separation consequence once a directional increment
inequality has actually been established for a function.
-/

namespace BFGS

noncomputable section

open Filter Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The difference quotient in the Clarke generalized derivative. -/
def clarkeQuotient (f : E → ℝ) (d : E) (p : E × ℝ) : EReal :=
  if p.2 = 0 then 0 else ((f (p.1 + p.2 • d) - f p.1) / p.2 : ℝ)

/-- The base point approaches `x` and the step approaches zero from above. -/
def clarkeFilter (x : E) : Filter (E × ℝ) :=
  nhds x ×ˢ nhdsWithin 0 (Ioi 0)

/-- The standard Clarke generalized directional derivative. -/
def clarkeDirectional (f : E → ℝ) (x d : E) : EReal :=
  Filter.limsup (clarkeQuotient f d) (clarkeFilter x)

/-- The standard dual-space Clarke subdifferential. -/
def clarkeSubdifferential (f : E → ℝ) (x : E) : Set (E →L[ℝ] ℝ) :=
  {L | ∀ d, (L d : EReal) ≤ clarkeDirectional f x d}

/-- A uniform lower bound on increments in one fixed direction. -/
def HasDirectionalLowerBound (f : E → ℝ) (v : E) (m : ℝ) : Prop :=
  ∀ x t, 0 ≤ t → f x + m * t ≤ f (x + t • v)

theorem clarkeQuotient_neg_le_of_lowerBound
    {f : E → ℝ} {v : E} {m : ℝ}
    (hf : HasDirectionalLowerBound f v m) {x : E} {t : ℝ} (ht : 0 < t) :
    clarkeQuotient f (-v) (x, t) ≤ ((-m : ℝ) : EReal) := by
  have h := hf (x + t • (-v)) t ht.le
  have hcancel : x + t • (-v) + t • v = x := by simp
  rw [hcancel] at h
  have hq : (f (x + t • (-v)) - f x) / t ≤ -m := by
    apply (div_le_iff₀ ht).2
    linarith
  simpa [clarkeQuotient, ht.ne'] using EReal.coe_le_coe_iff.mpr hq

/-- Directional monotonicity bounds the Clarke derivative in the opposite
direction. No differentiability assumption is needed for this implication. -/
theorem clarkeDirectional_neg_le_of_lowerBound
    {f : E → ℝ} {v : E} {m : ℝ}
    (hf : HasDirectionalLowerBound f v m) (x : E) :
    clarkeDirectional f x (-v) ≤ ((-m : ℝ) : EReal) := by
  have ht : ∀ᶠ p : E × ℝ in clarkeFilter x, 0 < p.2 := by
    exact (tendsto_snd : Tendsto (fun p : E × ℝ ↦ p.2)
      (clarkeFilter x) (nhdsWithin 0 (Ioi 0))) self_mem_nhdsWithin
  have hbound : ∀ᶠ p : E × ℝ in clarkeFilter x,
      clarkeQuotient f (-v) p ≤ ((-m : ℝ) : EReal) := by
    filter_upwards [ht] with p hp
    exact clarkeQuotient_neg_le_of_lowerBound hf hp
  exact Filter.limsup_le_of_le (h := hbound)

/-- Every genuine Clarke subgradient lies in the separating half-space. -/
theorem le_apply_of_mem_clarkeSubdifferential
    {f : E → ℝ} {v : E} {m : ℝ}
    (hf : HasDirectionalLowerBound f v m) {x : E} {L : E →L[ℝ] ℝ}
    (hL : L ∈ clarkeSubdifferential f x) : m ≤ L v := by
  have h := (hL (-v)).trans (clarkeDirectional_neg_le_of_lowerBound hf x)
  have hreal : L (-v) ≤ -m := EReal.coe_le_coe_iff.mp h
  simpa only [map_neg, neg_le_neg_iff] using hreal

/-- A strictly positive directional lower bound excludes Clarke stationarity. -/
theorem zero_not_mem_clarkeSubdifferential
    {f : E → ℝ} {v : E} {m : ℝ}
    (hf : HasDirectionalLowerBound f v m) (hm : 0 < m) (x : E) :
    (0 : E →L[ℝ] ℝ) ∉ clarkeSubdifferential f x := by
  intro h
  have hle := le_apply_of_mem_clarkeSubdifferential hf h
  simpa using (not_le_of_gt hm) hle

/-- Directional increment inequalities transport through linear coordinates.
This transfers the descent bound from the interpolation coordinates to
the coordinates of the BFGS orbit. -/
theorem HasDirectionalLowerBound.comp_linear
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : F → ℝ} {v : F} {m : ℝ}
    (hf : HasDirectionalLowerBound f v m)
    (A : E →L[ℝ] F) {w : E} (hw : A w = v) :
    HasDirectionalLowerBound (f ∘ A) w m := by
  intro x t ht
  simpa [Function.comp_def, map_add, map_smul, hw] using hf (A x) t ht

theorem tendsto_shift_clarkeFilter (x d : E) :
    Tendsto (fun p : E × ℝ ↦ p.1 + p.2 • d)
      (clarkeFilter x) (nhds x) := by
  have hx : Tendsto (fun p : E × ℝ ↦ p.1) (clarkeFilter x) (nhds x) :=
    tendsto_fst
  have ht : Tendsto (fun p : E × ℝ ↦ p.2) (clarkeFilter x) (nhds (0 : ℝ)) :=
    (tendsto_snd : Tendsto (fun p : E × ℝ ↦ p.2)
      (clarkeFilter x) (nhdsWithin 0 (Ioi 0))).mono_right nhdsWithin_le_nhds
  simpa using hx.add (ht.smul tendsto_const_nhds)

/-- The Clarke derivative depends only on the germ of a function. -/
theorem clarkeDirectional_congr_of_eventuallyEq
    {f g : E → ℝ} {x : E} (hfg : f =ᶠ[nhds x] g) (d : E) :
    clarkeDirectional f x d = clarkeDirectional g x d := by
  have hbase := (tendsto_fst : Tendsto (fun p : E × ℝ ↦ p.1)
    (clarkeFilter x) (nhds x)) hfg
  have hshift := tendsto_shift_clarkeFilter x d hfg
  apply Filter.limsup_congr
  filter_upwards [hbase, hshift] with p hp hq
  change f p.1 = g p.1 at hp
  change f (p.1 + p.2 • d) = g (p.1 + p.2 • d) at hq
  simp only [clarkeQuotient, hp, hq]

/-- In particular, a coercive modification away from a point preserves the
Clarke subdifferential at that point. -/
theorem clarkeSubdifferential_congr_of_eventuallyEq
    {f g : E → ℝ} {x : E} (hfg : f =ᶠ[nhds x] g) :
    clarkeSubdifferential f x = clarkeSubdifferential g x := by
  ext L
  simp only [clarkeSubdifferential, mem_ofPred_eq,
    clarkeDirectional_congr_of_eventuallyEq hfg]

end

end BFGS
