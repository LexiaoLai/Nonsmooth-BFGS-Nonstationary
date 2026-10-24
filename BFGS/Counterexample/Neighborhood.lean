import BFGS.Analysis.LocalCycleNeighborhood

/-! Local safety and open invariant neighborhoods for the cycle map. -/
namespace BFGS.Counterexample.CycleDynamics
noncomputable section
open Algorithm BFGS.StateSpace Filter Topology

/-- The smooth cycle map uses trial length `1`; it agrees locally with BFGS
when the strict tests in `StepAccepted` hold. -/
def cycleStep (g : Vec → Vec) : State → State := acceptedStep g 1

def StepAccepted (f : Vec → ℝ) (g : Vec → Vec) (c₁ c₂ : ℝ) (z : State) : Prop :=
  armijo f (point z) (direction g z) (g (point z)) c₁ 1 ∧
    weakWolfe g (point z) (direction g z) c₂ 1

def armijoMargin (f : Vec → ℝ) (g : Vec → Vec) (c₁ : ℝ) (z : State) : ℝ :=
  f (point z)+c₁*dot (g (point z)) (direction g z)-f (point z+direction g z)

def wolfeMargin (g : Vec → Vec) (c₂ : ℝ) (z : State) : ℝ :=
  dot (g (point z+direction g z)) (direction g z)-
    c₂*dot (g (point z)) (direction g z)

theorem StepAccepted.of_margins (f : Vec → ℝ) (g : Vec → Vec)
    (c₁ c₂ : ℝ) (z : State)
    (ha : 0 < armijoMargin f g c₁ z) (hw : 0 < wolfeMargin g c₂ z) :
    StepAccepted f g c₁ c₂ z := by
  unfold StepAccepted armijo weakWolfe
  dsimp [armijoMargin, wolfeMargin] at ha hw
  simp only [one_smul, mul_one]
  exact ⟨by linarith, by linarith⟩

theorem lineSearch_accepts_first (f : Vec → ℝ) (g : Vec → Vec)
    (c₁ c₂ : ℝ) (z : State) (fuel : ℕ) (hz : StepAccepted f g c₁ c₂ z) :
    lineSearch f g (point z) (direction g z) c₁ c₂ (fuel+1) 0 none 1 = some 1 := by
  simp [lineSearch, hz.1, hz.2]

theorem bfgsStep_eq_cycleStep (f : Vec → ℝ) (g : Vec → Vec)
    (c₁ c₂ : ℝ) (fuel : ℕ) (z : State) (hz : StepAccepted f g c₁ c₂ z) :
    bfgsStep f g c₁ c₂ (fuel+1) z = some (cycleStep g z) := by
  simp [bfgsStep, lineSearch_accepts_first f g c₁ c₂ z fuel hz, cycleStep]

theorem bfgsRun_eq_cycleStep_iterate (f : Vec → ℝ) (g : Vec → Vec)
    (c₁ c₂ : ℝ) (fuel : ℕ) (z : State)
    (haccept : ∀ k, StepAccepted f g c₁ c₂ ((cycleStep g)^[k] z)) (n : ℕ) :
    bfgsRun f g c₁ c₂ (fuel+1) z n = some ((cycleStep g)^[n] z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [bfgsRun, ih]
      simpa only [Option.bind_some, Function.iterate_succ_apply'] using
        bfgsStep_eq_cycleStep f g c₁ c₂ fuel _ (haccept n)

theorem StepAccepted.scale_iff (f : Vec → ℝ) (g : Vec → Vec)
    (c₁ c₂ t : ℝ) (ht : 0 < t) (z : State)
    (hf : ∀ x, f (t • x) = t*f x) (hg : ∀ x, g (t • x) = g x) :
    StepAccepted f g c₁ c₂ (t • z) ↔ StepAccepted f g c₁ c₂ z := by
  exact and_congr (armijo_scale_iff f g c₁ 1 t z ht hf hg)
    (weakWolfe_scale_iff g c₂ 1 t z ht hg)

/-- Strict endpoint margins persist on a neighborhood of the current state. -/
theorem margins_eventually (f : Vec → ℝ) (g : Vec → Vec)
    (c₁ c₂ : ℝ) (z : State) (hf : Continuous f)
    (hg₀ : ContinuousAt g (point z))
    (hg₁ : ContinuousAt g (point z+direction g z))
    (ha : 0 < armijoMargin f g c₁ z) (hw : 0 < wolfeMargin g c₂ z) :
    ∀ᶠ w in 𝓝 z, 0 < armijoMargin f g c₁ w ∧ 0 < wolfeMargin g c₂ w := by
  have hp : ContinuousAt point z := by unfold point; fun_prop
  have hgp : ContinuousAt (fun w => g (point w)) z := hg₀.comp hp
  have hd := direction_continuousAt g z hg₀
  have hn : ContinuousAt (fun w => point w+direction g w) z := hp.add hd
  have hgn : ContinuousAt (fun w => g (point w+direction g w)) z := hg₁.comp (f := fun w => point w+direction g w) hn
  have hdot : ContinuousAt (fun w => dot (g (point w)) (direction g w)) z :=
    (hgp.fst.mul hd.fst).add (hgp.snd.mul hd.snd)
  have hdotn : ContinuousAt (fun w => dot (g (point w+direction g w)) (direction g w)) z :=
    (hgn.fst.mul hd.fst).add (hgn.snd.mul hd.snd)
  have hsf : ContinuousAt (fun w => f (point w)) z := hf.continuousAt.comp hp
  have hnf : ContinuousAt (fun w => f (point w+direction g w)) z := hf.continuousAt.comp hn
  have hac : ContinuousAt (armijoMargin f g c₁) z :=
    (hsf.add (continuousAt_const.mul hdot)).sub hnf
  have hwc : ContinuousAt (wolfeMargin g c₂) z := hdotn.sub (continuousAt_const.mul hdot)
  exact (hac.eventually_const_lt ha).and (hwc.eventually_const_lt hw)

structure PhaseCertificate (f : Vec → ℝ) (g : Vec → Vec)
    (c₁ c₂ : ℝ) (S : Set Vec) (R : ℝ) (z : State) : Prop where
  point_mem : point z ∈ S
  next_mem : point z+direction g z ∈ S
  metric_pos : (metric z).Positive
  armijo_margin : 0 < armijoMargin f g c₁ z
  wolfe_margin : 0 < wolfeMargin g c₂ z
  point_bound : ‖point z‖ < R
  next_bound : ‖point z+direction g z‖ < R
  curvature_ne : curvature g 1 z ≠ 0

structure PhaseSafe (f : Vec → ℝ) (g : Vec → Vec)
    (c₁ c₂ : ℝ) (S : Set Vec) (R : ℝ) (z : State) : Prop where
  point_mem : point z ∈ S
  next_mem : point z+direction g z ∈ S
  metric_pos : (metric z).Positive
  accepted : StepAccepted f g c₁ c₂ z
  point_bound : ‖point z‖ < R
  next_bound : ‖point z+direction g z‖ < R
  curvature_ne : curvature g 1 z ≠ 0

theorem phaseSafe_eventually (f : Vec → ℝ) (g : Vec → Vec)
    (c₁ c₂ : ℝ) (S : Set Vec) (R : ℝ) (z : State)
    (hf : Continuous f) (hS : IsOpen S)
    (hg : ∀ x ∈ S, DifferentiableAt ℝ g x)
    (hz : PhaseCertificate f g c₁ c₂ S R z) :
    ∀ᶠ w in 𝓝 z, PhaseSafe f g c₁ c₂ S R w := by
  have hp : ContinuousAt point z := by unfold point; fun_prop
  have hg₀ := (hg _ hz.point_mem).continuousAt
  have hg₁ := (hg _ hz.next_mem).continuousAt
  have hd := direction_continuousAt g z hg₀
  have hn : ContinuousAt (fun w => point w+direction g w) z := hp.add hd
  have hcurv : ContinuousAt (curvature g 1) z := by
    have hgn : ContinuousAt (fun w => g (point w+direction g w)) z := hg₁.comp (f := fun w => point w+direction g w) hn
    have hgc : ContinuousAt (fun w => g (point w)) z := hg₀.comp hp
    have hc : ContinuousAt (fun w => dot (direction g w)
        (g (point w+direction g w)-g (point w))) z :=
      (hd.fst.mul (hgn.fst.sub hgc.fst)).add (hd.snd.mul (hgn.snd.sub hgc.snd))
    change ContinuousAt (fun w => dot ((1 : ℝ) • direction g w)
      (g (point w+(1 : ℝ) • direction g w)-g (point w))) z
    simpa only [one_smul] using hc
  filter_upwards [hp.eventually (hS.mem_nhds hz.point_mem),
    hn.eventually (hS.mem_nhds hz.next_mem), LocalCycle.metric_positive_eventually z hz.metric_pos,
    margins_eventually f g c₁ c₂ z hf hg₀ hg₁ hz.armijo_margin hz.wolfe_margin,
    hp.norm.eventually_lt_const hz.point_bound, hn.norm.eventually_lt_const hz.next_bound,
    hcurv.eventually_ne hz.curvature_ne] with w hP hN hM hA hPB hNB hC
  exact ⟨hP,hN,hM,StepAccepted.of_margins f g c₁ c₂ w hA.1 hA.2,hPB,hNB,hC⟩

theorem cycleStep_differentiableAt_of_certificate
    (f : Vec → ℝ) (g : Vec → Vec) (c₁ c₂ : ℝ)
    (S : Set Vec) (R : ℝ) (z : State)
    (hg : ∀ x ∈ S, DifferentiableAt ℝ g x)
    (hz : PhaseCertificate f g c₁ c₂ S R z) :
    DifferentiableAt ℝ (cycleStep g) z := by
  apply acceptedStep_differentiableAt g 1 z (hg _ hz.point_mem)
  · simpa only [one_smul] using hg _ hz.next_mem
  · exact hz.curvature_ne

end
end BFGS.Counterexample.CycleDynamics
