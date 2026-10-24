import BFGS.Counterexample.Extension
import BFGS.Counterexample.Neighborhood
import BFGS.Analysis.FixedScale

/-! Transfer of a homogeneous cycle basin to the coercive objective
and its actual derivative. The concrete basin is instantiated separately. -/
namespace BFGS.Counterexample
noncomputable section
open Algorithm CycleDynamics BFGS.StateSpace Filter Topology

/-- The parameter rectangle in Theorem 1.1:
`0 < c₁ ≤ 0.03 < 0.6 ≤ c₂ < 1`. -/
def Parameters (c₁ c₂ : ℝ) : Prop :=
  0 < c₁ ∧ c₁ ≤ 3/100 ∧ 3/5 ≤ c₂ ∧ c₂ < 1

/-- The actual classical derivative, represented as a coordinate gradient. -/
def actualGradient (f : Vec → ℝ) (x : Vec) : Vec :=
  ((fderiv ℝ f x) (1,0),(fderiv ℝ f x) (0,1))

theorem actualGradient_eq {f : Vec → ℝ} {g x : Vec} (h : IsGradientAt f g x) :
    actualGradient f x = g := by
  unfold actualGradient
  rw [h.fderiv]
  ext <;> simp [gradientFunctional]

/-- At differentiable endpoints the auxiliary gradient agrees with the actual one. -/
theorem stepAccepted_actualGradient (f : Vec → ℝ) (g : Vec → Vec)
    (c₁ c₂ : ℝ) (z : State) (ha : StepAccepted f g c₁ c₂ z)
    (h0 : IsGradientAt f (g (point z)) (point z))
    (h1 : IsGradientAt f (g (point (cycleStep g z))) (point (cycleStep g z))) :
    StepAccepted f (actualGradient f) c₁ c₂ z := by
  have hc := actualGradient_eq h0
  have hn := actualGradient_eq h1
  have hd : direction (actualGradient f) z = direction g z := by rw [direction,hc]; rfl
  have hp : point (cycleStep g z) = point z+direction g z := by
    simp [cycleStep,acceptedStep]
  rw [hp] at hn
  simpa only [StepAccepted,armijo,weakWolfe,hd,hc,one_smul,hn] using ha

theorem stepAccepted_gradient_ne (f : Vec → ℝ) (g : Vec → Vec)
    (c₁ c₂ : ℝ) (z : State) (ha : StepAccepted f g c₁ c₂ z) :
    g (point z) ≠ 0 := by
  intro hz
  have h := ha.1
  simp [armijo,direction,hz,Sym2.mulV,dot, ← Prod.zero_eq_mk] at h

theorem stepAccepted_curvature_pos (f : Vec → ℝ) (g : Vec → Vec)
    (c₁ c₂ : ℝ) (z : State) (ha : StepAccepted f g c₁ c₂ z)
    (hH : (metric z).Positive) (hc₂ : c₂ < 1) : 0 < curvature g 1 z := by
  exact weakWolfe_positive_curvature _ _ _ 1 c₂ (by norm_num) hc₂
    (direction_descent g z hH (stepAccepted_gradient_ne f g c₁ c₂ z ha)) ha.2

theorem canonical_run_of_cycle_orbit (f : Vec → ℝ) (g : Vec → Vec)
    (c₁ c₂ : ℝ) (z : State)
    (hl : ∀ n, StepAccepted f g c₁ c₂ ((cycleStep g)^[n] z))
    (hgrad : ∀ n, IsGradientAt f (g (point ((cycleStep g)^[n] z)))
      (point ((cycleStep g)^[n] z))) (fuel n : ℕ) :
    bfgsRun f (actualGradient f) c₁ c₂ (fuel+1) z n = some ((cycleStep g)^[n] z) := by
  have hc (k : ℕ) : actualGradient f (point ((cycleStep g)^[k] z)) =
      g (point ((cycleStep g)^[k] z)) := actualGradient_eq (hgrad k)
  have hstep (k : ℕ) : bfgsStep f (actualGradient f) c₁ c₂ (fuel+1)
      ((cycleStep g)^[k] z) = some (cycleStep g ((cycleStep g)^[k] z)) := by
    let w := (cycleStep g)^[k] z
    have hd : direction (actualGradient f) w = direction g w := by simp [direction, w, hc]
    have hcw : actualGradient f (point w) = g (point w) := hc k
    have hpw : point (cycleStep g w) = point w+direction g w := by
      simp [cycleStep, acceptedStep]
    have hn : actualGradient f (point w+direction g w) = g (point w+direction g w) := by
      have h := hc (k+1)
      rw [Function.iterate_succ_apply'] at h
      change actualGradient f (point (cycleStep g w)) = g (point (cycleStep g w)) at h
      rwa [hpw] at h
    have ha : StepAccepted f (actualGradient f) c₁ c₂ w := by
      have h := hl k
      change StepAccepted f g c₁ c₂ w at h
      simpa only [StepAccepted, weakWolfe, hd, hcw, one_smul, hn] using h
    rw [bfgsStep_eq_cycleStep f (actualGradient f) c₁ c₂ fuel w ha]
    congr 1
    change cycleStep (actualGradient f) w = cycleStep g w
    simp only [cycleStep, acceptedStep, hd, one_smul, hcw, hn]
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [bfgsRun, ih]
      simpa only [Option.bind_some, Function.iterate_succ_apply'] using hstep n

theorem stepAccepted_parameters (f : Vec → ℝ) (g : Vec → Vec) (z : State)
    (c₁ c₂ : ℝ) (hc : Parameters c₁ c₂)
    (hd : dot (g (point z)) (direction g z) < 0)
    (ha : StepAccepted f g (3/100) (3/5) z) : StepAccepted f g c₁ c₂ z := by
  dsimp [StepAccepted, armijo, weakWolfe] at ha ⊢
  simp only [one_smul, mul_one] at ha ⊢
  obtain ⟨_,hc₁,hc₂,_⟩ := hc
  exact ⟨by nlinarith [ha.1], by nlinarith [ha.2]⟩

private theorem scaled_point_bound (t : ℝ) (ht : 0 < t) (htb : t ≤ 1)
    (x : Vec) (hx : ‖x‖ < 4) : ‖t • x‖ < 4 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  nlinarith [norm_nonneg x]

private theorem squaredRadius_lt_of_norm_lt (x : Vec) (hx : ‖x‖ < 4) :
    squaredRadius x < 100 := by
  have ha := norm_fst_le x
  have hb := norm_snd_le x
  have ha' := mul_self_le_mul_self (norm_nonneg x.1) ha
  have hb' := mul_self_le_mul_self (norm_nonneg x.2) hb
  simp only [Real.norm_eq_abs, ← sq, sq_abs] at ha' hb'
  dsimp [squaredRadius]
  nlinarith [norm_nonneg x]

structure RunSafe (f : Vec → ℝ) (g : Vec → Vec) (c₁ c₂ : ℝ) (z : State) : Prop where
  positive : (metric z).Positive
  accepted : StepAccepted (radialExtension f) g c₁ c₂ z
  gradient : IsGradientAt (radialExtension f) (g (point z)) (point z)

theorem safe_scaled_phase (f : Vec → ℝ) (g : Vec → Vec) (S : Set Vec)
    (hSscale : ∀ t : ℝ, 0 < t → ∀ x ∈ S, t • x ∈ S)
    (hf : ∀ t : ℝ, 0 < t → ∀ x, f (t • x) = t*f x)
    (hg : ∀ t : ℝ, 0 < t → ∀ x, g (t • x) = g x)
    (hgradient : ∀ x ∈ S, IsGradientAt f (g x) x)
    (z : State) (hz : PhaseSafe f g (3/100) (3/5) S 4 z)
    (t : ℝ) (ht : 0 < t) (htb : t ≤ 1)
    (c₁ c₂ : ℝ) (hc : Parameters c₁ c₂) : RunSafe f g c₁ c₂ (t • z) := by
  have hg0 : g (point z) ≠ 0 := by
    intro h
    apply hz.curvature_ne
    simp [curvature, direction, h, Sym2.mulV, dot]
  have hd := direction_descent g z hz.metric_pos hg0
  have hacc := stepAccepted_parameters f g z c₁ c₂ hc hd hz.accepted
  have hscaled := (StepAccepted.scale_iff f g c₁ c₂ t ht z (hf t ht) (hg t ht)).mpr hacc
  have hpoint : squaredRadius (point (t • z)) < 100 :=
    squaredRadius_lt_of_norm_lt _ (scaled_point_bound t ht htb _ hz.point_bound)
  have hnext : squaredRadius (point (t • z)+direction g (t • z)) < 100 := by
    rw [point_smul, direction_scale g t z (hg t ht _), ← smul_add]
    exact squaredRadius_lt_of_norm_lt _ (scaled_point_bound t ht htb _ hz.next_bound)
  refine ⟨?_, ?_, ?_⟩
  · change ((metric z).scale t).Positive
    intro w hw
    have h := hz.metric_pos w hw
    have he : ((metric z).scale t).quad w = t*(metric z).quad w := by
      simp [Sym2.quad, Sym2.mulV, Sym2.scale, dot]; ring
    rw [he]
    exact mul_pos ht h
  · simp only [StepAccepted, armijo, one_smul] at hscaled ⊢
    rw [radialExtension_eq f hpoint.le, radialExtension_eq f hnext.le]
    exact hscaled
  · apply radialExtension_gradient f _ hpoint
    exact hgradient _ (hSscale t ht _ hz.point_mem)

/-- The invariant neighborhood for `r⁻¹ T⁴` itself is the initial set.
The phase identities in Section 2.4 give actual
BFGS runs, with no additional state-coordinate normalization. -/
theorem open_failure_of_cycle_basin
    (f : Vec → ℝ) (g : Vec → Vec) (S : Set Vec) (U : Set State)
    (hUo : IsOpen U) (hUne : U.Nonempty)
    (hSscale : ∀ t : ℝ, 0 < t → ∀ x ∈ S, t • x ∈ S)
    (hf : ∀ t : ℝ, 0 < t → ∀ x, f (t • x) = t*f x)
    (hg : ∀ t : ℝ, 0 < t → ∀ x, g (t • x) = g x)
    (hgradient : ∀ x ∈ S, IsGradientAt f (g x) x)
    (r M : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hU : Set.MapsTo (FixedScale.returnMap (cycleStep g) 4 r) U U)
    (hphase : ∀ w ∈ U, ∀ i : Fin 4, PhaseSafe f g (3/100) (3/5) S 4
      ((cycleStep g)^[i.val] w))
    (hbound : ∀ w ∈ U, ∀ i : Fin 4, ‖(cycleStep g)^[i.val] w‖ ≤ M) :
    ∃ B : Set State, IsOpen B ∧ B.Nonempty ∧ ∀ z ∈ B,
      ∃ orbit : ℕ → State,
        (∀ c₁ c₂, Parameters c₁ c₂ → ∀ fuel n,
          bfgsRun (radialExtension f) (actualGradient (radialExtension f))
            c₁ c₂ (fuel+1) z n = some (orbit n)) ∧
        (∀ n, (metric (orbit n)).Positive) ∧
        (∀ n, IsGradientAt (radialExtension f)
          (actualGradient (radialExtension f) (point (orbit n))) (point (orbit n))) ∧
        (∀ c₁ c₂, Parameters c₁ c₂ → ∀ n,
          StepAccepted (radialExtension f) (actualGradient (radialExtension f))
            c₁ c₂ (orbit n)) ∧
        Tendsto (fun n => point (orbit n)) atTop (𝓝 0) := by
  refine ⟨U,hUo,hUne,?_⟩
  intro z hz
  have hhom := acceptedStep_posHomogeneous g 1 hg
  have hsafe (c₁ c₂ : ℝ) (hc : Parameters c₁ c₂) (n : ℕ) :
      RunSafe f g c₁ c₂ ((cycleStep g)^[n] z) := by
    apply FixedScale.basin_all_iterates_le_one (cycleStep g) 4 r U
      (RunSafe f g c₁ c₂) (by norm_num) hr hr1.le hhom hU _ z hz n
    intro σ hσ hσb i hi w hw
    exact safe_scaled_phase f g S hSscale hf hg hgradient _ (hphase w hw ⟨i,hi⟩)
      σ hσ hσb c₁ c₂ hc
  have href : Parameters (1/100) (9/10) := by norm_num [Parameters]
  refine ⟨fun n => (cycleStep g)^[n] z, ?_, ?_, ?_, ?_, ?_⟩
  · intro c₁ c₂ hc fuel n
    exact canonical_run_of_cycle_orbit (radialExtension f) g c₁ c₂ z
      (fun k => (hsafe c₁ c₂ hc k).accepted)
      (fun k => (hsafe c₁ c₂ hc k).gradient) fuel n
  · intro n
    exact (hsafe _ _ href n).positive
  · intro n
    have h := (hsafe _ _ href n).gradient
    rw [actualGradient_eq h]
    exact h
  · intro c₁ c₂ hc n
    apply stepAccepted_actualGradient (radialExtension f) g c₁ c₂ _
      (hsafe c₁ c₂ hc n).accepted (hsafe c₁ c₂ hc n).gradient
    simpa only [Function.iterate_succ_apply'] using (hsafe c₁ c₂ hc (n+1)).gradient
  · have hconv : Tendsto (fun n => (cycleStep g)^[n] z) atTop (𝓝 0) :=
      FixedScale.basin_converges_from_initial_state (cycleStep g) 4 r M U
        (by norm_num) hr hr1 hhom hU (fun i hi w hw => hbound w hw ⟨i,hi⟩) z hz
    have hp : Continuous point := by unfold point; fun_prop
    have h := hp.continuousAt.tendsto.comp hconv
    rw [show point (0 : State) = (0 : Vec) from rfl] at h
    exact h

end
end BFGS.Counterexample
