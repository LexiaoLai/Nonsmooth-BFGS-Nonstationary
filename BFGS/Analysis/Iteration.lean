import BFGS.Analysis.Algorithm

/-! The five-coordinate BFGS state, accepted-step maps, and their agreement
with the Armijo–Wolfe line search. -/
namespace BFGS.Algorithm
noncomputable section
open Classical

abbrev State := Fin 5 → ℝ

def point (z : State) : Vec := (z 0,z 1)
def metric (z : State) : Sym2 := ⟨z 2,z 3,z 4⟩
def pack (x : Vec) (H : Sym2) : State := ![x.1,x.2,H.a,H.b,H.d]
def direction (g : Vec → Vec) (z : State) : Vec := -(metric z).mulV (g (point z))

def acceptedStep (g : Vec → Vec) (α : ℝ) (z : State) : State :=
  let s := α • direction g z
  let x' := point z+s
  pack x' (update (metric z) s (g x'-g (point z)))

def halfStep (g : Vec → Vec) : State → State := acceptedStep g (1/2)

def curvature (g : Vec → Vec) (α : ℝ) (z : State) : ℝ :=
  dot (α • direction g z) (g (point z+α • direction g z)-g (point z))

/-- The two strict tests which force the actual line search to return one half. -/
def HalfAccepted (f : Vec → ℝ) (g : Vec → Vec) (c₁ c₂ : ℝ) (z : State) : Prop :=
  ¬ armijo f (point z) (direction g z) (g (point z)) c₁ 1 ∧
  armijo f (point z) (direction g z) (g (point z)) c₁ (1/2) ∧
  weakWolfe g (point z) (direction g z) c₂ (1/2)

def bfgsStep (f : Vec → ℝ) (g : Vec → Vec) (c₁ c₂ : ℝ)
    (fuel : ℕ) (z : State) : Option State :=
  (lineSearch f g (point z) (direction g z) c₁ c₂ fuel 0 none 1).map
    (fun α => acceptedStep g α z)

theorem bfgsStep_eq_halfStep (f : Vec → ℝ) (g : Vec → Vec)
    (c₁ c₂ : ℝ) (fuel : ℕ) (z : State) (hz : HalfAccepted f g c₁ c₂ z) :
    bfgsStep f g c₁ c₂ (fuel+2) z = some (halfStep g z) := by
  rw [bfgsStep,lineSearch_halfstep f g (point z) (direction g z) c₁ c₂ fuel
    hz.1 hz.2.1 hz.2.2]
  rfl

/-- A failed line search propagates as `none`; an accepted step uses the
ordinary inverse-BFGS update. -/
def bfgsRun (f : Vec → ℝ) (g : Vec → Vec) (c₁ c₂ : ℝ) (fuel : ℕ)
    (z : State) : ℕ → Option State
  | 0 => some z
  | n+1 => (bfgsRun f g c₁ c₂ fuel z n).bind (bfgsStep f g c₁ c₂ fuel)

theorem bfgsRun_eq_halfStep_iterate (f : Vec → ℝ) (g : Vec → Vec)
    (c₁ c₂ : ℝ) (fuel : ℕ) (z : State)
    (h : ∀ n, HalfAccepted f g c₁ c₂ ((halfStep g)^[n] z)) :
    ∀ n, bfgsRun f g c₁ c₂ (fuel+2) z n = some ((halfStep g)^[n] z) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [bfgsRun,ih]
    simp only [Option.bind_some,Function.iterate_succ_apply']
    exact bfgsStep_eq_halfStep f g c₁ c₂ fuel _ (h n)

@[simp] theorem point_pack (x : Vec) (H : Sym2) : point (pack x H) = x := by
  rcases x with ⟨x,y⟩
  rfl

@[simp] theorem metric_pack (x : Vec) (H : Sym2) : metric (pack x H) = H := by
  rcases H
  rfl

@[simp] theorem point_smul (t : ℝ) (z : State) : point (t • z) = t • point z := rfl

@[simp] theorem metric_smul (t : ℝ) (z : State) :
    metric (t • z) = (metric z).scale t := rfl

theorem pack_scale (t : ℝ) (x : Vec) (H : Sym2) :
    pack (t • x) (H.scale t) = t • pack x H := by
  ext i
  fin_cases i <;> rfl

theorem direction_scale (g : Vec → Vec) (t : ℝ) (z : State)
    (hg : g (t • point z) = g (point z)) :
    direction g (t • z) = t • direction g z := by
  simp only [direction,point_smul,metric_smul,hg]
  apply Prod.ext <;> simp [Sym2.mulV,Sym2.scale] <;> ring

theorem acceptedStep_scale (g : Vec → Vec) (α t : ℝ) (z : State)
    (ht : t ≠ 0) (hc : curvature g α z ≠ 0)
    (hg : ∀ x, g (t • x) = g x) :
    acceptedStep g α (t • z) = t • acceptedStep g α z := by
  have hd := direction_scale g t z (hg _)
  have hs : α • direction g (t • z) = t • (α • direction g z) := by
    rw [hd,smul_comm]
  simp only [acceptedStep,point_smul,metric_smul,hs,← smul_add,hg]
  rw [update_scale _ _ _ t ht hc,pack_scale]

theorem acceptedStep_scale_total (g : Vec → Vec) (α t : ℝ) (z : State)
    (ht : t ≠ 0) (hg : ∀ x, g (t • x) = g x) :
    acceptedStep g α (t • z) = t • acceptedStep g α z := by
  have hd := direction_scale g t z (hg _)
  have hs : α • direction g (t • z) = t • (α • direction g z) := by
    rw [hd,smul_comm]
  simp only [acceptedStep,point_smul,metric_smul,hs,← smul_add,hg]
  rw [update_scale_total _ _ _ t ht,pack_scale]

theorem acceptedStep_zero (g : Vec → Vec) (α : ℝ) : acceptedStep g α 0 = 0 := by
  ext i
  fin_cases i <;> simp [acceptedStep,direction,point,metric,Sym2.mulV,
    pack,update,dot]

theorem acceptedStep_posHomogeneous (g : Vec → Vec) (α : ℝ)
    (hg : ∀ t : ℝ, 0 < t → ∀ x, g (t • x) = g x) :
    ∀ t : ℝ, 0 ≤ t → ∀ z, acceptedStep g α (t • z) = t • acceptedStep g α z := by
  intro t ht z
  rcases eq_or_lt_of_le ht with he | hp
  · subst t
    simp [acceptedStep_zero]
  · exact acceptedStep_scale_total g α t z hp.ne' (hg t hp)

theorem armijo_scale_iff (f : Vec → ℝ) (g : Vec → Vec)
    (c₁ α t : ℝ) (z : State) (ht : 0 < t)
    (hf : ∀ x, f (t • x) = t*f x) (hg : ∀ x, g (t • x) = g x) :
    armijo f (point (t • z)) (direction g (t • z)) (g (point (t • z))) c₁ α ↔
    armijo f (point z) (direction g z) (g (point z)) c₁ α := by
  rw [direction_scale g t z (hg _),point_smul,hg]
  unfold armijo
  rw [smul_comm α t,← smul_add,hf,hf]
  have he : dot (g (point z)) (t • direction g z) =
      t * dot (g (point z)) (direction g z) := by simp [dot]; ring
  rw [he]
  have ha : t*f (point z)+c₁*α*(t*dot (g (point z)) (direction g z)) =
      t*(f (point z)+c₁*α*dot (g (point z)) (direction g z)) := by ring
  rw [ha,mul_lt_mul_iff_right₀ ht]

theorem weakWolfe_scale_iff (g : Vec → Vec)
    (c₂ α t : ℝ) (z : State) (ht : 0 < t)
    (hg : ∀ x, g (t • x) = g x) :
    weakWolfe g (point (t • z)) (direction g (t • z)) c₂ α ↔
    weakWolfe g (point z) (direction g z) c₂ α := by
  rw [direction_scale g t z (hg _),point_smul]
  unfold weakWolfe
  rw [smul_comm α t,← smul_add,hg,hg]
  have he (a b : Vec) : dot a (t • b) = t*dot a b := by simp [dot]; ring
  simp only [he]
  rw [show c₂*(t*dot (g (point z)) (direction g z)) =
    t*(c₂*dot (g (point z)) (direction g z)) by ring,mul_lt_mul_iff_right₀ ht]

theorem HalfAccepted.scale_iff (f : Vec → ℝ) (g : Vec → Vec)
    (c₁ c₂ t : ℝ) (z : State) (ht : 0 < t)
    (hf : ∀ x, f (t • x) = t*f x) (hg : ∀ x, g (t • x) = g x) :
    HalfAccepted f g c₁ c₂ (t • z) ↔ HalfAccepted f g c₁ c₂ z := by
  simp only [HalfAccepted,armijo_scale_iff f g c₁ 1 t z ht hf hg,
    armijo_scale_iff f g c₁ (1/2) t z ht hf hg,
    weakWolfe_scale_iff g c₂ (1/2) t z ht hg]

theorem direction_descent (g : Vec → Vec) (z : State)
    (hH : (metric z).Positive) (hg : g (point z) ≠ 0) :
    dot (g (point z)) (direction g z) < 0 := by
  have h := hH _ hg
  have he : dot (g (point z)) (direction g z) = -(metric z).quad (g (point z)) := by
    simp [dot,direction,Sym2.quad]
    ring
  rw [he]
  linarith

theorem halfStep_positive (f : Vec → ℝ) (g : Vec → Vec)
    (c₁ c₂ : ℝ) (z : State) (hc₂ : c₂ < 1)
    (hz : HalfAccepted f g c₁ c₂ z)
    (hH : (metric z).Positive) (hg : g (point z) ≠ 0) :
    (metric (halfStep g z)).Positive := by
  have hc := weakWolfe_positive_curvature (g (point z))
    (g (point z+(1/2 : ℝ) • direction g z)) (direction g z) (1/2) c₂
    (by norm_num) hc₂ (direction_descent g z hH hg) hz.2.2
  simp only [halfStep,acceptedStep,metric_pack]
  exact update_positive _ _ _ hH hc

theorem acceptedStep_differentiableAt (g : Vec → Vec) (α : ℝ) (z : State)
    (hg₀ : DifferentiableAt ℝ g (point z))
    (hg₁ : DifferentiableAt ℝ g (point z+α • direction g z))
    (hc : curvature g α z ≠ 0) :
    DifferentiableAt ℝ (acceptedStep g α) z := by
  have hp : DifferentiableAt ℝ point z := by unfold point; fun_prop
  have hg : DifferentiableAt ℝ (fun q => g (point q)) z := hg₀.comp z hp
  have hd : DifferentiableAt ℝ (direction g) z := by
    unfold direction metric Sym2.mulV
    fun_prop
  have hs : DifferentiableAt ℝ (fun q => α • direction g q) z := by fun_prop
  have hx : DifferentiableAt ℝ (fun q => point q+α • direction g q) z := by fun_prop
  have hgn : DifferentiableAt ℝ (fun q => g (point q+α • direction g q)) z :=
    hg₁.comp z hx
  have hy : DifferentiableAt ℝ
      (fun q => g (point q+α • direction g q)-g (point q)) z := by fun_prop
  have hcurv : DifferentiableAt ℝ (curvature g α) z := by
    unfold curvature dot
    fun_prop
  have hi : DifferentiableAt ℝ (fun q => (curvature g α q)⁻¹) z :=
    hcurv.inv hc
  apply differentiableAt_pi.2
  intro i
  fin_cases i <;> dsimp [acceptedStep,pack,update,metric,Sym2.mulV,dot]
  all_goals
    change DifferentiableAt ℝ _ z
    try simp only [div_eq_mul_inv]
    fun_prop

end
theorem direction_continuousAt (g : Vec → Vec) (z : State)
    (hg : ContinuousAt g (point z)) : ContinuousAt (direction g) z := by
  have hp : ContinuousAt point z := by unfold point; fun_prop
  have hgp : ContinuousAt (fun q => g (point q)) z := hg.comp hp
  have h₂ : ContinuousAt (fun q : State => q 2) z := (continuous_apply 2).continuousAt
  have h₃ : ContinuousAt (fun q : State => q 3) z := (continuous_apply 3).continuousAt
  have h₄ : ContinuousAt (fun q : State => q 4) z := (continuous_apply 4).continuousAt
  exact ((h₂.mul hgp.fst |>.add (h₃.mul hgp.snd)).prodMk
    (h₃.mul hgp.fst |>.add (h₄.mul hgp.snd))).neg

end BFGS.Algorithm
