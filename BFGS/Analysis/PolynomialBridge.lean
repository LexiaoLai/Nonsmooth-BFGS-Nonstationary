import BFGS.Analysis.Interpolation

/-!
# A polynomial monotone Hermite bridge

The derivative uses two positive polynomial endpoint layers and a positive
interior bump. Unlike a compactly supported cutoff construction, the
one-interval bridge is a single polynomial. The parameter `n` makes the
integrals of the endpoint layers arbitrarily small.
-/

namespace BFGS

noncomputable section

def bridgeLeft (n : ℕ) (m p P : ℝ) : ℝ := P + (n + 2 : ℝ) * (p - m)

def bridgeRight (n : ℕ) (m q Q : ℝ) : ℝ := Q - (n + 2 : ℝ) * (q - m)

def bridgeDerivative (n : ℕ) (m p q P Q c : ℝ) (x : ℝ) : ℝ :=
  m + (1 - x) ^ (n + 2) * ((p - m) + bridgeLeft n m p P * x) +
    x ^ (n + 2) * ((q - m) + bridgeRight n m q Q * (x - 1)) +
    c * x ^ 2 * (1 - x) ^ 2

def bridgePrimitive (n : ℕ) (m p q P Q c : ℝ) (x : ℝ) : ℝ :=
  m * x +
    ((p - m) + bridgeLeft n m p P) / (n + 3 : ℝ) *
      (1 - (1 - x) ^ (n + 3)) -
    bridgeLeft n m p P / (n + 4 : ℝ) * (1 - (1 - x) ^ (n + 4)) +
    ((q - m) - bridgeRight n m q Q) / (n + 3 : ℝ) * x ^ (n + 3) +
    bridgeRight n m q Q / (n + 4 : ℝ) * x ^ (n + 4) +
    c * (x ^ 3 / 3 - x ^ 4 / 2 + x ^ 5 / 5)

def bridgeBaseIntegral (n : ℕ) (m p q P Q : ℝ) : ℝ :=
  m + 2 * ((p - m) + (q - m)) / (n + 4 : ℝ) +
    (P - Q) / ((n + 3 : ℝ) * (n + 4 : ℝ))

theorem bridgeDerivative_lower (n : ℕ) {m p q P Q c x : ℝ}
    (hp : m ≤ p) (hq : m ≤ q) (hL : 0 ≤ bridgeLeft n m p P)
    (hR : bridgeRight n m q Q ≤ 0) (hc : 0 ≤ c)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    m ≤ bridgeDerivative n m p q P Q c x := by
  have hleft : 0 ≤ (1 - x) ^ (n + 2) * ((p - m) + bridgeLeft n m p P * x) :=
    mul_nonneg (pow_nonneg (by linarith) _) (by nlinarith)
  have hright : 0 ≤ x ^ (n + 2) * ((q - m) + bridgeRight n m q Q * (x - 1)) :=
    mul_nonneg (pow_nonneg hx0 _) (by nlinarith)
  have hbump : 0 ≤ c * x ^ 2 * (1 - x) ^ 2 := by positivity
  unfold bridgeDerivative
  linarith

@[simp] theorem bridgeDerivative_zero (n : ℕ) (m p q P Q c : ℝ) :
    bridgeDerivative n m p q P Q c 0 = p := by
  simp [bridgeDerivative]

@[simp] theorem bridgeDerivative_one (n : ℕ) (m p q P Q c : ℝ) :
    bridgeDerivative n m p q P Q c 1 = q := by
  simp [bridgeDerivative]

@[simp] theorem bridgePrimitive_zero (n : ℕ) (m p q P Q c : ℝ) :
    bridgePrimitive n m p q P Q c 0 = 0 := by
  simp [bridgePrimitive]

theorem bridgePrimitive_one (n : ℕ) (m p q P Q c : ℝ) :
    bridgePrimitive n m p q P Q c 1 = bridgeBaseIntegral n m p q P Q + c / 30 := by
  have h3 : (n + 3 : ℝ) ≠ 0 := by positivity
  have h4 : (n + 4 : ℝ) ≠ 0 := by positivity
  simp only [bridgePrimitive, bridgeBaseIntegral, bridgeLeft, bridgeRight,
    one_pow, sub_self, zero_pow (by omega : n + 3 ≠ 0),
    zero_pow (by omega : n + 4 ≠ 0), mul_one, sub_zero]
  field_simp
  ring

private theorem hasDerivAt_real_pow_succ (n : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ y ^ (n + 1)) ((n + 1 : ℝ) * x ^ n) x := by
  convert hasDerivAt_pow (n + 1) x using 1 <;> first | rfl | simp

private theorem hasDerivAt_one_sub_pow_succ (n : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ (1 - y) ^ (n + 1))
      (-((n + 1 : ℝ) * (1 - x) ^ n)) x := by
  have hsub : HasDerivAt (fun y : ℝ ↦ 1 - y) (-1) x := by
    simpa using (hasDerivAt_const x (1 : ℝ)).fun_sub (hasDerivAt_id x)
  have h := (hasDerivAt_real_pow_succ n (1 - x)).comp x hsub
  convert h using 1 <;> first | rfl | ring

private theorem hasDerivAt_one_sub_one_sub_pow_succ (n : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ 1 - (1 - y) ^ (n + 1))
      ((n + 1 : ℝ) * (1 - x) ^ n) x := by
  simpa using (hasDerivAt_const x (1 : ℝ)).fun_sub
    (hasDerivAt_one_sub_pow_succ n x)

/-- The primitive displayed above differentiates to the positive endpoint
layers and interior bump, for every real argument. -/
theorem hasDerivAt_bridgePrimitive (n : ℕ) (m p q P Q c x : ℝ) :
    HasDerivAt (bridgePrimitive n m p q P Q c)
      (bridgeDerivative n m p q P Q c x) x := by
  have h3 : (n + 3 : ℝ) ≠ 0 := by positivity
  have h4 : (n + 4 : ℝ) ≠ 0 := by positivity
  have hL3 := (hasDerivAt_one_sub_one_sub_pow_succ (n + 2) x).const_smul
    (((p - m) + bridgeLeft n m p P) / (n + 3 : ℝ))
  have hL4 := (hasDerivAt_one_sub_one_sub_pow_succ (n + 3) x).const_smul
    (bridgeLeft n m p P / (n + 4 : ℝ))
  have hR3 := (hasDerivAt_real_pow_succ (n + 2) x).const_smul
    (((q - m) - bridgeRight n m q Q) / (n + 3 : ℝ))
  have hR4 := (hasDerivAt_real_pow_succ (n + 3) x).const_smul
    (bridgeRight n m q Q / (n + 4 : ℝ))
  have hB3 := (hasDerivAt_real_pow_succ 2 x).const_smul (1 / 3 : ℝ)
  have hB4 := (hasDerivAt_real_pow_succ 3 x).const_smul (1 / 2 : ℝ)
  have hB5 := (hasDerivAt_real_pow_succ 4 x).const_smul (1 / 5 : ℝ)
  have hB := ((hB3.fun_sub hB4).fun_add hB5).const_smul c
  have h := ((((hasDerivAt_const_mul m).fun_add hL3).fun_sub hL4).fun_add
    hR3).fun_add hR4 |>.fun_add hB
  convert h using 1
  · rfl
  · rfl
  · funext t
    simp only [bridgePrimitive, Pi.smul_apply, smul_eq_mul]
    ring
  · simp only [bridgeDerivative, smul_eq_mul, Nat.cast_add, Nat.cast_ofNat]
    field_simp
    simp only [pow_succ]
    ring

def bridgeSecondDerivative (n : ℕ) (m p q P Q c : ℝ) (x : ℝ) : ℝ :=
  -((n + 2 : ℝ) * (1 - x) ^ (n + 1)) *
      ((p - m) + bridgeLeft n m p P * x) +
    (1 - x) ^ (n + 2) * bridgeLeft n m p P +
    (n + 2 : ℝ) * x ^ (n + 1) *
      ((q - m) + bridgeRight n m q Q * (x - 1)) +
    x ^ (n + 2) * bridgeRight n m q Q +
    c * (2 * x) * (1 - x) ^ 2 - c * x ^ 2 * (2 * (1 - x))

theorem hasDerivAt_bridgeDerivative (n : ℕ) (m p q P Q c x : ℝ) :
    HasDerivAt (bridgeDerivative n m p q P Q c)
      (bridgeSecondDerivative n m p q P Q c x) x := by
  have hCL : HasDerivAt (fun t : ℝ ↦ (p - m) + bridgeLeft n m p P * t)
      (bridgeLeft n m p P) x :=
    (hasDerivAt_const_mul (bridgeLeft n m p P)).const_add (p - m)
  have hCR : HasDerivAt (fun t : ℝ ↦ (q - m) + bridgeRight n m q Q * (t - 1))
      (bridgeRight n m q Q) x := by
    convert (((hasDerivAt_id x).sub_const 1).const_smul
      (bridgeRight n m q Q)).const_add (q - m) using 1 <;>
      first | rfl | simp [smul_eq_mul]
  have hL := (hasDerivAt_one_sub_pow_succ (n + 1) x).mul hCL
  have hR := (hasDerivAt_real_pow_succ (n + 1) x).mul hCR
  have hB := (((hasDerivAt_real_pow_succ 1 x).const_smul c).mul
    (hasDerivAt_one_sub_pow_succ 1 x))
  have h := (((hasDerivAt_const x m).fun_add hL).fun_add hR).fun_add hB
  convert h using 1 <;> try rfl
  simp only [bridgeSecondDerivative, Pi.smul_apply, smul_eq_mul, Nat.cast_add]
  ring

@[simp] theorem bridgeSecondDerivative_zero (n : ℕ) (m p q P Q c : ℝ) :
    bridgeSecondDerivative n m p q P Q c 0 = P := by
  simp [bridgeSecondDerivative, bridgeLeft]
  ring

@[simp] theorem bridgeSecondDerivative_one (n : ℕ) (m p q P Q c : ℝ) :
    bridgeSecondDerivative n m p q P Q c 1 = Q := by
  simp [bridgeSecondDerivative, bridgeRight]

/-- Large powers make the endpoint layers positive and their combined
integral smaller than any prescribed positive excess over the slope floor. -/
theorem exists_bridge_degree {m p q P Q Δ : ℝ}
    (hp : m < p) (hq : m < q) (hΔ : m < Δ) :
    ∃ n : ℕ, 0 ≤ bridgeLeft n m p P ∧ bridgeRight n m q Q ≤ 0 ∧
      bridgeBaseIntegral n m p q P Q < Δ := by
  let C := 2 * ((p - m) + (q - m)) + |P - Q|
  obtain ⟨n, hn⟩ := exists_nat_gt
    (max ((-P) / (p - m)) (max (Q / (q - m)) (C / (Δ - m))))
  have hnL : (-P) / (p - m) < (n : ℝ) :=
    lt_of_le_of_lt (le_max_left _ _) hn
  have hnR : Q / (q - m) < (n : ℝ) :=
    lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hn
  have hnC : C / (Δ - m) < (n : ℝ) :=
    lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hn
  have hp0 : 0 < p - m := sub_pos.mpr hp
  have hq0 : 0 < q - m := sub_pos.mpr hq
  have hΔ0 : 0 < Δ - m := sub_pos.mpr hΔ
  have hL := (div_lt_iff₀ hp0).mp hnL
  have hR := (div_lt_iff₀ hq0).mp hnR
  have hC := (div_lt_iff₀ hΔ0).mp hnC
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h3 : (0 : ℝ) < n + 3 := by positivity
  have h4 : (0 : ℝ) < n + 4 := by positivity
  have hterm : (P - Q) / ((n + 3 : ℝ) * (n + 4 : ℝ)) ≤
      |P - Q| / (n + 4 : ℝ) := by
    apply (div_le_iff₀ (mul_pos h3 h4)).2
    calc
      P - Q ≤ |P - Q| := le_abs_self _
      _ ≤ |P - Q| * (n + 3 : ℝ) := by nlinarith [abs_nonneg (P - Q)]
      _ = (|P - Q| / (n + 4 : ℝ)) * ((n + 3 : ℝ) * (n + 4 : ℝ)) := by
        field_simp
  have hbase : bridgeBaseIntegral n m p q P Q ≤ m + C / (n + 4 : ℝ) := by
    dsimp [bridgeBaseIntegral, C]
    rw [add_div]
    linarith
  have hsmall : C / (n + 4 : ℝ) < Δ - m := by
    apply (div_lt_iff₀ h4).2
    nlinarith
  refine ⟨n, ?_, ?_, ?_⟩
  · unfold bridgeLeft
    nlinarith
  · unfold bridgeRight
    nlinarith
  · linarith

/-- Existence of an explicit polynomial primitive with the prescribed
increment, endpoint slopes, arbitrary endpoint second derivatives, and a
positive derivative floor on the whole interval. -/
theorem exists_monotone_twoJet_bridge {m p q P Q Δ : ℝ}
    (hp : m < p) (hq : m < q) (hΔ : m < Δ) :
    ∃ n : ℕ, ∃ c : ℝ, 0 < c ∧
      bridgePrimitive n m p q P Q c 0 = 0 ∧
      bridgePrimitive n m p q P Q c 1 = Δ ∧
      bridgeDerivative n m p q P Q c 0 = p ∧
      bridgeDerivative n m p q P Q c 1 = q ∧
      bridgeSecondDerivative n m p q P Q c 0 = P ∧
      bridgeSecondDerivative n m p q P Q c 1 = Q ∧
      (∀ x, HasDerivAt (bridgePrimitive n m p q P Q c)
        (bridgeDerivative n m p q P Q c x) x) ∧
      (∀ x, HasDerivAt (bridgeDerivative n m p q P Q c)
        (bridgeSecondDerivative n m p q P Q c x) x) ∧
      (∀ x ∈ Set.Icc (0 : ℝ) 1, m ≤ bridgeDerivative n m p q P Q c x) := by
  obtain ⟨n, hL, hR, hbase⟩ := exists_bridge_degree hp hq hΔ
  let c := 30 * (Δ - bridgeBaseIntegral n m p q P Q)
  have hc : 0 < c := by dsimp [c]; linarith
  refine ⟨n, c, hc, bridgePrimitive_zero .., ?_, bridgeDerivative_zero ..,
    bridgeDerivative_one .., bridgeSecondDerivative_zero .., bridgeSecondDerivative_one ..,
    hasDerivAt_bridgePrimitive n m p q P Q c,
    hasDerivAt_bridgeDerivative n m p q P Q c, ?_⟩
  · rw [bridgePrimitive_one]
    dsimp [c]
    ring
  · intro x hx
    exact bridgeDerivative_lower n hp.le hq.le hL hR hc.le hx.1 hx.2

/-- The preceding displayed primitive is literally a polynomial, with no
integration or function-existence oracle hidden in its definition. -/
def bridgePolynomial (n : ℕ) (m p q P Q c : ℝ) : Polynomial ℝ :=
  let X := Polynomial.X
  let C := Polynomial.C
  C m * X +
    C (((p - m) + bridgeLeft n m p P) / (n + 3 : ℝ)) * (1 - (1 - X) ^ (n + 3)) -
    C (bridgeLeft n m p P / (n + 4 : ℝ)) * (1 - (1 - X) ^ (n + 4)) +
    C (((q - m) - bridgeRight n m q Q) / (n + 3 : ℝ)) * X ^ (n + 3) +
    C (bridgeRight n m q Q / (n + 4 : ℝ)) * X ^ (n + 4) +
    C c * (C (1 / 3) * X ^ 3 - C (1 / 2) * X ^ 4 + C (1 / 5) * X ^ 5)

@[simp] theorem bridgePolynomial_eval (n : ℕ) (m p q P Q c x : ℝ) :
    (bridgePolynomial n m p q P Q c).eval x = bridgePrimitive n m p q P Q c x := by
  simp only [bridgePolynomial, bridgePrimitive, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one,
    Polynomial.eval_pow]
  ring

@[simp] theorem bridgePolynomial_derivative_eval (n : ℕ) (m p q P Q c x : ℝ) :
    (bridgePolynomial n m p q P Q c).derivative.eval x =
      bridgeDerivative n m p q P Q c x := by
  have h : HasDerivAt (bridgePrimitive n m p q P Q c)
      ((bridgePolynomial n m p q P Q c).derivative.eval x) x := by
    convert (bridgePolynomial n m p q P Q c).hasDerivAt x using 1 <;> try rfl
    funext t
    exact (bridgePolynomial_eval n m p q P Q c t).symm
  exact h.unique (hasDerivAt_bridgePrimitive n m p q P Q c x)

@[simp] theorem bridgePolynomial_second_derivative_eval (n : ℕ) (m p q P Q c x : ℝ) :
    (bridgePolynomial n m p q P Q c).derivative.derivative.eval x =
      bridgeSecondDerivative n m p q P Q c x := by
  have h : HasDerivAt (bridgeDerivative n m p q P Q c)
      ((bridgePolynomial n m p q P Q c).derivative.derivative.eval x) x := by
    convert (bridgePolynomial n m p q P Q c).derivative.hasDerivAt x using 1 <;> try rfl
    funext t
    exact (bridgePolynomial_derivative_eval n m p q P Q c t).symm
  exact h.unique (hasDerivAt_bridgeDerivative n m p q P Q c x)

/-- A polynomial monotone two-jet interpolant exists on the unit interval. -/
theorem exists_polynomial_monotone_twoJet_unit {m p q P Q Δ : ℝ}
    (hp : m < p) (hq : m < q) (hΔ : m < Δ) :
    ∃ H : Polynomial ℝ,
      H.eval 0 = 0 ∧ H.eval 1 = Δ ∧
      H.derivative.eval 0 = p ∧ H.derivative.eval 1 = q ∧
      H.derivative.derivative.eval 0 = P ∧ H.derivative.derivative.eval 1 = Q ∧
      ∀ x ∈ Set.Icc (0 : ℝ) 1, m ≤ H.derivative.eval x := by
  obtain ⟨n, c, _, h0, h1, hp0, hq1, hP0, hQ1, _, _, hbound⟩ :=
    exists_monotone_twoJet_bridge hp hq hΔ
  refine ⟨bridgePolynomial n m p q P Q c, ?_⟩
  simpa only [bridgePolynomial_eval, bridgePolynomial_derivative_eval,
    bridgePolynomial_second_derivative_eval] using
    And.intro h0 (And.intro h1 (And.intro hp0 (And.intro hq1 (And.intro hP0
      (And.intro hQ1 hbound)))))

def rescalePolynomial (K : Polynomial ℝ) (a A L : ℝ) : Polynomial ℝ :=
  Polynomial.C A + K.comp (Polynomial.C (1 / L) * (Polynomial.X - Polynomial.C a))

@[simp] theorem rescalePolynomial_eval (K : Polynomial ℝ) (a A L x : ℝ) :
    (rescalePolynomial K a A L).eval x = A + K.eval ((x - a) / L) := by
  simp [rescalePolynomial, div_eq_mul_inv, mul_comm]

@[simp] theorem rescalePolynomial_derivative_eval (K : Polynomial ℝ) (a A L x : ℝ) :
    (rescalePolynomial K a A L).derivative.eval x = K.derivative.eval ((x - a) / L) / L := by
  simp [rescalePolynomial, Polynomial.derivative_comp, Polynomial.derivative_mul,
    div_eq_mul_inv, mul_comm]

@[simp] theorem rescalePolynomial_second_derivative_eval
    (K : Polynomial ℝ) (a A L x : ℝ) :
    (rescalePolynomial K a A L).derivative.derivative.eval x =
      K.derivative.derivative.eval ((x - a) / L) / L ^ 2 := by
  simp [rescalePolynomial, Polynomial.derivative_comp, Polynomial.derivative_mul,
    div_eq_mul_inv, pow_two]
  ring

/-- A single polynomial matches arbitrary increasing endpoint values,
positive endpoint slopes and arbitrary endpoint curvatures on an arbitrary
nondegenerate interval, while retaining the requested derivative floor. -/
theorem exists_polynomial_monotone_twoJet
    {a b A B m p q P Q : ℝ} (hab : a < b)
    (hp : m < p) (hq : m < q) (hAB : m * (b - a) < B - A) :
    ∃ H : Polynomial ℝ,
      H.eval a = A ∧ H.eval b = B ∧
      H.derivative.eval a = p ∧ H.derivative.eval b = q ∧
      H.derivative.derivative.eval a = P ∧ H.derivative.derivative.eval b = Q ∧
      ∀ x ∈ Set.Icc a b, m ≤ H.derivative.eval x := by
  let L := b - a
  have hL : 0 < L := sub_pos.mpr hab
  obtain ⟨K, hK0, hK1, hp0, hq1, hP0, hQ1, hbound⟩ :=
    exists_polynomial_monotone_twoJet_unit
      (p := p * L) (q := q * L) (P := P * L ^ 2) (Q := Q * L ^ 2)
      (mul_lt_mul_of_pos_right hp hL) (mul_lt_mul_of_pos_right hq hL) hAB
  refine ⟨rescalePolynomial K a A L, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hK0]
  · simp [L, hL.ne', hK1]
  · simp [hp0, hL.ne']
  · simp [L, hL.ne', hq1]
  · simp [hP0, hL.ne']
  · simp [L, hL.ne', hQ1]
  · intro x hx
    have hx0 : 0 ≤ (x - a) / L := div_nonneg (sub_nonneg.mpr hx.1) hL.le
    have hx1 : (x - a) / L ≤ 1 := by
      apply (div_le_iff₀ hL).2
      dsimp [L]
      linarith [hx.2]
    have hh := hbound ((x - a) / L) ⟨hx0, hx1⟩
    rw [rescalePolynomial_derivative_eval]
    exact (le_div_iff₀ hL).2 hh

end

end BFGS
