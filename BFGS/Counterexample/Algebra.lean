import BFGS.Analysis.Algorithm

/-! The two-dimensional cycle data from Section 2.1.
The symmetric-matrix type and update are those of `BFGS.Algorithm`. -/
namespace BFGS.Counterexample
noncomputable section
open BFGS.Algorithm

def rho : ℝ := 8/9
def r : ℝ := 64/81

def p (b : ℝ) : ℝ := -9*(882*b^2 - 463*b - 256)/(640*(2*b-1))
def t (b : ℝ) : ℝ := -(3087*b^2 - 2233*b - 256)/(320*(2*b-1))
def q (b : ℝ) : ℝ := (15876*b^3 - 4316*b^2 - 6815*b - 2304)/(1280*b*(2*b-1))

/-- Multiplication by the manuscript's matrix J. -/
def jMul (b : ℝ) (v : Vec) : Vec :=
  (p b*v.1+t b*v.2, q b*v.1-p b*v.2)

/-- Multiplication by the transpose of J. -/
def jtMul (b : ℝ) (v : Vec) : Vec :=
  (p b*v.1+q b*v.2, t b*v.1-p b*v.2)

/-- The symmetric matrix rho Jᵀ H J, written by its three entries. -/
def transformH (b : ℝ) (H : Sym2) : Sym2 :=
  ⟨rho*(H.a*(p b)^2+2*H.b*p b*q b+H.d*(q b)^2),
   rho*(H.a*p b*t b+H.b*(q b*t b-(p b)^2)-H.d*p b*q b),
   rho*(H.a*(t b)^2-2*H.b*t b*p b+H.d*(p b)^2)⟩

def g0 : Vec := (1,0)
def g1 : Vec := (0,1)
def g2 (b : ℝ) : Vec := (p b,q b)
def g3 (b : ℝ) : Vec := (t b,-p b)
def g4 : Vec := g0

def H0 (b : ℝ) : Sym2 := ⟨1,1/2,b/4+1/8⟩
def H1 (b : ℝ) : Sym2 := ⟨b+3/2,b+1/2,b⟩
def H2 (b : ℝ) : Sym2 := transformH b (H0 b)
def H3 (b : ℝ) : Sym2 := transformH b (H1 b)
def H4 (b : ℝ) : Sym2 := (H0 b).scale r

def v0 (b : ℝ) : Vec := (b+3/2,b+1/2)
def x0 (b : ℝ) : Vec := (1-r)⁻¹ • (v0 b+rho • jtMul b (v0 b))
def x1 (b : ℝ) : Vec := x0 b-(1,1/2)
def x2 (b : ℝ) : Vec := rho • jtMul b (x0 b)
def x3 (b : ℝ) : Vec := rho • jtMul b (x1 b)
def x4 (b : ℝ) : Vec := r • x0 b

def s0 (b : ℝ) : Vec := -(H0 b).mulV g0
def s1 (b : ℝ) : Vec := -(H1 b).mulV g1
def s2 (b : ℝ) : Vec := -(H2 b).mulV (g2 b)
def s3 (b : ℝ) : Vec := -(H3 b).mulV (g3 b)

def y0 : Vec := g1-g0
def y1 (b : ℝ) : Vec := g2 b-g1
def y2 (b : ℝ) : Vec := g3 b-g2 b
def y3 (b : ℝ) : Vec := g4-g3 b

theorem rho_sq : rho^2 = r := by norm_num [rho,r]
theorem rho_pos : 0 < rho := by norm_num [rho]
theorem r_pos : 0 < r := by norm_num [r]
theorem r_lt_one : r < 1 := by norm_num [r]
theorem return_metric (b : ℝ) : H4 b = (H0 b).scale r := rfl
theorem return_position (b : ℝ) : x4 b = r • x0 b := rfl

theorem step0_explicit (b : ℝ) : s0 b = (-1,-1/2) := by
  norm_num [s0,H0,g0,Sym2.mulV]

theorem step1_explicit (b : ℝ) : s1 b = (-(b+1/2),-b) := by
  simp [s1,H1,g1,Sym2.mulV]

end
end BFGS.Counterexample
