import BFGS.Counterexample.Cycle
import BFGS.Counterexample.Certificates.IntervalTrace4

/-! Semantic identification of the rational trace with the manuscript cycle.
These equalities connect the generated arithmetic to the actual cycle data;
none of the interval bounds is taken as an external assumption. -/
namespace BFGS.Counterexample
noncomputable section
open BFGS.Algorithm Trace
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.vecHead Matrix.vecTail
@[local simp] private theorem vector_five_four {α : Type*} (a b c d e : α) :
    (![a,b,c,d,e] : Fin 5 → α) 4 = e := rfl
@[local simp] private theorem castSucc_two : (2 : Fin 4).castSucc = (2 : Fin 5) := rfl
@[local simp] private theorem castSucc_three : (3 : Fin 4).castSucc = (3 : Fin 5) := rfl


theorem trace_n0 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n0 b = b := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n0]
  <;> ring_nf <;> simp

theorem trace_n15 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n15 b = 1 := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n15, rho, r]
  <;> ring_nf <;> simp

theorem trace_n66 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n66 b = 0 := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n66, rho, r]
  <;> ring_nf <;> simp

theorem trace_n64 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n64 b = 1/2 := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n64, rho, r]
  <;> ring_nf <;> simp

theorem trace_n89 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n89 b = rho := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n89, rho, r]
  <;> ring_nf <;> simp

theorem trace_n122 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n122 b = r := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n122, rho, r]
  <;> ring_nf <;> simp

theorem trace_n233 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n233 b = r/2 := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n233, rho, r]
  <;> ring_nf <;> simp

theorem trace_n21 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n21 b = p b := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n1, n2, n3, n4, n5, n6, n7, n9, n10, n11, n12, n13, n14, n16, n17, n18, n19, n20, n21, trace_n0 b hb hp, p, t, q]
  <;> ring_nf <;> simp

theorem trace_n34 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n34 b = t b := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n9, n13, n14, n16, n17, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, trace_n0 b hb hp, p, t, q]
  <;> ring_nf <;> simp

theorem trace_n55 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n55 b = q b := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n13, n14, n16, n17, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n49, n50, n51, n52, n53, n54, n55, trace_n0 b hb hp, p, t, q]
  <;> ring_nf <;> simp

theorem trace_n56 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n56 b = -p b := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n56, trace_n21 b hb hp, p, t, q]
  <;> ring_nf <;> simp

theorem trace_n61 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n61 b = (H0 b).d := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n58, n59, n60, n61, trace_n0 b hb hp, H0, H1, H2, H3, H4, transformH, Sym2.scale, rho, r]
  <;> ring_nf <;> simp

theorem trace_n63 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n63 b = (H1 b).a := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n62, n63, trace_n0 b hb hp, H0, H1, H2, H3, H4, transformH, Sym2.scale, rho, r]
  <;> ring_nf <;> simp

theorem trace_n65 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n65 b = (H1 b).b := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n65, trace_n0 b hb hp, trace_n64 b hb hp, H0, H1, H2, H3, H4, transformH, Sym2.scale, rho, r]
  <;> ring_nf <;> simp

theorem trace_n90 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n90 b = (H2 b).a := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n67, n68, n69, n70, n71, n77, n78, n79, n90, trace_n21 b hb hp, trace_n55 b hb hp, trace_n61 b hb hp, trace_n64 b hb hp, trace_n89 b hb hp, H0, H1, H2, H3, H4, transformH, Sym2.scale, rho, r]
  <;> ring_nf <;> simp

theorem trace_n91 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n91 b = (H2 b).b := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n67, n68, n69, n70, n71, n80, n81, n82, n91, trace_n21 b hb hp, trace_n34 b hb hp, trace_n55 b hb hp, trace_n56 b hb hp, trace_n61 b hb hp, trace_n64 b hb hp, trace_n89 b hb hp, H0, H1, H2, H3, H4, transformH, Sym2.scale, rho, r]
  <;> ring_nf <;> simp

theorem trace_n92 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n92 b = (H2 b).b := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n72, n73, n74, n75, n76, n83, n84, n85, n92, trace_n21 b hb hp, trace_n34 b hb hp, trace_n55 b hb hp, trace_n56 b hb hp, trace_n61 b hb hp, trace_n64 b hb hp, trace_n89 b hb hp, H0, H1, H2, H3, H4, transformH, Sym2.scale, rho, r]
  <;> ring_nf <;> simp

theorem trace_n93 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n93 b = (H2 b).d := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n72, n73, n74, n75, n76, n86, n87, n88, n93, trace_n34 b hb hp, trace_n56 b hb hp, trace_n61 b hb hp, trace_n64 b hb hp, trace_n89 b hb hp, H0, H1, H2, H3, H4, transformH, Sym2.scale, rho, r]
  <;> ring_nf <;> simp

theorem trace_n118 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n118 b = (H3 b).a := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n94, n95, n96, n97, n98, n99, n106, n107, n108, n118, trace_n0 b hb hp, trace_n21 b hb hp, trace_n55 b hb hp, trace_n63 b hb hp, trace_n65 b hb hp, trace_n89 b hb hp, H0, H1, H2, H3, H4, transformH, Sym2.scale, rho, r]
  <;> ring_nf <;> simp

theorem trace_n119 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n119 b = (H3 b).b := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n94, n95, n96, n97, n98, n99, n109, n110, n111, n119, trace_n0 b hb hp, trace_n21 b hb hp, trace_n34 b hb hp, trace_n55 b hb hp, trace_n56 b hb hp, trace_n63 b hb hp, trace_n65 b hb hp, trace_n89 b hb hp, H0, H1, H2, H3, H4, transformH, Sym2.scale, rho, r]
  <;> ring_nf <;> simp

theorem trace_n120 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n120 b = (H3 b).b := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n100, n101, n102, n103, n104, n105, n112, n113, n114, n120, trace_n0 b hb hp, trace_n21 b hb hp, trace_n34 b hb hp, trace_n55 b hb hp, trace_n56 b hb hp, trace_n63 b hb hp, trace_n65 b hb hp, trace_n89 b hb hp, H0, H1, H2, H3, H4, transformH, Sym2.scale, rho, r]
  <;> ring_nf <;> simp

theorem trace_n121 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n121 b = (H3 b).d := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n100, n101, n102, n103, n104, n105, n115, n116, n117, n121, trace_n0 b hb hp, trace_n34 b hb hp, trace_n56 b hb hp, trace_n63 b hb hp, trace_n65 b hb hp, trace_n89 b hb hp, H0, H1, H2, H3, H4, transformH, Sym2.scale, rho, r]
  <;> ring_nf <;> simp

theorem trace_n123 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n123 b = (H4 b).d := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n123, trace_n61 b hb hp, trace_n122 b hb hp, H0, H1, H2, H3, H4, transformH, Sym2.scale, rho, r]
  <;> ring_nf <;> simp

theorem trace_n136 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n136 b = (x0 b).1 := by
  rw [x0_explicit b hb hp]
  norm_num [div_eq_mul_inv, mul_inv_rev, n11, n49, n124, n125, n126, n127, n128, n129, n130, n131, n132, n133, n134, n135, n136, trace_n0 b hb hp, x1, x2, x3, x4, jtMul, rho, r]
  <;> ring_nf <;> simp

theorem trace_n150 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n150 b = (x0 b).2 := by
  rw [x0_explicit b hb hp]
  norm_num [div_eq_mul_inv, mul_inv_rev, n137, n138, n139, n140, n141, n142, n143, n144, n145, n146, n147, n149, n150, trace_n0 b hb hp, x1, x2, x3, x4, jtMul, rho, r]
  <;> ring_nf <;> simp

theorem trace_n151 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n151 b = (x1 b).1 := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n16, n151, trace_n136 b hb hp, x1, x2, x3, x4, jtMul, rho, r]
  <;> ring_nf <;> simp

theorem trace_n153 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n153 b = (x1 b).2 := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n152, n153, trace_n150 b hb hp, x1, x2, x3, x4, jtMul, rho, r]
  <;> ring_nf <;> simp

theorem trace_n160 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n160 b = (x2 b).1 := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n154, n155, n156, n160, trace_n21 b hb hp, trace_n55 b hb hp, trace_n89 b hb hp, trace_n136 b hb hp, trace_n150 b hb hp, x1, x2, x3, x4, jtMul, rho, r]
  <;> ring_nf <;> simp

theorem trace_n161 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n161 b = (x2 b).2 := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n157, n158, n159, n161, trace_n34 b hb hp, trace_n56 b hb hp, trace_n89 b hb hp, trace_n136 b hb hp, trace_n150 b hb hp, x1, x2, x3, x4, jtMul, rho, r]
  <;> ring_nf <;> simp

theorem trace_n168 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n168 b = (x3 b).1 := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n162, n163, n164, n168, trace_n21 b hb hp, trace_n55 b hb hp, trace_n89 b hb hp, trace_n151 b hb hp, trace_n153 b hb hp, x1, x2, x3, x4, jtMul, rho, r]
  <;> ring_nf <;> simp

theorem trace_n169 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n169 b = (x3 b).2 := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n165, n166, n167, n169, trace_n34 b hb hp, trace_n56 b hb hp, trace_n89 b hb hp, trace_n151 b hb hp, trace_n153 b hb hp, x1, x2, x3, x4, jtMul, rho, r]
  <;> ring_nf <;> simp

theorem trace_n170 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n170 b = (x4 b).1 := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n170, trace_n122 b hb hp, trace_n136 b hb hp, x1, x2, x3, x4, jtMul, rho, r]
  <;> ring_nf <;> simp

theorem trace_n171 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n171 b = (x4 b).2 := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n171, trace_n122 b hb hp, trace_n150 b hb hp, x1, x2, x3, x4, jtMul, rho, r]
  <;> ring_nf <;> simp

def phaseGradient (b : ℝ) : Fin 5 → Vec := ![g0,g1,g2 b,g3 b,g4]
def phaseMetric (b : ℝ) : Fin 5 → Sym2 := ![H0 b,H1 b,H2 b,H3 b,H4 b]
def phasePoint (b : ℝ) : Fin 5 → Vec := ![x0 b,x1 b,x2 b,x3 b,x4 b]

def traceGradient (b : ℝ) : Fin 5 → Vec :=
  ![(n15 b,n66 b),(n66 b,n15 b),(n21 b,n55 b),(n34 b,n56 b),(n15 b,n66 b)]

theorem traceGradient_eq (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    traceGradient b = phaseGradient b := by
  funext i
  fin_cases i <;> simp [traceGradient, phaseGradient,trace_n15 b hb hp,trace_n21 b hb hp,trace_n34 b hb hp,trace_n55 b hb hp,trace_n56 b hb hp,trace_n66 b hb hp,g0,g1,g2,g3,g4,H0,H1,H4,Sym2.scale,r,div_eq_mul_inv]

def traceMetric (b : ℝ) : Fin 5 → Sym2 :=
  ![⟨n15 b,n64 b,n61 b⟩,⟨n63 b,n65 b,n0 b⟩,⟨n90 b,n91 b,n93 b⟩,⟨n118 b,n119 b,n121 b⟩,⟨n122 b,n233 b,n123 b⟩]

theorem traceMetric_eq (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    traceMetric b = phaseMetric b := by
  funext i
  fin_cases i <;> simp [traceMetric, phaseMetric,trace_n0 b hb hp,trace_n15 b hb hp,trace_n61 b hb hp,trace_n63 b hb hp,trace_n64 b hb hp,trace_n65 b hb hp,trace_n90 b hb hp,trace_n91 b hb hp,trace_n92 b hb hp,trace_n93 b hb hp,trace_n118 b hb hp,trace_n119 b hb hp,trace_n120 b hb hp,trace_n121 b hb hp,trace_n122 b hb hp,trace_n123 b hb hp,trace_n233 b hb hp,g0,g1,g2,g3,g4,H0,H1,H4,Sym2.scale,r,div_eq_mul_inv]

def tracePoint (b : ℝ) : Fin 5 → Vec :=
  ![(n136 b,n150 b),(n151 b,n153 b),(n160 b,n161 b),(n168 b,n169 b),(n170 b,n171 b)]

theorem tracePoint_eq (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    tracePoint b = phasePoint b := by
  funext i
  fin_cases i <;> simp [tracePoint, phasePoint,trace_n136 b hb hp,trace_n150 b hb hp,trace_n151 b hb hp,trace_n153 b hb hp,trace_n160 b hb hp,trace_n161 b hb hp,trace_n168 b hb hp,trace_n169 b hb hp,trace_n170 b hb hp,trace_n171 b hb hp,g0,g1,g2,g3,g4,H0,H1,H4,Sym2.scale,r,div_eq_mul_inv]

/-- The prescribed rank-one Hessian, perpendicular to the cycle position. -/
def pointHessian (beta : ℝ) (v : Vec) : Sym2 :=
  ⟨beta * v.2 ^ 2 / dot v v, -(beta * v.1 * v.2 / dot v v),
    beta * v.1 ^ 2 / dot v v⟩

def phaseHessian (b : ℝ) : Fin 5 → Sym2 :=
  ![pointHessian (19/10) (x0 b), pointHessian (8/5) (x1 b),
    pointHessian (-41/10) (x2 b), pointHessian (1/5) (x3 b),
    (pointHessian (19/10) (x0 b)).scale (1/r)]

def phaseValue (b : ℝ) (i : Fin 5) : ℝ := dot (phaseGradient b i) (phasePoint b i)
def phaseNormSquared (b : ℝ) (i : Fin 5) : ℝ := dot (phasePoint b i) (phasePoint b i)
def phaseCoordinate (b : ℝ) (i : Fin 4) : ℝ :=
  (phasePoint b i.castSucc).1 - (phasePoint b i.castSucc).2 / 20
/-- Signed absolute coordinate; the interval certificate verifies its positivity. -/
def phaseAbsCoordinate (b : ℝ) (i : Fin 4) : ℝ :=
  if i.val < 2 then phaseCoordinate b i else -phaseCoordinate b i

def phaseNodeT (b : ℝ) (i : Fin 4) : ℝ :=
  (phasePoint b i.castSucc).2 / phaseAbsCoordinate b i

def phaseNodeEta (b : ℝ) (i : Fin 4) : ℝ :=
  phaseValue b i.castSucc / phaseAbsCoordinate b i

def phaseNodeD (b : ℝ) (i : Fin 4) : ℝ :=
  (1/20) * (phaseGradient b i.castSucc).1 + (phaseGradient b i.castSucc).2

def phaseNodeK (b : ℝ) (i : Fin 4) : ℝ :=
  phaseAbsCoordinate b i * dot ((1/20),1)
    ((phaseHessian b i.castSucc).mulV ((1/20),1))

def phaseStep (b : ℝ) (i : Fin 4) : Vec :=
  -(phaseMetric b i.castSucc).mulV (phaseGradient b i.castSucc)

def phaseCurvature (b : ℝ) (i : Fin 4) : ℝ :=
  dot (phaseStep b i) (phaseGradient b i.succ - phaseGradient b i.castSucc)

def phaseArmijo (b : ℝ) (i : Fin 4) : ℝ :=
  phaseValue b i.castSucc + (3/100) * dot (phaseGradient b i.castSucc) (phaseStep b i) -
    phaseValue b i.succ

def phaseWolfe (b : ℝ) (i : Fin 4) : ℝ :=
  dot (phaseGradient b i.succ - (3/5 : ℝ) • phaseGradient b i.castSucc) (phaseStep b i)

theorem trace_n178 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n178 b = phaseNormSquared b 0 := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n176, n177, n178, trace_n136 b hb hp, trace_n150 b hb hp, phaseGradient, phaseMetric, phasePoint, phaseHessian, phaseValue, phaseNormSquared, phaseCoordinate, phaseAbsCoordinate, phaseNodeT, phaseNodeEta, phaseNodeD, phaseNodeK, phaseStep, phaseCurvature, phaseArmijo, phaseWolfe, g0, g1, g2, g3, g4, H0, H1, H4, Sym2.scale, Sym2.mulV, dot, r, rho]
  <;> ring_nf <;> simp

theorem trace_n192 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n192 b = phaseNormSquared b 1 := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n190, n191, n192, trace_n151 b hb hp, trace_n153 b hb hp, phaseGradient, phaseMetric, phasePoint, phaseHessian, phaseValue, phaseNormSquared, phaseCoordinate, phaseAbsCoordinate, phaseNodeT, phaseNodeEta, phaseNodeD, phaseNodeK, phaseStep, phaseCurvature, phaseArmijo, phaseWolfe, g0, g1, g2, g3, g4, H0, H1, H4, Sym2.scale, Sym2.mulV, dot, r, rho]
  <;> ring_nf <;> simp

theorem trace_n206 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n206 b = phaseNormSquared b 2 := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n204, n205, n206, trace_n160 b hb hp, trace_n161 b hb hp, phaseGradient, phaseMetric, phasePoint, phaseHessian, phaseValue, phaseNormSquared, phaseCoordinate, phaseAbsCoordinate, phaseNodeT, phaseNodeEta, phaseNodeD, phaseNodeK, phaseStep, phaseCurvature, phaseArmijo, phaseWolfe, g0, g1, g2, g3, g4, H0, H1, H4, Sym2.scale, Sym2.mulV, dot, r, rho]
  <;> ring_nf <;> simp

theorem trace_n220 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n220 b = phaseNormSquared b 3 := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n218, n219, n220, trace_n168 b hb hp, trace_n169 b hb hp, phaseGradient, phaseMetric, phasePoint, phaseHessian, phaseValue, phaseNormSquared, phaseCoordinate, phaseAbsCoordinate, phaseNodeT, phaseNodeEta, phaseNodeD, phaseNodeK, phaseStep, phaseCurvature, phaseArmijo, phaseWolfe, g0, g1, g2, g3, g4, H0, H1, H4, Sym2.scale, Sym2.mulV, dot, r, rho]
  <;> ring_nf <;> simp

theorem trace_n301 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n301 b = phaseNormSquared b 4 := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n299, n300, n301, trace_n170 b hb hp, trace_n171 b hb hp, phaseGradient, phaseMetric, phasePoint, phaseHessian, phaseValue, phaseNormSquared, phaseCoordinate, phaseAbsCoordinate, phaseNodeT, phaseNodeEta, phaseNodeD, phaseNodeK, phaseStep, phaseCurvature, phaseArmijo, phaseWolfe, g0, g1, g2, g3, g4, H0, H1, H4, Sym2.scale, Sym2.mulV, dot, r, rho]
  <;> ring_nf <;> simp

theorem trace_n182 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n182 b = (phaseHessian b 0).a := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n172, n173, n179, n180, n181, n182, trace_n150 b hb hp, trace_n178 b hb hp, phaseGradient, phaseMetric, phasePoint, phaseHessian, phaseValue, phaseNormSquared, phaseCoordinate, phaseAbsCoordinate, phaseNodeT, phaseNodeEta, phaseNodeD, phaseNodeK, phaseStep, phaseCurvature, phaseArmijo, phaseWolfe, g0, g1, g2, g3, g4, H0, H1, H4, Sym2.scale, Sym2.mulV, dot, r, rho, pointHessian]
  <;> ring_nf <;> simp

theorem trace_n183 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n183 b = (phaseHessian b 0).b := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n172, n174, n179, n180, n181, n183, trace_n136 b hb hp, trace_n150 b hb hp, trace_n178 b hb hp, phaseGradient, phaseMetric, phasePoint, phaseHessian, phaseValue, phaseNormSquared, phaseCoordinate, phaseAbsCoordinate, phaseNodeT, phaseNodeEta, phaseNodeD, phaseNodeK, phaseStep, phaseCurvature, phaseArmijo, phaseWolfe, g0, g1, g2, g3, g4, H0, H1, H4, Sym2.scale, Sym2.mulV, dot, r, rho, pointHessian]
  <;> ring_nf <;> simp

theorem trace_n184 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n184 b = (phaseHessian b 0).b := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n172, n175, n179, n180, n181, n184, trace_n136 b hb hp, trace_n150 b hb hp, trace_n178 b hb hp, phaseGradient, phaseMetric, phasePoint, phaseHessian, phaseValue, phaseNormSquared, phaseCoordinate, phaseAbsCoordinate, phaseNodeT, phaseNodeEta, phaseNodeD, phaseNodeK, phaseStep, phaseCurvature, phaseArmijo, phaseWolfe, g0, g1, g2, g3, g4, H0, H1, H4, Sym2.scale, Sym2.mulV, dot, r, rho, pointHessian]
  <;> ring_nf <;> simp

theorem trace_n185 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n185 b = (phaseHessian b 0).d := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n176, n179, n180, n181, n185, trace_n136 b hb hp, trace_n178 b hb hp, phaseGradient, phaseMetric, phasePoint, phaseHessian, phaseValue, phaseNormSquared, phaseCoordinate, phaseAbsCoordinate, phaseNodeT, phaseNodeEta, phaseNodeD, phaseNodeK, phaseStep, phaseCurvature, phaseArmijo, phaseWolfe, g0, g1, g2, g3, g4, H0, H1, H4, Sym2.scale, Sym2.mulV, dot, r, rho, pointHessian]
  <;> ring_nf <;> simp

theorem trace_n196 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n196 b = (phaseHessian b 1).a := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n186, n187, n193, n194, n195, n196, trace_n153 b hb hp, trace_n192 b hb hp, phaseGradient, phaseMetric, phasePoint, phaseHessian, phaseValue, phaseNormSquared, phaseCoordinate, phaseAbsCoordinate, phaseNodeT, phaseNodeEta, phaseNodeD, phaseNodeK, phaseStep, phaseCurvature, phaseArmijo, phaseWolfe, g0, g1, g2, g3, g4, H0, H1, H4, Sym2.scale, Sym2.mulV, dot, r, rho, pointHessian]
  <;> ring_nf <;> simp

theorem trace_n197 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n197 b = (phaseHessian b 1).b := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n186, n188, n193, n194, n195, n197, trace_n151 b hb hp, trace_n153 b hb hp, trace_n192 b hb hp, phaseGradient, phaseMetric, phasePoint, phaseHessian, phaseValue, phaseNormSquared, phaseCoordinate, phaseAbsCoordinate, phaseNodeT, phaseNodeEta, phaseNodeD, phaseNodeK, phaseStep, phaseCurvature, phaseArmijo, phaseWolfe, g0, g1, g2, g3, g4, H0, H1, H4, Sym2.scale, Sym2.mulV, dot, r, rho, pointHessian]
  <;> ring_nf <;> simp

theorem trace_n198 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n198 b = (phaseHessian b 1).b := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n186, n189, n193, n194, n195, n198, trace_n151 b hb hp, trace_n153 b hb hp, trace_n192 b hb hp, phaseGradient, phaseMetric, phasePoint, phaseHessian, phaseValue, phaseNormSquared, phaseCoordinate, phaseAbsCoordinate, phaseNodeT, phaseNodeEta, phaseNodeD, phaseNodeK, phaseStep, phaseCurvature, phaseArmijo, phaseWolfe, g0, g1, g2, g3, g4, H0, H1, H4, Sym2.scale, Sym2.mulV, dot, r, rho, pointHessian]
  <;> ring_nf <;> simp

theorem trace_n199 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n199 b = (phaseHessian b 1).d := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n190, n193, n194, n195, n199, trace_n151 b hb hp, trace_n192 b hb hp, phaseGradient, phaseMetric, phasePoint, phaseHessian, phaseValue, phaseNormSquared, phaseCoordinate, phaseAbsCoordinate, phaseNodeT, phaseNodeEta, phaseNodeD, phaseNodeK, phaseStep, phaseCurvature, phaseArmijo, phaseWolfe, g0, g1, g2, g3, g4, H0, H1, H4, Sym2.scale, Sym2.mulV, dot, r, rho, pointHessian]
  <;> ring_nf <;> simp

theorem trace_n210 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n210 b = (phaseHessian b 2).a := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n200, n201, n207, n208, n209, n210, trace_n161 b hb hp, trace_n206 b hb hp, phaseGradient, phaseMetric, phasePoint, phaseHessian, phaseValue, phaseNormSquared, phaseCoordinate, phaseAbsCoordinate, phaseNodeT, phaseNodeEta, phaseNodeD, phaseNodeK, phaseStep, phaseCurvature, phaseArmijo, phaseWolfe, g0, g1, g2, g3, g4, H0, H1, H4, Sym2.scale, Sym2.mulV, dot, r, rho, pointHessian]
  <;> ring_nf <;> simp

theorem trace_n211 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n211 b = (phaseHessian b 2).b := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n200, n202, n207, n208, n209, n211, trace_n160 b hb hp, trace_n161 b hb hp, trace_n206 b hb hp, phaseGradient, phaseMetric, phasePoint, phaseHessian, phaseValue, phaseNormSquared, phaseCoordinate, phaseAbsCoordinate, phaseNodeT, phaseNodeEta, phaseNodeD, phaseNodeK, phaseStep, phaseCurvature, phaseArmijo, phaseWolfe, g0, g1, g2, g3, g4, H0, H1, H4, Sym2.scale, Sym2.mulV, dot, r, rho, pointHessian]
  <;> ring_nf <;> simp

theorem trace_n212 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n212 b = (phaseHessian b 2).b := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n200, n203, n207, n208, n209, n212, trace_n160 b hb hp, trace_n161 b hb hp, trace_n206 b hb hp, phaseGradient, phaseMetric, phasePoint, phaseHessian, phaseValue, phaseNormSquared, phaseCoordinate, phaseAbsCoordinate, phaseNodeT, phaseNodeEta, phaseNodeD, phaseNodeK, phaseStep, phaseCurvature, phaseArmijo, phaseWolfe, g0, g1, g2, g3, g4, H0, H1, H4, Sym2.scale, Sym2.mulV, dot, r, rho, pointHessian]
  <;> ring_nf <;> simp

theorem trace_n213 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n213 b = (phaseHessian b 2).d := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n204, n207, n208, n209, n213, trace_n160 b hb hp, trace_n206 b hb hp, phaseGradient, phaseMetric, phasePoint, phaseHessian, phaseValue, phaseNormSquared, phaseCoordinate, phaseAbsCoordinate, phaseNodeT, phaseNodeEta, phaseNodeD, phaseNodeK, phaseStep, phaseCurvature, phaseArmijo, phaseWolfe, g0, g1, g2, g3, g4, H0, H1, H4, Sym2.scale, Sym2.mulV, dot, r, rho, pointHessian]
  <;> ring_nf <;> simp

theorem trace_n224 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n224 b = (phaseHessian b 3).a := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n214, n215, n221, n222, n223, n224, trace_n169 b hb hp, trace_n220 b hb hp, phaseGradient, phaseMetric, phasePoint, phaseHessian, phaseValue, phaseNormSquared, phaseCoordinate, phaseAbsCoordinate, phaseNodeT, phaseNodeEta, phaseNodeD, phaseNodeK, phaseStep, phaseCurvature, phaseArmijo, phaseWolfe, g0, g1, g2, g3, g4, H0, H1, H4, Sym2.scale, Sym2.mulV, dot, r, rho, pointHessian]
  <;> ring_nf <;> simp

theorem trace_n225 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n225 b = (phaseHessian b 3).b := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n214, n216, n221, n222, n223, n225, trace_n168 b hb hp, trace_n169 b hb hp, trace_n220 b hb hp, phaseGradient, phaseMetric, phasePoint, phaseHessian, phaseValue, phaseNormSquared, phaseCoordinate, phaseAbsCoordinate, phaseNodeT, phaseNodeEta, phaseNodeD, phaseNodeK, phaseStep, phaseCurvature, phaseArmijo, phaseWolfe, g0, g1, g2, g3, g4, H0, H1, H4, Sym2.scale, Sym2.mulV, dot, r, rho, pointHessian]
  <;> ring_nf <;> simp

theorem trace_n226 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n226 b = (phaseHessian b 3).b := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n214, n217, n221, n222, n223, n226, trace_n168 b hb hp, trace_n169 b hb hp, trace_n220 b hb hp, phaseGradient, phaseMetric, phasePoint, phaseHessian, phaseValue, phaseNormSquared, phaseCoordinate, phaseAbsCoordinate, phaseNodeT, phaseNodeEta, phaseNodeD, phaseNodeK, phaseStep, phaseCurvature, phaseArmijo, phaseWolfe, g0, g1, g2, g3, g4, H0, H1, H4, Sym2.scale, Sym2.mulV, dot, r, rho, pointHessian]
  <;> ring_nf <;> simp

theorem trace_n227 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n227 b = (phaseHessian b 3).d := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n218, n221, n222, n223, n227, trace_n168 b hb hp, trace_n220 b hb hp, phaseGradient, phaseMetric, phasePoint, phaseHessian, phaseValue, phaseNormSquared, phaseCoordinate, phaseAbsCoordinate, phaseNodeT, phaseNodeEta, phaseNodeD, phaseNodeK, phaseStep, phaseCurvature, phaseArmijo, phaseWolfe, g0, g1, g2, g3, g4, H0, H1, H4, Sym2.scale, Sym2.mulV, dot, r, rho, pointHessian]
  <;> ring_nf <;> simp

theorem trace_n229 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n229 b = (phaseHessian b 4).a := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n228, n229, trace_n182 b hb hp, phaseGradient, phaseMetric, phasePoint, phaseHessian, phaseValue, phaseNormSquared, phaseCoordinate, phaseAbsCoordinate, phaseNodeT, phaseNodeEta, phaseNodeD, phaseNodeK, phaseStep, phaseCurvature, phaseArmijo, phaseWolfe, g0, g1, g2, g3, g4, H0, H1, H4, Sym2.scale, Sym2.mulV, dot, r, rho, pointHessian]
  <;> ring_nf <;> simp

theorem trace_n230 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n230 b = (phaseHessian b 4).b := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n228, n230, trace_n183 b hb hp, phaseGradient, phaseMetric, phasePoint, phaseHessian, phaseValue, phaseNormSquared, phaseCoordinate, phaseAbsCoordinate, phaseNodeT, phaseNodeEta, phaseNodeD, phaseNodeK, phaseStep, phaseCurvature, phaseArmijo, phaseWolfe, g0, g1, g2, g3, g4, H0, H1, H4, Sym2.scale, Sym2.mulV, dot, r, rho, pointHessian]
  <;> ring_nf <;> simp

theorem trace_n231 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n231 b = (phaseHessian b 4).b := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n228, n231, trace_n184 b hb hp, phaseGradient, phaseMetric, phasePoint, phaseHessian, phaseValue, phaseNormSquared, phaseCoordinate, phaseAbsCoordinate, phaseNodeT, phaseNodeEta, phaseNodeD, phaseNodeK, phaseStep, phaseCurvature, phaseArmijo, phaseWolfe, g0, g1, g2, g3, g4, H0, H1, H4, Sym2.scale, Sym2.mulV, dot, r, rho, pointHessian]
  <;> ring_nf <;> simp

theorem trace_n232 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n232 b = (phaseHessian b 4).d := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n228, n232, trace_n185 b hb hp, phaseGradient, phaseMetric, phasePoint, phaseHessian, phaseValue, phaseNormSquared, phaseCoordinate, phaseAbsCoordinate, phaseNodeT, phaseNodeEta, phaseNodeD, phaseNodeK, phaseStep, phaseCurvature, phaseArmijo, phaseWolfe, g0, g1, g2, g3, g4, H0, H1, H4, Sym2.scale, Sym2.mulV, dot, r, rho, pointHessian]
  <;> ring_nf <;> simp

theorem trace_n236 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n236 b = phaseValue b 2 := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n234, n235, n236, trace_n21 b hb hp, trace_n55 b hb hp, trace_n160 b hb hp, trace_n161 b hb hp, phaseGradient, phaseMetric, phasePoint, phaseHessian, phaseValue, phaseNormSquared, phaseCoordinate, phaseAbsCoordinate, phaseNodeT, phaseNodeEta, phaseNodeD, phaseNodeK, phaseStep, phaseCurvature, phaseArmijo, phaseWolfe, g0, g1, g2, g3, g4, H0, H1, H4, Sym2.scale, Sym2.mulV, dot, r, rho]
  <;> ring_nf <;> simp

theorem trace_n239 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n239 b = phaseValue b 3 := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n237, n238, n239, trace_n34 b hb hp, trace_n56 b hb hp, trace_n168 b hb hp, trace_n169 b hb hp, phaseGradient, phaseMetric, phasePoint, phaseHessian, phaseValue, phaseNormSquared, phaseCoordinate, phaseAbsCoordinate, phaseNodeT, phaseNodeEta, phaseNodeD, phaseNodeK, phaseStep, phaseCurvature, phaseArmijo, phaseWolfe, g0, g1, g2, g3, g4, H0, H1, H4, Sym2.scale, Sym2.mulV, dot, r, rho]
  <;> ring_nf <;> simp

theorem trace_n244 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n244 b = phaseCoordinate b 0 := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n241, n242, n243, n244, trace_n136 b hb hp, trace_n150 b hb hp, phaseGradient, phaseMetric, phasePoint, phaseHessian, phaseValue, phaseNormSquared, phaseCoordinate, phaseAbsCoordinate, phaseNodeT, phaseNodeEta, phaseNodeD, phaseNodeK, phaseStep, phaseCurvature, phaseArmijo, phaseWolfe, g0, g1, g2, g3, g4, H0, H1, H4, Sym2.scale, Sym2.mulV, dot, r, rho]
  <;> ring_nf <;> simp

theorem trace_n257 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n257 b = phaseCoordinate b 1 := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n241, n255, n256, n257, trace_n151 b hb hp, trace_n153 b hb hp, phaseGradient, phaseMetric, phasePoint, phaseHessian, phaseValue, phaseNormSquared, phaseCoordinate, phaseAbsCoordinate, phaseNodeT, phaseNodeEta, phaseNodeD, phaseNodeK, phaseStep, phaseCurvature, phaseArmijo, phaseWolfe, g0, g1, g2, g3, g4, H0, H1, H4, Sym2.scale, Sym2.mulV, dot, r, rho]
  <;> ring_nf <;> simp

theorem trace_n269 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n269 b = phaseCoordinate b 2 := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n241, n267, n268, n269, trace_n160 b hb hp, trace_n161 b hb hp, phaseGradient, phaseMetric, phasePoint, phaseHessian, phaseValue, phaseNormSquared, phaseCoordinate, phaseAbsCoordinate, phaseNodeT, phaseNodeEta, phaseNodeD, phaseNodeK, phaseStep, phaseCurvature, phaseArmijo, phaseWolfe, g0, g1, g2, g3, g4, H0, H1, H4, Sym2.scale, Sym2.mulV, dot, r, rho]
  <;> ring_nf <;> simp

theorem trace_n285 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n285 b = phaseCoordinate b 3 := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n241, n283, n284, n285, trace_n168 b hb hp, trace_n169 b hb hp, phaseGradient, phaseMetric, phasePoint, phaseHessian, phaseValue, phaseNormSquared, phaseCoordinate, phaseAbsCoordinate, phaseNodeT, phaseNodeEta, phaseNodeD, phaseNodeK, phaseStep, phaseCurvature, phaseArmijo, phaseWolfe, g0, g1, g2, g3, g4, H0, H1, H4, Sym2.scale, Sym2.mulV, dot, r, rho]
  <;> ring_nf <;> simp

theorem trace_n246 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n246 b = phaseNodeT b 0 := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n245, n246, trace_n150 b hb hp, trace_n244 b hb hp, phaseGradient, phaseMetric, phasePoint, phaseHessian, phaseValue, phaseNormSquared, phaseCoordinate, phaseAbsCoordinate, phaseNodeT, phaseNodeEta, phaseNodeD, phaseNodeK, phaseStep, phaseCurvature, phaseArmijo, phaseWolfe, g0, g1, g2, g3, g4, H0, H1, H4, Sym2.scale, Sym2.mulV, dot, r, rho]
  <;> ring_nf <;> simp

theorem trace_n247 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n247 b = phaseNodeEta b 0 := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n245, n247, trace_n136 b hb hp, trace_n244 b hb hp, phaseGradient, phaseMetric, phasePoint, phaseHessian, phaseValue, phaseNormSquared, phaseCoordinate, phaseAbsCoordinate, phaseNodeT, phaseNodeEta, phaseNodeD, phaseNodeK, phaseStep, phaseCurvature, phaseArmijo, phaseWolfe, g0, g1, g2, g3, g4, H0, H1, H4, Sym2.scale, Sym2.mulV, dot, r, rho]
  <;> ring_nf <;> simp

theorem trace_n241 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n241 b = phaseNodeD b 0 := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n241, phaseGradient, phaseMetric, phasePoint, phaseHessian, phaseValue, phaseNormSquared, phaseCoordinate, phaseAbsCoordinate, phaseNodeT, phaseNodeEta, phaseNodeD, phaseNodeK, phaseStep, phaseCurvature, phaseArmijo, phaseWolfe, g0, g1, g2, g3, g4, H0, H1, H4, Sym2.scale, Sym2.mulV, dot, r, rho]
  <;> ring_nf <;> simp

theorem trace_n254 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n254 b = phaseNodeK b 0 := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n248, n249, n250, n251, n252, n253, n254, trace_n182 b hb hp, trace_n183 b hb hp, trace_n184 b hb hp, trace_n185 b hb hp, trace_n241 b hb hp, trace_n244 b hb hp, phaseGradient, phaseMetric, phasePoint, phaseHessian, phaseValue, phaseNormSquared, phaseCoordinate, phaseAbsCoordinate, phaseNodeT, phaseNodeEta, phaseNodeD, phaseNodeK, phaseStep, phaseCurvature, phaseArmijo, phaseWolfe, g0, g1, g2, g3, g4, H0, H1, H4, Sym2.scale, Sym2.mulV, dot, r, rho]
  <;> ring_nf <;> simp

theorem trace_n259 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n259 b = phaseNodeT b 1 := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n258, n259, trace_n153 b hb hp, trace_n257 b hb hp, phaseGradient, phaseMetric, phasePoint, phaseHessian, phaseValue, phaseNormSquared, phaseCoordinate, phaseAbsCoordinate, phaseNodeT, phaseNodeEta, phaseNodeD, phaseNodeK, phaseStep, phaseCurvature, phaseArmijo, phaseWolfe, g0, g1, g2, g3, g4, H0, H1, H4, Sym2.scale, Sym2.mulV, dot, r, rho]
  <;> ring_nf <;> simp

theorem trace_n266 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n266 b = phaseNodeK b 1 := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n260, n261, n262, n263, n264, n265, n266, trace_n196 b hb hp, trace_n197 b hb hp, trace_n198 b hb hp, trace_n199 b hb hp, trace_n241 b hb hp, trace_n257 b hb hp, phaseGradient, phaseMetric, phasePoint, phaseHessian, phaseValue, phaseNormSquared, phaseCoordinate, phaseAbsCoordinate, phaseNodeT, phaseNodeEta, phaseNodeD, phaseNodeK, phaseStep, phaseCurvature, phaseArmijo, phaseWolfe, g0, g1, g2, g3, g4, H0, H1, H4, Sym2.scale, Sym2.mulV, dot, r, rho]
  <;> ring_nf <;> simp

theorem trace_n272 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n272 b = phaseNodeT b 2 := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n270, n271, n272, trace_n161 b hb hp, trace_n269 b hb hp, phaseGradient, phaseMetric, phasePoint, phaseHessian, phaseValue, phaseNormSquared, phaseCoordinate, phaseAbsCoordinate, phaseNodeT, phaseNodeEta, phaseNodeD, phaseNodeK, phaseStep, phaseCurvature, phaseArmijo, phaseWolfe, g0, g1, g2, g3, g4, H0, H1, H4, Sym2.scale, Sym2.mulV, dot, r, rho]
  <;> ring_nf <;> simp

theorem trace_n273 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n273 b = phaseNodeEta b 2 := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n270, n271, n273, trace_n236 b hb hp, trace_n269 b hb hp, phaseGradient, phaseMetric, phasePoint, phaseHessian, phaseValue, phaseNormSquared, phaseCoordinate, phaseAbsCoordinate, phaseNodeT, phaseNodeEta, phaseNodeD, phaseNodeK, phaseStep, phaseCurvature, phaseArmijo, phaseWolfe, g0, g1, g2, g3, g4, H0, H1, H4, Sym2.scale, Sym2.mulV, dot, r, rho]
  <;> ring_nf <;> simp

theorem trace_n275 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n275 b = phaseNodeD b 2 := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n274, n275, trace_n21 b hb hp, trace_n55 b hb hp, trace_n241 b hb hp, phaseGradient, phaseMetric, phasePoint, phaseHessian, phaseValue, phaseNormSquared, phaseCoordinate, phaseAbsCoordinate, phaseNodeT, phaseNodeEta, phaseNodeD, phaseNodeK, phaseStep, phaseCurvature, phaseArmijo, phaseWolfe, g0, g1, g2, g3, g4, H0, H1, H4, Sym2.scale, Sym2.mulV, dot, r, rho]
  <;> ring_nf <;> simp

theorem trace_n282 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n282 b = phaseNodeK b 2 := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n270, n276, n277, n278, n279, n280, n281, n282, trace_n210 b hb hp, trace_n211 b hb hp, trace_n212 b hb hp, trace_n213 b hb hp, trace_n241 b hb hp, trace_n269 b hb hp, phaseGradient, phaseMetric, phasePoint, phaseHessian, phaseValue, phaseNormSquared, phaseCoordinate, phaseAbsCoordinate, phaseNodeT, phaseNodeEta, phaseNodeD, phaseNodeK, phaseStep, phaseCurvature, phaseArmijo, phaseWolfe, g0, g1, g2, g3, g4, H0, H1, H4, Sym2.scale, Sym2.mulV, dot, r, rho]
  <;> ring_nf <;> simp

theorem trace_n288 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n288 b = phaseNodeT b 3 := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n286, n287, n288, trace_n169 b hb hp, trace_n285 b hb hp, phaseGradient, phaseMetric, phasePoint, phaseHessian, phaseValue, phaseNormSquared, phaseCoordinate, phaseAbsCoordinate, phaseNodeT, phaseNodeEta, phaseNodeD, phaseNodeK, phaseStep, phaseCurvature, phaseArmijo, phaseWolfe, g0, g1, g2, g3, g4, H0, H1, H4, Sym2.scale, Sym2.mulV, dot, r, rho]
  <;> ring_nf <;> simp

theorem trace_n289 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n289 b = phaseNodeEta b 3 := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n286, n287, n289, trace_n239 b hb hp, trace_n285 b hb hp, phaseGradient, phaseMetric, phasePoint, phaseHessian, phaseValue, phaseNormSquared, phaseCoordinate, phaseAbsCoordinate, phaseNodeT, phaseNodeEta, phaseNodeD, phaseNodeK, phaseStep, phaseCurvature, phaseArmijo, phaseWolfe, g0, g1, g2, g3, g4, H0, H1, H4, Sym2.scale, Sym2.mulV, dot, r, rho]
  <;> ring_nf <;> simp

theorem trace_n291 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n291 b = phaseNodeD b 3 := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n290, n291, trace_n34 b hb hp, trace_n56 b hb hp, trace_n241 b hb hp, phaseGradient, phaseMetric, phasePoint, phaseHessian, phaseValue, phaseNormSquared, phaseCoordinate, phaseAbsCoordinate, phaseNodeT, phaseNodeEta, phaseNodeD, phaseNodeK, phaseStep, phaseCurvature, phaseArmijo, phaseWolfe, g0, g1, g2, g3, g4, H0, H1, H4, Sym2.scale, Sym2.mulV, dot, r, rho]
  <;> ring_nf <;> simp

theorem trace_n298 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n298 b = phaseNodeK b 3 := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n286, n292, n293, n294, n295, n296, n297, n298, trace_n224 b hb hp, trace_n225 b hb hp, trace_n226 b hb hp, trace_n227 b hb hp, trace_n241 b hb hp, trace_n285 b hb hp, phaseGradient, phaseMetric, phasePoint, phaseHessian, phaseValue, phaseNormSquared, phaseCoordinate, phaseAbsCoordinate, phaseNodeT, phaseNodeEta, phaseNodeD, phaseNodeK, phaseStep, phaseCurvature, phaseArmijo, phaseWolfe, g0, g1, g2, g3, g4, H0, H1, H4, Sym2.scale, Sym2.mulV, dot, r, rho]
  <;> ring_nf <;> simp

theorem trace_n323 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n323 b = phaseCurvature b 1 := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n16, n302, n303, n320, n321, n322, n323, trace_n0 b hb hp, trace_n21 b hb hp, trace_n55 b hb hp, trace_n65 b hb hp, phaseGradient, phaseMetric, phasePoint, phaseHessian, phaseValue, phaseNormSquared, phaseCoordinate, phaseAbsCoordinate, phaseNodeT, phaseNodeEta, phaseNodeD, phaseNodeK, phaseStep, phaseCurvature, phaseArmijo, phaseWolfe, g0, g1, g2, g3, g4, H0, H1, H4, Sym2.scale, Sym2.mulV, dot, r, rho]
  <;> ring_nf <;> simp

theorem trace_n329 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n329 b = phaseCurvature b 2 := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n304, n305, n306, n307, n308, n309, n310, n311, n324, n325, n326, n327, n328, n329, trace_n21 b hb hp, trace_n34 b hb hp, trace_n55 b hb hp, trace_n56 b hb hp, trace_n90 b hb hp, trace_n91 b hb hp, trace_n92 b hb hp, trace_n93 b hb hp, phaseGradient, phaseMetric, phasePoint, phaseHessian, phaseValue, phaseNormSquared, phaseCoordinate, phaseAbsCoordinate, phaseNodeT, phaseNodeEta, phaseNodeD, phaseNodeK, phaseStep, phaseCurvature, phaseArmijo, phaseWolfe, g0, g1, g2, g3, g4, H0, H1, H4, Sym2.scale, Sym2.mulV, dot, r, rho]
  <;> ring_nf <;> simp

theorem trace_n335 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n335 b = phaseCurvature b 3 := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n312, n313, n314, n315, n316, n317, n318, n319, n330, n331, n332, n333, n334, n335, trace_n15 b hb hp, trace_n34 b hb hp, trace_n56 b hb hp, trace_n118 b hb hp, trace_n119 b hb hp, trace_n120 b hb hp, trace_n121 b hb hp, phaseGradient, phaseMetric, phasePoint, phaseHessian, phaseValue, phaseNormSquared, phaseCoordinate, phaseAbsCoordinate, phaseNodeT, phaseNodeEta, phaseNodeD, phaseNodeK, phaseStep, phaseCurvature, phaseArmijo, phaseWolfe, g0, g1, g2, g3, g4, H0, H1, H4, Sym2.scale, Sym2.mulV, dot, r, rho]
  <;> ring_nf <;> simp

theorem trace_n339 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n339 b = phaseArmijo b 0 := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n186, n337, n338, n339, trace_n136 b hb hp, trace_n153 b hb hp, phaseGradient, phaseMetric, phasePoint, phaseHessian, phaseValue, phaseNormSquared, phaseCoordinate, phaseAbsCoordinate, phaseNodeT, phaseNodeEta, phaseNodeD, phaseNodeK, phaseStep, phaseCurvature, phaseArmijo, phaseWolfe, g0, g1, g2, g3, g4, H0, H1, H4, Sym2.scale, Sym2.mulV, dot, r, rho]
  <;> ring_nf <;> simp

theorem trace_n343 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n343 b = phaseArmijo b 1 := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n303, n336, n340, n341, n342, n343, trace_n0 b hb hp, trace_n153 b hb hp, trace_n236 b hb hp, phaseGradient, phaseMetric, phasePoint, phaseHessian, phaseValue, phaseNormSquared, phaseCoordinate, phaseAbsCoordinate, phaseNodeT, phaseNodeEta, phaseNodeD, phaseNodeK, phaseStep, phaseCurvature, phaseArmijo, phaseWolfe, g0, g1, g2, g3, g4, H0, H1, H4, Sym2.scale, Sym2.mulV, dot, r, rho]
  <;> ring_nf <;> simp

theorem trace_n350 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n350 b = phaseArmijo b 2 := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n304, n305, n306, n307, n308, n309, n310, n311, n336, n344, n345, n346, n347, n348, n349, n350, trace_n21 b hb hp, trace_n55 b hb hp, trace_n90 b hb hp, trace_n91 b hb hp, trace_n92 b hb hp, trace_n93 b hb hp, trace_n236 b hb hp, trace_n239 b hb hp, phaseGradient, phaseMetric, phasePoint, phaseHessian, phaseValue, phaseNormSquared, phaseCoordinate, phaseAbsCoordinate, phaseNodeT, phaseNodeEta, phaseNodeD, phaseNodeK, phaseStep, phaseCurvature, phaseArmijo, phaseWolfe, g0, g1, g2, g3, g4, H0, H1, H4, Sym2.scale, Sym2.mulV, dot, r, rho]
  <;> ring_nf <;> simp

theorem trace_n357 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n357 b = phaseArmijo b 3 := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n312, n313, n314, n315, n316, n317, n318, n319, n336, n351, n352, n353, n354, n355, n356, n357, trace_n34 b hb hp, trace_n56 b hb hp, trace_n118 b hb hp, trace_n119 b hb hp, trace_n120 b hb hp, trace_n121 b hb hp, trace_n170 b hb hp, trace_n239 b hb hp, phaseGradient, phaseMetric, phasePoint, phaseHessian, phaseValue, phaseNormSquared, phaseCoordinate, phaseAbsCoordinate, phaseNodeT, phaseNodeEta, phaseNodeD, phaseNodeK, phaseStep, phaseCurvature, phaseArmijo, phaseWolfe, g0, g1, g2, g3, g4, H0, H1, H4, Sym2.scale, Sym2.mulV, dot, r, rho]
  <;> ring_nf <;> simp

theorem trace_n359 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n359 b = phaseWolfe b 0 := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n359, phaseGradient, phaseMetric, phasePoint, phaseHessian, phaseValue, phaseNormSquared, phaseCoordinate, phaseAbsCoordinate, phaseNodeT, phaseNodeEta, phaseNodeD, phaseNodeK, phaseStep, phaseCurvature, phaseArmijo, phaseWolfe, g0, g1, g2, g3, g4, H0, H1, H4, Sym2.scale, Sym2.mulV, dot, r, rho]
  <;> ring_nf <;> simp

theorem trace_n364 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n364 b = phaseWolfe b 1 := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n302, n303, n360, n361, n362, n363, n364, trace_n0 b hb hp, trace_n21 b hb hp, trace_n55 b hb hp, trace_n65 b hb hp, phaseGradient, phaseMetric, phasePoint, phaseHessian, phaseValue, phaseNormSquared, phaseCoordinate, phaseAbsCoordinate, phaseNodeT, phaseNodeEta, phaseNodeD, phaseNodeK, phaseStep, phaseCurvature, phaseArmijo, phaseWolfe, g0, g1, g2, g3, g4, H0, H1, H4, Sym2.scale, Sym2.mulV, dot, r, rho]
  <;> ring_nf <;> simp

theorem trace_n373 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n373 b = phaseWolfe b 2 := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n304, n305, n306, n307, n308, n309, n310, n311, n358, n365, n366, n367, n368, n369, n370, n371, n372, n373, trace_n21 b hb hp, trace_n34 b hb hp, trace_n55 b hb hp, trace_n56 b hb hp, trace_n90 b hb hp, trace_n91 b hb hp, trace_n92 b hb hp, trace_n93 b hb hp, phaseGradient, phaseMetric, phasePoint, phaseHessian, phaseValue, phaseNormSquared, phaseCoordinate, phaseAbsCoordinate, phaseNodeT, phaseNodeEta, phaseNodeD, phaseNodeK, phaseStep, phaseCurvature, phaseArmijo, phaseWolfe, g0, g1, g2, g3, g4, H0, H1, H4, Sym2.scale, Sym2.mulV, dot, r, rho]
  <;> ring_nf <;> simp

theorem trace_n381 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    n381 b = phaseWolfe b 3 := by
  norm_num [div_eq_mul_inv, mul_inv_rev, n312, n313, n314, n315, n316, n317, n318, n319, n358, n374, n375, n376, n377, n378, n379, n380, n381, trace_n15 b hb hp, trace_n34 b hb hp, trace_n56 b hb hp, trace_n118 b hb hp, trace_n119 b hb hp, trace_n120 b hb hp, trace_n121 b hb hp, phaseGradient, phaseMetric, phasePoint, phaseHessian, phaseValue, phaseNormSquared, phaseCoordinate, phaseAbsCoordinate, phaseNodeT, phaseNodeEta, phaseNodeD, phaseNodeK, phaseStep, phaseCurvature, phaseArmijo, phaseWolfe, g0, g1, g2, g3, g4, H0, H1, H4, Sym2.scale, Sym2.mulV, dot, r, rho]
  <;> ring_nf <;> simp

def traceHessian (b : ℝ) : Fin 5 → Sym2 :=
  ![⟨n182 b,n183 b,n185 b⟩,⟨n196 b,n197 b,n199 b⟩,⟨n210 b,n211 b,n213 b⟩,⟨n224 b,n225 b,n227 b⟩,⟨n229 b,n230 b,n232 b⟩]

theorem traceHessian_eq (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    traceHessian b = phaseHessian b := by
  funext i
  fin_cases i <;> simp [traceHessian, phaseHessian,trace_n182 b hb hp,trace_n183 b hb hp,trace_n184 b hb hp,trace_n185 b hb hp,trace_n196 b hb hp,trace_n197 b hb hp,trace_n198 b hb hp,trace_n199 b hb hp,trace_n210 b hb hp,trace_n211 b hb hp,trace_n212 b hb hp,trace_n213 b hb hp,trace_n224 b hb hp,trace_n225 b hb hp,trace_n226 b hb hp,trace_n227 b hb hp,trace_n229 b hb hp,trace_n230 b hb hp,trace_n231 b hb hp,trace_n232 b hb hp]

def traceValue (b : ℝ) : Fin 5 → ℝ := ![n136 b,n153 b,n236 b,n239 b,n170 b]

theorem traceValue_eq (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    traceValue b = phaseValue b := by
  funext i
  fin_cases i <;> norm_num [traceValue, trace_n136 b hb hp,trace_n153 b hb hp,trace_n170 b hb hp,trace_n236 b hb hp,trace_n239 b hb hp, phaseGradient,phaseMetric,phasePoint,phaseHessian,phaseValue,phaseNormSquared,phaseCoordinate,phaseAbsCoordinate,phaseNodeT,phaseNodeEta,phaseNodeD,phaseNodeK,phaseStep,phaseCurvature,phaseArmijo,phaseWolfe,g0,g1,g2,g3,g4,H0,H1,H4,Sym2.scale,Sym2.mulV,dot,r,rho] <;> ring

def traceNormSquared (b : ℝ) : Fin 5 → ℝ := ![n178 b,n192 b,n206 b,n220 b,n301 b]

theorem traceNormSquared_eq (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    traceNormSquared b = phaseNormSquared b := by
  funext i
  fin_cases i <;> norm_num [traceNormSquared, trace_n178 b hb hp,trace_n192 b hb hp,trace_n206 b hb hp,trace_n220 b hb hp,trace_n301 b hb hp, phaseGradient,phaseMetric,phasePoint,phaseHessian,phaseValue,phaseNormSquared,phaseCoordinate,phaseAbsCoordinate,phaseNodeT,phaseNodeEta,phaseNodeD,phaseNodeK,phaseStep,phaseCurvature,phaseArmijo,phaseWolfe,g0,g1,g2,g3,g4,H0,H1,H4,Sym2.scale,Sym2.mulV,dot,r,rho] <;> ring

def traceCoordinate (b : ℝ) : Fin 4 → ℝ := ![n244 b,n257 b,n269 b,n285 b]

theorem traceCoordinate_eq (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    traceCoordinate b = phaseCoordinate b := by
  funext i
  fin_cases i <;> norm_num [traceCoordinate, trace_n244 b hb hp,trace_n257 b hb hp,trace_n269 b hb hp,trace_n285 b hb hp, phaseGradient,phaseMetric,phasePoint,phaseHessian,phaseValue,phaseNormSquared,phaseCoordinate,phaseAbsCoordinate,phaseNodeT,phaseNodeEta,phaseNodeD,phaseNodeK,phaseStep,phaseCurvature,phaseArmijo,phaseWolfe,g0,g1,g2,g3,g4,H0,H1,H4,Sym2.scale,Sym2.mulV,dot,r,rho] <;> ring

def traceNodeT (b : ℝ) : Fin 4 → ℝ := ![n246 b,n259 b,n272 b,n288 b]

theorem traceNodeT_eq (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    traceNodeT b = phaseNodeT b := by
  funext i
  fin_cases i <;> norm_num [traceNodeT, trace_n246 b hb hp,trace_n259 b hb hp,trace_n272 b hb hp,trace_n288 b hb hp, phaseGradient,phaseMetric,phasePoint,phaseHessian,phaseValue,phaseNormSquared,phaseCoordinate,phaseAbsCoordinate,phaseNodeT,phaseNodeEta,phaseNodeD,phaseNodeK,phaseStep,phaseCurvature,phaseArmijo,phaseWolfe,g0,g1,g2,g3,g4,H0,H1,H4,Sym2.scale,Sym2.mulV,dot,r,rho] <;> ring

def traceNodeEta (b : ℝ) : Fin 4 → ℝ := ![n247 b,n259 b,n273 b,n289 b]

theorem traceNodeEta_eq (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    traceNodeEta b = phaseNodeEta b := by
  funext i
  fin_cases i <;> norm_num [traceNodeEta, trace_n247 b hb hp,trace_n259 b hb hp,trace_n273 b hb hp,trace_n289 b hb hp, phaseGradient,phaseMetric,phasePoint,phaseHessian,phaseValue,phaseNormSquared,phaseCoordinate,phaseAbsCoordinate,phaseNodeT,phaseNodeEta,phaseNodeD,phaseNodeK,phaseStep,phaseCurvature,phaseArmijo,phaseWolfe,g0,g1,g2,g3,g4,H0,H1,H4,Sym2.scale,Sym2.mulV,dot,r,rho] <;> ring

def traceNodeD (b : ℝ) : Fin 4 → ℝ := ![n241 b,n15 b,n275 b,n291 b]

theorem traceNodeD_eq (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    traceNodeD b = phaseNodeD b := by
  funext i
  fin_cases i <;> norm_num [traceNodeD, trace_n15 b hb hp,trace_n241 b hb hp,trace_n275 b hb hp,trace_n291 b hb hp, phaseGradient,phaseMetric,phasePoint,phaseHessian,phaseValue,phaseNormSquared,phaseCoordinate,phaseAbsCoordinate,phaseNodeT,phaseNodeEta,phaseNodeD,phaseNodeK,phaseStep,phaseCurvature,phaseArmijo,phaseWolfe,g0,g1,g2,g3,g4,H0,H1,H4,Sym2.scale,Sym2.mulV,dot,r,rho] <;> ring

def traceNodeK (b : ℝ) : Fin 4 → ℝ := ![n254 b,n266 b,n282 b,n298 b]

theorem traceNodeK_eq (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    traceNodeK b = phaseNodeK b := by
  funext i
  fin_cases i <;> norm_num [traceNodeK, trace_n254 b hb hp,trace_n266 b hb hp,trace_n282 b hb hp,trace_n298 b hb hp, phaseGradient,phaseMetric,phasePoint,phaseHessian,phaseValue,phaseNormSquared,phaseCoordinate,phaseAbsCoordinate,phaseNodeT,phaseNodeEta,phaseNodeD,phaseNodeK,phaseStep,phaseCurvature,phaseArmijo,phaseWolfe,g0,g1,g2,g3,g4,H0,H1,H4,Sym2.scale,Sym2.mulV,dot,r,rho] <;> ring

def traceCurvature (b : ℝ) : Fin 4 → ℝ := ![n64 b,n323 b,n329 b,n335 b]

theorem traceCurvature_eq (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    traceCurvature b = phaseCurvature b := by
  funext i
  fin_cases i <;> norm_num [traceCurvature, trace_n64 b hb hp,trace_n323 b hb hp,trace_n329 b hb hp,trace_n335 b hb hp, phaseGradient,phaseMetric,phasePoint,phaseHessian,phaseValue,phaseNormSquared,phaseCoordinate,phaseAbsCoordinate,phaseNodeT,phaseNodeEta,phaseNodeD,phaseNodeK,phaseStep,phaseCurvature,phaseArmijo,phaseWolfe,g0,g1,g2,g3,g4,H0,H1,H4,Sym2.scale,Sym2.mulV,dot,r,rho] <;> ring

def traceArmijo (b : ℝ) : Fin 4 → ℝ := ![n339 b,n343 b,n350 b,n357 b]

theorem traceArmijo_eq (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    traceArmijo b = phaseArmijo b := by
  funext i
  fin_cases i <;> norm_num [traceArmijo, trace_n339 b hb hp,trace_n343 b hb hp,trace_n350 b hb hp,trace_n357 b hb hp, phaseGradient,phaseMetric,phasePoint,phaseHessian,phaseValue,phaseNormSquared,phaseCoordinate,phaseAbsCoordinate,phaseNodeT,phaseNodeEta,phaseNodeD,phaseNodeK,phaseStep,phaseCurvature,phaseArmijo,phaseWolfe,g0,g1,g2,g3,g4,H0,H1,H4,Sym2.scale,Sym2.mulV,dot,r,rho] <;> ring

def traceWolfe (b : ℝ) : Fin 4 → ℝ := ![n359 b,n364 b,n373 b,n381 b]

theorem traceWolfe_eq (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    traceWolfe b = phaseWolfe b := by
  funext i
  fin_cases i <;> norm_num [traceWolfe, trace_n359 b hb hp,trace_n364 b hb hp,trace_n373 b hb hp,trace_n381 b hb hp, phaseGradient,phaseMetric,phasePoint,phaseHessian,phaseValue,phaseNormSquared,phaseCoordinate,phaseAbsCoordinate,phaseNodeT,phaseNodeEta,phaseNodeD,phaseNodeK,phaseStep,phaseCurvature,phaseArmijo,phaseWolfe,g0,g1,g2,g3,g4,H0,H1,H4,Sym2.scale,Sym2.mulV,dot,r,rho] <;> ring

end
end BFGS.Counterexample
