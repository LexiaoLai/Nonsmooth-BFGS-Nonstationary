import BFGS.Counterexample.Algebra
import BFGS.Counterexample.Root

/-! Lemma 2.5: exact algebra for the four BFGS updates.
The rational residual identities below are checked with field simplification
and polynomial normalization. Their only algebraic hypothesis is the
manuscript quartic equation. -/
namespace BFGS.Counterexample
noncomputable section
open BFGS.Algorithm
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option linter.unusedVariables false

theorem involution_scalar (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) : (p b)^2+q b*t b = 1 := by
  have hb0 : b ≠ 0 := by linarith
  have hb2 : 2*b-1 ≠ 0 := by linarith
  have he : (p b)^2+q b*t b - (1) = quartic b * (9/(409600*b*(2*b - 1))) := by
    dsimp [p,t,q,rho,r,H0,H1,H2,H3,H4,g0,g1,g2,g3,g4,s0,s1,s2,s3,y0,y1,y2,y3,x0,x1,x2,x3,x4,v0,jMul,jtMul,transformH,Sym2.mulV,Sym2.scale,dot,quartic]
    generalize hd : 2*b-1 = d at *
    field_simp [hb0,hb2]
    all_goals
      try rw [← hd]
      ring
  rw [hp, zero_mul] at he
  exact sub_eq_zero.mp he

theorem step2_transform (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) : s2 b = rho • jtMul b (s0 b) := by
  have hb0 : b ≠ 0 := by linarith
  have hb2 : 2*b-1 ≠ 0 := by linarith
  apply Prod.ext
  ·
    have he : (s2 b).1 - ((rho • jtMul b (s0 b)).1) = quartic b * ((7938*b^2 - 2207*b - 2304)/(131072000*b^2*(2*b - 1))) := by
      dsimp [p,t,q,rho,r,H0,H1,H2,H3,H4,g0,g1,g2,g3,g4,s0,s1,s2,s3,y0,y1,y2,y3,x0,x1,x2,x3,x4,v0,jMul,jtMul,transformH,Sym2.mulV,Sym2.scale,dot,quartic]
      generalize hd : 2*b-1 = d at *
      field_simp [hb0,hb2]
      all_goals
        try rw [← hd]
        ring
    rw [hp, zero_mul] at he
    exact sub_eq_zero.mp he
  ·
    have he : (s2 b).2 - ((rho • jtMul b (s0 b)).2) = quartic b * ((441*b - 256)/(13107200*b*(2*b - 1))) := by
      dsimp [p,t,q,rho,r,H0,H1,H2,H3,H4,g0,g1,g2,g3,g4,s0,s1,s2,s3,y0,y1,y2,y3,x0,x1,x2,x3,x4,v0,jMul,jtMul,transformH,Sym2.mulV,Sym2.scale,dot,quartic]
      generalize hd : 2*b-1 = d at *
      field_simp [hb0,hb2]
      all_goals
        try rw [← hd]
        ring
    rw [hp, zero_mul] at he
    exact sub_eq_zero.mp he

theorem step3_transform (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) : s3 b = rho • jtMul b (s1 b) := by
  have hb0 : b ≠ 0 := by linarith
  have hb2 : 2*b-1 ≠ 0 := by linarith
  apply Prod.ext
  ·
    have he : (s3 b).1 - ((rho • jtMul b (s1 b)).1) = quartic b * (49/(1638400*(2*b - 1))) := by
      dsimp [p,t,q,rho,r,H0,H1,H2,H3,H4,g0,g1,g2,g3,g4,s0,s1,s2,s3,y0,y1,y2,y3,x0,x1,x2,x3,x4,v0,jMul,jtMul,transformH,Sym2.mulV,Sym2.scale,dot,quartic]
      generalize hd : 2*b-1 = d at *
      field_simp [hb0,hb2]
      all_goals
        try rw [← hd]
        ring
    rw [hp, zero_mul] at he
    exact sub_eq_zero.mp he
  ·
    have he : (s3 b).2 - ((rho • jtMul b (s1 b)).2) = quartic b * (-(882*b^2 - 953*b - 256)/(32768000*b*(2*b - 1))) := by
      dsimp [p,t,q,rho,r,H0,H1,H2,H3,H4,g0,g1,g2,g3,g4,s0,s1,s2,s3,y0,y1,y2,y3,x0,x1,x2,x3,x4,v0,jMul,jtMul,transformH,Sym2.mulV,Sym2.scale,dot,quartic]
      generalize hd : 2*b-1 = d at *
      field_simp [hb0,hb2]
      all_goals
        try rw [← hd]
        ring
    rw [hp, zero_mul] at he
    exact sub_eq_zero.mp he

theorem curvature0 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) : dot (s0 b) y0 = 1/2 := by
  have hb0 : b ≠ 0 := by linarith
  have hb2 : 2*b-1 ≠ 0 := by linarith
  have he : dot (s0 b) y0 - (1/2) = quartic b * (0) := by
    dsimp [p,t,q,rho,r,H0,H1,H2,H3,H4,g0,g1,g2,g3,g4,s0,s1,s2,s3,y0,y1,y2,y3,x0,x1,x2,x3,x4,v0,jMul,jtMul,transformH,Sym2.mulV,Sym2.scale,dot,quartic]
    generalize hd : 2*b-1 = d at *
    field_simp [hb0,hb2]
    all_goals
      try rw [← hd]
      ring
  rw [hp, zero_mul] at he
  exact sub_eq_zero.mp he

theorem curvature1 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) : dot (s1 b) (y1 b) = 81*b/32 := by
  have hb0 : b ≠ 0 := by linarith
  have hb2 : 2*b-1 ≠ 0 := by linarith
  have he : dot (s1 b) (y1 b) - (81*b/32) = quartic b * (0) := by
    dsimp [p,t,q,rho,r,H0,H1,H2,H3,H4,g0,g1,g2,g3,g4,s0,s1,s2,s3,y0,y1,y2,y3,x0,x1,x2,x3,x4,v0,jMul,jtMul,transformH,Sym2.mulV,Sym2.scale,dot,quartic]
    generalize hd : 2*b-1 = d at *
    field_simp [hb0,hb2]
    all_goals
      try rw [← hd]
      ring
  rw [hp, zero_mul] at he
  exact sub_eq_zero.mp he

theorem curvature2 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) : dot (s2 b) (y2 b) = 4/9 := by
  have hb0 : b ≠ 0 := by linarith
  have hb2 : 2*b-1 ≠ 0 := by linarith
  rw [step2_transform b hb hp]
  have he : dot (rho • jtMul b (s0 b)) (y2 b) - (4/9) = quartic b * (1/(102400*b*(2*b - 1))) := by
    dsimp [p,t,q,rho,r,H0,H1,H2,H3,H4,g0,g1,g2,g3,g4,s0,s1,s2,s3,y0,y1,y2,y3,x0,x1,x2,x3,x4,v0,jMul,jtMul,transformH,Sym2.mulV,Sym2.scale,dot,quartic]
    generalize hd : 2*b-1 = d at *
    field_simp [hb0,hb2]
    all_goals
      try rw [← hd]
      ring
  rw [hp, zero_mul] at he
  exact sub_eq_zero.mp he

theorem curvature3 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) : dot (s3 b) (y3 b) = 9*b/4 := by
  have hb0 : b ≠ 0 := by linarith
  have hb2 : 2*b-1 ≠ 0 := by linarith
  rw [step3_transform b hb hp]
  have he : dot (rho • jtMul b (s1 b)) (y3 b) - (9*b/4) = quartic b * (1/(51200*(2*b - 1))) := by
    dsimp [p,t,q,rho,r,H0,H1,H2,H3,H4,g0,g1,g2,g3,g4,s0,s1,s2,s3,y0,y1,y2,y3,x0,x1,x2,x3,x4,v0,jMul,jtMul,transformH,Sym2.mulV,Sym2.scale,dot,quartic]
    generalize hd : 2*b-1 = d at *
    field_simp [hb0,hb2]
    all_goals
      try rw [← hd]
      ring
  rw [hp, zero_mul] at he
  exact sub_eq_zero.mp he

theorem position0 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) : x1 b = x0 b+s0 b := by
  have hb0 : b ≠ 0 := by linarith
  have hb2 : 2*b-1 ≠ 0 := by linarith
  apply Prod.ext
  ·
    have he : (x1 b).1 - ((x0 b+s0 b).1) = quartic b * (0) := by
      dsimp [p,t,q,rho,r,H0,H1,H2,H3,H4,g0,g1,g2,g3,g4,s0,s1,s2,s3,y0,y1,y2,y3,x0,x1,x2,x3,x4,v0,jMul,jtMul,transformH,Sym2.mulV,Sym2.scale,dot,quartic]
      generalize hd : 2*b-1 = d at *
      field_simp [hb0,hb2]
      all_goals
        try rw [← hd]
        ring
    rw [hp, zero_mul] at he
    exact sub_eq_zero.mp he
  ·
    have he : (x1 b).2 - ((x0 b+s0 b).2) = quartic b * (0) := by
      dsimp [p,t,q,rho,r,H0,H1,H2,H3,H4,g0,g1,g2,g3,g4,s0,s1,s2,s3,y0,y1,y2,y3,x0,x1,x2,x3,x4,v0,jMul,jtMul,transformH,Sym2.mulV,Sym2.scale,dot,quartic]
      generalize hd : 2*b-1 = d at *
      field_simp [hb0,hb2]
      all_goals
        try rw [← hd]
        ring
    rw [hp, zero_mul] at he
    exact sub_eq_zero.mp he

theorem position1 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) : x2 b = x1 b+s1 b := by
  have hb0 : b ≠ 0 := by linarith
  have hb2 : 2*b-1 ≠ 0 := by linarith
  apply Prod.ext
  ·
    have he : (x2 b).1 - ((x1 b+s1 b).1) = quartic b * (9*(2*b + 3)/(217600*b*(2*b - 1))) := by
      dsimp [p,t,q,rho,r,H0,H1,H2,H3,H4,g0,g1,g2,g3,g4,s0,s1,s2,s3,y0,y1,y2,y3,x0,x1,x2,x3,x4,v0,jMul,jtMul,transformH,Sym2.mulV,Sym2.scale,dot,quartic]
      generalize hd : 2*b-1 = d at *
      field_simp [hb0,hb2]
      all_goals
        try rw [← hd]
        ring
    rw [hp, zero_mul] at he
    exact sub_eq_zero.mp he
  ·
    have he : (x2 b).2 - ((x1 b+s1 b).2) = quartic b * (9*(2*b + 1)/(217600*b*(2*b - 1))) := by
      dsimp [p,t,q,rho,r,H0,H1,H2,H3,H4,g0,g1,g2,g3,g4,s0,s1,s2,s3,y0,y1,y2,y3,x0,x1,x2,x3,x4,v0,jMul,jtMul,transformH,Sym2.mulV,Sym2.scale,dot,quartic]
      generalize hd : 2*b-1 = d at *
      field_simp [hb0,hb2]
      all_goals
        try rw [← hd]
        ring
    rw [hp, zero_mul] at he
    exact sub_eq_zero.mp he

theorem position2 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) : x3 b = x2 b+s2 b := by
  have hb0 : b ≠ 0 := by linarith
  have hb2 : 2*b-1 ≠ 0 := by linarith
  rw [step2_transform b hb hp]
  apply Prod.ext
  ·
    have he : (x3 b).1 - ((x2 b+rho • jtMul b (s0 b)).1) = quartic b * (0) := by
      dsimp [p,t,q,rho,r,H0,H1,H2,H3,H4,g0,g1,g2,g3,g4,s0,s1,s2,s3,y0,y1,y2,y3,x0,x1,x2,x3,x4,v0,jMul,jtMul,transformH,Sym2.mulV,Sym2.scale,dot,quartic]
      generalize hd : 2*b-1 = d at *
      field_simp [hb0,hb2]
      all_goals
        try rw [← hd]
        ring
    rw [hp, zero_mul] at he
    exact sub_eq_zero.mp he
  ·
    have he : (x3 b).2 - ((x2 b+rho • jtMul b (s0 b)).2) = quartic b * (0) := by
      dsimp [p,t,q,rho,r,H0,H1,H2,H3,H4,g0,g1,g2,g3,g4,s0,s1,s2,s3,y0,y1,y2,y3,x0,x1,x2,x3,x4,v0,jMul,jtMul,transformH,Sym2.mulV,Sym2.scale,dot,quartic]
      generalize hd : 2*b-1 = d at *
      field_simp [hb0,hb2]
      all_goals
        try rw [← hd]
        ring
    rw [hp, zero_mul] at he
    exact sub_eq_zero.mp he

theorem position3 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) : x4 b = x3 b+s3 b := by
  have hb0 : b ≠ 0 := by linarith
  have hb2 : 2*b-1 ≠ 0 := by linarith
  rw [step3_transform b hb hp]
  apply Prod.ext
  ·
    have he : (x4 b).1 - ((x3 b+rho • jtMul b (s1 b)).1) = quartic b * (-9*(2*b + 3)/(217600*b*(2*b - 1))) := by
      dsimp [p,t,q,rho,r,H0,H1,H2,H3,H4,g0,g1,g2,g3,g4,s0,s1,s2,s3,y0,y1,y2,y3,x0,x1,x2,x3,x4,v0,jMul,jtMul,transformH,Sym2.mulV,Sym2.scale,dot,quartic]
      generalize hd : 2*b-1 = d at *
      field_simp [hb0,hb2]
      all_goals
        try rw [← hd]
        ring
    rw [hp, zero_mul] at he
    exact sub_eq_zero.mp he
  ·
    have he : (x4 b).2 - ((x3 b+rho • jtMul b (s1 b)).2) = quartic b * (-9*(2*b + 1)/(217600*b*(2*b - 1))) := by
      dsimp [p,t,q,rho,r,H0,H1,H2,H3,H4,g0,g1,g2,g3,g4,s0,s1,s2,s3,y0,y1,y2,y3,x0,x1,x2,x3,x4,v0,jMul,jtMul,transformH,Sym2.mulV,Sym2.scale,dot,quartic]
      generalize hd : 2*b-1 = d at *
      field_simp [hb0,hb2]
      all_goals
        try rw [← hd]
        ring
    rw [hp, zero_mul] at he
    exact sub_eq_zero.mp he

theorem update0 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) : H1 b = update (H0 b) (s0 b) y0 := by
  have hb0 : b ≠ 0 := by linarith
  have hb2 : 2*b-1 ≠ 0 := by linarith
  have hc := curvature0 b hb hp
  apply BFGS.Algorithm.Sym2.ext
  ·
    have he : (H1 b).a - ((update (H0 b) (s0 b) y0).a) = quartic b * (0) := by
      simp only [update, hc]
      dsimp [p,t,q,rho,r,H0,H1,H2,H3,H4,g0,g1,g2,g3,g4,s0,s1,s2,s3,y0,y1,y2,y3,x0,x1,x2,x3,x4,v0,jMul,jtMul,transformH,Sym2.mulV,Sym2.scale,dot,quartic]
      generalize hd : 2*b-1 = d at *
      field_simp [hb0,hb2]
      all_goals
        try rw [← hd]
        ring
    rw [hp, zero_mul] at he
    exact sub_eq_zero.mp he
  ·
    have he : (H1 b).b - ((update (H0 b) (s0 b) y0).b) = quartic b * (0) := by
      simp only [update, hc]
      dsimp [p,t,q,rho,r,H0,H1,H2,H3,H4,g0,g1,g2,g3,g4,s0,s1,s2,s3,y0,y1,y2,y3,x0,x1,x2,x3,x4,v0,jMul,jtMul,transformH,Sym2.mulV,Sym2.scale,dot,quartic]
      generalize hd : 2*b-1 = d at *
      field_simp [hb0,hb2]
      all_goals
        try rw [← hd]
        ring
    rw [hp, zero_mul] at he
    exact sub_eq_zero.mp he
  ·
    have he : (H1 b).d - ((update (H0 b) (s0 b) y0).d) = quartic b * (0) := by
      simp only [update, hc]
      dsimp [p,t,q,rho,r,H0,H1,H2,H3,H4,g0,g1,g2,g3,g4,s0,s1,s2,s3,y0,y1,y2,y3,x0,x1,x2,x3,x4,v0,jMul,jtMul,transformH,Sym2.mulV,Sym2.scale,dot,quartic]
      generalize hd : 2*b-1 = d at *
      field_simp [hb0,hb2]
      all_goals
        try rw [← hd]
        ring
    rw [hp, zero_mul] at he
    exact sub_eq_zero.mp he

theorem update1 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) : H2 b = update (H1 b) (s1 b) (y1 b) := by
  have hb0 : b ≠ 0 := by linarith
  have hb2 : 2*b-1 ≠ 0 := by linarith
  have hc := curvature1 b hb hp
  apply BFGS.Algorithm.Sym2.ext
  ·
    have he : (H2 b).a - ((update (H1 b) (s1 b) (y1 b)).a) = quartic b * ((2916*b^3 + 2468*b^2 - 583*b - 256)/(132710400*b^3*(2*b - 1))) := by
      simp only [update, hc]
      dsimp [p,t,q,rho,r,H0,H1,H2,H3,H4,g0,g1,g2,g3,g4,s0,s1,s2,s3,y0,y1,y2,y3,x0,x1,x2,x3,x4,v0,jMul,jtMul,transformH,Sym2.mulV,Sym2.scale,dot,quartic]
      generalize hd : 2*b-1 = d at *
      field_simp [hb0,hb2]
      all_goals
        try rw [← hd]
        ring
    rw [hp, zero_mul] at he
    exact sub_eq_zero.mp he
  ·
    have he : (H2 b).b - ((update (H1 b) (s1 b) (y1 b)).b) = quartic b * ((2*b + 1)*(729*b - 256)/(66355200*b^2*(2*b - 1))) := by
      simp only [update, hc]
      dsimp [p,t,q,rho,r,H0,H1,H2,H3,H4,g0,g1,g2,g3,g4,s0,s1,s2,s3,y0,y1,y2,y3,x0,x1,x2,x3,x4,v0,jMul,jtMul,transformH,Sym2.mulV,Sym2.scale,dot,quartic]
      generalize hd : 2*b-1 = d at *
      field_simp [hb0,hb2]
      all_goals
        try rw [← hd]
        ring
    rw [hp, zero_mul] at he
    exact sub_eq_zero.mp he
  ·
    have he : (H2 b).d - ((update (H1 b) (s1 b) (y1 b)).d) = quartic b * ((729*b - 256)/(33177600*b*(2*b - 1))) := by
      simp only [update, hc]
      dsimp [p,t,q,rho,r,H0,H1,H2,H3,H4,g0,g1,g2,g3,g4,s0,s1,s2,s3,y0,y1,y2,y3,x0,x1,x2,x3,x4,v0,jMul,jtMul,transformH,Sym2.mulV,Sym2.scale,dot,quartic]
      generalize hd : 2*b-1 = d at *
      field_simp [hb0,hb2]
      all_goals
        try rw [← hd]
        ring
    rw [hp, zero_mul] at he
    exact sub_eq_zero.mp he

theorem update2 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) : H3 b = update (H2 b) (s2 b) (y2 b) := by
  have hb0 : b ≠ 0 := by linarith
  have hb2 : 2*b-1 ≠ 0 := by linarith
  rw [step2_transform b hb hp]
  have hc : dot (rho • jtMul b (s0 b)) (y2 b) = 4/9 := by
    rw [← step2_transform b hb hp]
    exact curvature2 b hb hp
  apply BFGS.Algorithm.Sym2.ext
  ·
    have he : (H3 b).a - ((update (H2 b) (rho • jtMul b (s0 b)) (y2 b)).a) = quartic b * (-(7938*b^2 - 2207*b - 2304)*(111152892816*b^7 - 57718849104*b^6 - 149970354912*b^5 + 37763872420*b^4 + 82352659847*b^3 - 3407462144*b^2 - 15098904576*b - 1358954496)/(274877906944000000*b^4*(2*b - 1)^2)) := by
      simp only [update, hc]
      dsimp [p,t,q,rho,r,H0,H1,H2,H3,H4,g0,g1,g2,g3,g4,s0,s1,s2,s3,y0,y1,y2,y3,x0,x1,x2,x3,x4,v0,jMul,jtMul,transformH,Sym2.mulV,Sym2.scale,dot,quartic]
      generalize hd : 2*b-1 = d at *
      field_simp [hb0,hb2]
      all_goals
        try rw [← hd]
        ring
    rw [hp, zero_mul] at he
    exact sub_eq_zero.mp he
  ·
    have he : (H3 b).b - ((update (H2 b) (rho • jtMul b (s0 b)) (y2 b)).b) = quartic b * (-3*(16339475243952*b^8 - 17969717671920*b^7 - 18649761199776*b^6 + 20247194583084*b^5 + 9292910995589*b^4 - 8619628616192*b^3 - 1756075393024*b^2 + 1153098055680*b + 115964116992)/(27487790694400000*b^3*(2*b - 1)^2)) := by
      simp only [update, hc]
      dsimp [p,t,q,rho,r,H0,H1,H2,H3,H4,g0,g1,g2,g3,g4,s0,s1,s2,s3,y0,y1,y2,y3,x0,x1,x2,x3,x4,v0,jMul,jtMul,transformH,Sym2.mulV,Sym2.scale,dot,quartic]
      generalize hd : 2*b-1 = d at *
      field_simp [hb0,hb2]
      all_goals
        try rw [← hd]
        ring
    rw [hp, zero_mul] at he
    exact sub_eq_zero.mp he
  ·
    have he : (H3 b).d - ((update (H2 b) (rho • jtMul b (s0 b)) (y2 b)).d) = quartic b * (-(441*b - 256)*(6175160712*b^6 - 5074398252*b^5 - 7244808858*b^4 + 4882361071*b^3 + 2921494784*b^2 - 1440677888*b - 150994944)/(2748779069440000*b^2*(2*b - 1)^2)) := by
      simp only [update, hc]
      dsimp [p,t,q,rho,r,H0,H1,H2,H3,H4,g0,g1,g2,g3,g4,s0,s1,s2,s3,y0,y1,y2,y3,x0,x1,x2,x3,x4,v0,jMul,jtMul,transformH,Sym2.mulV,Sym2.scale,dot,quartic]
      generalize hd : 2*b-1 = d at *
      field_simp [hb0,hb2]
      all_goals
        try rw [← hd]
        ring
    rw [hp, zero_mul] at he
    exact sub_eq_zero.mp he

theorem update3 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) : H4 b = update (H3 b) (s3 b) (y3 b) := by
  have hb0 : b ≠ 0 := by linarith
  have hb2 : 2*b-1 ≠ 0 := by linarith
  rw [step3_transform b hb hp]
  have hc : dot (rho • jtMul b (s1 b)) (y3 b) = 9*b/4 := by
    rw [← step3_transform b hb hp]
    exact curvature3 b hb hp
  apply BFGS.Algorithm.Sym2.ext
  ·
    have he : (H4 b).a - ((update (H3 b) (rho • jtMul b (s1 b)) (y3 b)).a) = quartic b * (-(1867795524*b^4 - 1384493432*b^3 - 1410983665*b^2 + 1055481856*b + 52494336)/(15288238080000*b*(2*b - 1)^2)) := by
      simp only [update, hc]
      dsimp [p,t,q,rho,r,H0,H1,H2,H3,H4,g0,g1,g2,g3,g4,s0,s1,s2,s3,y0,y1,y2,y3,x0,x1,x2,x3,x4,v0,jMul,jtMul,transformH,Sym2.mulV,Sym2.scale,dot,quartic]
      generalize hd : 2*b-1 = d at *
      field_simp [hb0,hb2]
      all_goals
        try rw [← hd]
        ring
    rw [hp, zero_mul] at he
    exact sub_eq_zero.mp he
  ·
    have he : (H4 b).b - ((update (H3 b) (rho • jtMul b (s1 b)) (y3 b)).b) = quartic b * ((33620319432*b^6 - 61247598804*b^5 - 8229000122*b^4 + 44118988921*b^3 - 2417991424*b^2 - 6269894656*b - 1660944384)/(305764761600000*b^2*(2*b - 1)^2)) := by
      simp only [update, hc]
      dsimp [p,t,q,rho,r,H0,H1,H2,H3,H4,g0,g1,g2,g3,g4,s0,s1,s2,s3,y0,y1,y2,y3,x0,x1,x2,x3,x4,v0,jMul,jtMul,transformH,Sym2.mulV,Sym2.scale,dot,quartic]
      generalize hd : 2*b-1 = d at *
      field_simp [hb0,hb2]
      all_goals
        try rw [← hd]
        ring
    rw [hp, zero_mul] at he
    exact sub_eq_zero.mp he
  ·
    have he : (H4 b).d - ((update (H3 b) (rho • jtMul b (s1 b)) (y3 b)).d) = quartic b * (-(605165749776*b^8 - 1756337684976*b^7 + 867432281184*b^6 + 1537538699788*b^5 - 1036864078401*b^4 - 517877256704*b^3 + 303211646976*b^2 + 49190797312*b - 2415919104)/(6115295232000000*b^3*(2*b - 1)^2)) := by
      simp only [update, hc]
      dsimp [p,t,q,rho,r,H0,H1,H2,H3,H4,g0,g1,g2,g3,g4,s0,s1,s2,s3,y0,y1,y2,y3,x0,x1,x2,x3,x4,v0,jMul,jtMul,transformH,Sym2.mulV,Sym2.scale,dot,quartic]
      generalize hd : 2*b-1 = d at *
      field_simp [hb0,hb2]
      all_goals
        try rw [← hd]
        ring
    rw [hp, zero_mul] at he
    exact sub_eq_zero.mp he


theorem curvature_positive (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    0 < dot (s0 b) y0 ∧ 0 < dot (s1 b) (y1 b) ∧
    0 < dot (s2 b) (y2 b) ∧ 0 < dot (s3 b) (y3 b) := by
  rw [curvature0 b hb hp,curvature1 b hb hp,curvature2 b hb hp,curvature3 b hb hp]
  constructor
  · norm_num
  constructor
  · positivity
  constructor
  · norm_num
  · positivity

theorem H0_positive (b : ℝ) (hb : 1/2 < b) : (H0 b).Positive := by
  rintro ⟨u,v⟩ hne
  have hc : 0 < b/4-1/8 := by linarith
  have he : (H0 b).quad (u,v) = (u+v/2)^2+(b/4-1/8)*v^2 := by
    dsimp [Sym2.quad,Sym2.mulV,dot,H0]
    ring
  rw [he]
  by_cases hv : v = 0
  · subst v
    have hu : u ≠ 0 := by
      intro hu
      apply hne
      simp [hu]
    simpa using sq_pos_of_ne_zero hu
  · have hpos := mul_pos hc (sq_pos_of_ne_zero hv)
    nlinarith [sq_nonneg (u+v/2)]

theorem metrics_positive (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    (H0 b).Positive ∧ (H1 b).Positive ∧ (H2 b).Positive ∧
    (H3 b).Positive ∧ (H4 b).Positive := by
  obtain ⟨hc0,hc1,hc2,hc3⟩ := curvature_positive b hb hp
  have h0 := H0_positive b hb
  have h1 : (H1 b).Positive := by
    rw [update0 b hb hp]
    exact update_positive _ _ _ h0 hc0
  have h2 : (H2 b).Positive := by
    rw [update1 b hb hp]
    exact update_positive _ _ _ h1 hc1
  have h3 : (H3 b).Positive := by
    rw [update2 b hb hp]
    exact update_positive _ _ _ h2 hc2
  have h4 : (H4 b).Positive := by
    rw [update3 b hb hp]
    exact update_positive _ _ _ h3 hc3
  exact ⟨h0,h1,h2,h3,h4⟩

/-- All four equations use the ordinary inverse-BFGS update and unit steps. -/
theorem exact_cycle (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    x1 b = x0 b+s0 b ∧ x2 b = x1 b+s1 b ∧
    x3 b = x2 b+s2 b ∧ x4 b = x3 b+s3 b ∧
    H1 b = update (H0 b) (s0 b) y0 ∧
    H2 b = update (H1 b) (s1 b) (y1 b) ∧
    H3 b = update (H2 b) (s2 b) (y2 b) ∧
    H4 b = update (H3 b) (s3 b) (y3 b) ∧
    H4 b = (H0 b).scale r ∧ x4 b = r • x0 b :=
  ⟨position0 b hb hp,position1 b hb hp,position2 b hb hp,position3 b hb hp,
   update0 b hb hp,update1 b hb hp,update2 b hb hp,update3 b hb hp,rfl,rfl⟩


/-- The two coordinates used by the independent interval verifier. -/
theorem x0_explicit (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    x0 b = (-9*(8978*b^2-6527*b-2304)/(5440*b),
      9*(1764*b^2-2671*b+1488)/2720) := by
  have hb0 : b ≠ 0 := by linarith
  have hb2 : 2*b-1 ≠ 0 := by linarith
  apply Prod.ext
  · dsimp [x0,v0,r,rho,jtMul,p,t,q]
    generalize hd : 2*b-1 = d at *
    field_simp [hb0,hb2]
    all_goals
      try rw [← hd]
      ring
  · dsimp [x0,v0,r,rho,jtMul,p,t,q]
    generalize hd : 2*b-1 = d at *
    field_simp [hb0,hb2]
    all_goals
      try rw [← hd]
      ring

/-- The manuscript matrix J is an involution. -/
theorem jMul_involution (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) (v : Vec) :
    jMul b (jMul b v) = v := by
  rcases v with ⟨u,v⟩
  have h := involution_scalar b hb hp
  apply Prod.ext <;> dsimp [jMul]
  · linear_combination u*h
  · linear_combination v*h

theorem jtMul_involution (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) (v : Vec) :
    jtMul b (jtMul b v) = v := by
  rcases v with ⟨u,v⟩
  have h := involution_scalar b hb hp
  apply Prod.ext <;> dsimp [jtMul]
  · linear_combination u*h
  · linear_combination v*h

theorem j_determinant (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    -(p b)^2-t b*q b = -1 := by
  have h := involution_scalar b hb hp
  nlinarith

end
end BFGS.Counterexample
