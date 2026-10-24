import BFGS.Counterexample.Certificates.IntervalBase

/-! Generated arithmetic proofs. Each bound is checked by the Lean kernel. -/
namespace BFGS.Counterexample.Trace
noncomputable section
open BFGS RationalInterval
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false

def n0 (b : ℝ) : ℝ := b
def i0 : RationalInterval := ⟨(22945259791 / 25000000000 : ℚ), (18356207833 / 20000000000 : ℚ)⟩
theorem b0 (b : ℝ) (hb : rootInterval.Contains b) : i0.Contains (n0 b) := by
  convert hb using 1 <;> norm_num [n0, i0, rootInterval, RationalInterval.Contains]

def n1 (b : ℝ) : ℝ := ((882 : ℚ) : ℝ)
def i1 : RationalInterval := ⟨(882 : ℚ), (882 : ℚ)⟩
theorem b1 (b : ℝ) (hb : rootInterval.Contains b) : i1.Contains (n1 b) := by
  exact RationalInterval.contains_point (882 : ℚ)

def n2 (b : ℝ) : ℝ := (n0 b) * (n1 b)
def i2 : RationalInterval := ⟨(10118859567831 / 12500000000 : ℚ), (8095087654353 / 10000000000 : ℚ)⟩
theorem b2 (b : ℝ) (hb : rootInterval.Contains b) : i2.Contains (n2 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b0 b hb) (b1 b hb))
    (by norm_num [i2, i0, i1, RationalInterval.mul]) (by norm_num [i2, i0, i1, RationalInterval.mul])

def n3 (b : ℝ) : ℝ := (n2 b) * (n0 b)
def i3 : RationalInterval := ⟨(232179861572528281383321 / 312500000000000000000 : ℚ), (148595111409656135147049 / 200000000000000000000 : ℚ)⟩
theorem b3 (b : ℝ) (hb : rootInterval.Contains b) : i3.Contains (n3 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2 b hb) (b0 b hb))
    (by norm_num [i3, i2, i0, RationalInterval.mul]) (by norm_num [i3, i2, i0, RationalInterval.mul])

def n4 (b : ℝ) : ℝ := ((463 : ℚ) : ℝ)
def i4 : RationalInterval := ⟨(463 : ℚ), (463 : ℚ)⟩
theorem b4 (b : ℝ) (hb : rootInterval.Contains b) : i4.Contains (n4 b) := by
  exact RationalInterval.contains_point (463 : ℚ)

def n5 (b : ℝ) : ℝ := (n0 b) * (n4 b)
def i5 : RationalInterval := ⟨(10623655283233 / 25000000000 : ℚ), (8498924226679 / 20000000000 : ℚ)⟩
theorem b5 (b : ℝ) (hb : rootInterval.Contains b) : i5.Contains (n5 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b0 b hb) (b4 b hb))
    (by norm_num [i5, i0, i4, RationalInterval.mul]) (by norm_num [i5, i0, i4, RationalInterval.mul])

def n6 (b : ℝ) : ℝ := -(n5 b)
def i6 : RationalInterval := ⟨(-8498924226679 / 20000000000 : ℚ), (-10623655283233 / 25000000000 : ℚ)⟩
theorem b6 (b : ℝ) (hb : rootInterval.Contains b) : i6.Contains (n6 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b5 b hb))
    (by norm_num [i6, i5, RationalInterval.neg]) (by norm_num [i6, i5, RationalInterval.neg])

def n7 (b : ℝ) : ℝ := (n3 b) + (n6 b)
def i7 : RationalInterval := ⟨(99384170530668906383321 / 312500000000000000000 : ℚ), (63605869143792135147049 / 200000000000000000000 : ℚ)⟩
theorem b7 (b : ℝ) (hb : rootInterval.Contains b) : i7.Contains (n7 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3 b hb) (b6 b hb))
    (by norm_num [i7, i3, i6, RationalInterval.add]) (by norm_num [i7, i3, i6, RationalInterval.add])

def n8 (b : ℝ) : ℝ := ((256 : ℚ) : ℝ)
def i8 : RationalInterval := ⟨(256 : ℚ), (256 : ℚ)⟩
theorem b8 (b : ℝ) (hb : rootInterval.Contains b) : i8.Contains (n8 b) := by
  exact RationalInterval.contains_point (256 : ℚ)

def n9 (b : ℝ) : ℝ := ((-256 : ℚ) : ℝ)
def i9 : RationalInterval := ⟨(-256 : ℚ), (-256 : ℚ)⟩
theorem b9 (b : ℝ) (hb : rootInterval.Contains b) : i9.Contains (n9 b) := by
  exact RationalInterval.contains_point (-256 : ℚ)

def n10 (b : ℝ) : ℝ := (n7 b) + (n9 b)
def i10 : RationalInterval := ⟨(19384170530668906383321 / 312500000000000000000 : ℚ), (12405869143792135147049 / 200000000000000000000 : ℚ)⟩
theorem b10 (b : ℝ) (hb : rootInterval.Contains b) : i10.Contains (n10 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b7 b hb) (b9 b hb))
    (by norm_num [i10, i7, i9, RationalInterval.add]) (by norm_num [i10, i7, i9, RationalInterval.add])

def n11 (b : ℝ) : ℝ := ((-9 : ℚ) : ℝ)
def i11 : RationalInterval := ⟨(-9 : ℚ), (-9 : ℚ)⟩
theorem b11 (b : ℝ) (hb : rootInterval.Contains b) : i11.Contains (n11 b) := by
  exact RationalInterval.contains_point (-9 : ℚ)

def n12 (b : ℝ) : ℝ := (n10 b) * (n11 b)
def i12 : RationalInterval := ⟨(-111652822294129216323441 / 200000000000000000000 : ℚ), (-174457534776020157449889 / 312500000000000000000 : ℚ)⟩
theorem b12 (b : ℝ) (hb : rootInterval.Contains b) : i12.Contains (n12 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b10 b hb) (b11 b hb))
    (by norm_num [i12, i10, i11, RationalInterval.mul]) (by norm_num [i12, i10, i11, RationalInterval.mul])

def n13 (b : ℝ) : ℝ := ((2 : ℚ) : ℝ)
def i13 : RationalInterval := ⟨(2 : ℚ), (2 : ℚ)⟩
theorem b13 (b : ℝ) (hb : rootInterval.Contains b) : i13.Contains (n13 b) := by
  exact RationalInterval.contains_point (2 : ℚ)

def n14 (b : ℝ) : ℝ := (n0 b) * (n13 b)
def i14 : RationalInterval := ⟨(22945259791 / 12500000000 : ℚ), (18356207833 / 10000000000 : ℚ)⟩
theorem b14 (b : ℝ) (hb : rootInterval.Contains b) : i14.Contains (n14 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b0 b hb) (b13 b hb))
    (by norm_num [i14, i0, i13, RationalInterval.mul]) (by norm_num [i14, i0, i13, RationalInterval.mul])

def n15 (b : ℝ) : ℝ := ((1 : ℚ) : ℝ)
def i15 : RationalInterval := ⟨(1 : ℚ), (1 : ℚ)⟩
theorem b15 (b : ℝ) (hb : rootInterval.Contains b) : i15.Contains (n15 b) := by
  exact RationalInterval.contains_point (1 : ℚ)

def n16 (b : ℝ) : ℝ := ((-1 : ℚ) : ℝ)
def i16 : RationalInterval := ⟨(-1 : ℚ), (-1 : ℚ)⟩
theorem b16 (b : ℝ) (hb : rootInterval.Contains b) : i16.Contains (n16 b) := by
  exact RationalInterval.contains_point (-1 : ℚ)

def n17 (b : ℝ) : ℝ := (n14 b) + (n16 b)
def i17 : RationalInterval := ⟨(10445259791 / 12500000000 : ℚ), (8356207833 / 10000000000 : ℚ)⟩
theorem b17 (b : ℝ) (hb : rootInterval.Contains b) : i17.Contains (n17 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b14 b hb) (b16 b hb))
    (by norm_num [i17, i14, i16, RationalInterval.add]) (by norm_num [i17, i14, i16, RationalInterval.add])

def n18 (b : ℝ) : ℝ := ((640 : ℚ) : ℝ)
def i18 : RationalInterval := ⟨(640 : ℚ), (640 : ℚ)⟩
theorem b18 (b : ℝ) (hb : rootInterval.Contains b) : i18.Contains (n18 b) := by
  exact RationalInterval.contains_point (640 : ℚ)

def n19 (b : ℝ) : ℝ := (n17 b) * (n18 b)
def i19 : RationalInterval := ⟨(10445259791 / 19531250 : ℚ), (8356207833 / 15625000 : ℚ)⟩
theorem b19 (b : ℝ) (hb : rootInterval.Contains b) : i19.Contains (n19 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b17 b hb) (b18 b hb))
    (by norm_num [i19, i17, i18, RationalInterval.mul]) (by norm_num [i19, i17, i18, RationalInterval.mul])

def n20 (b : ℝ) : ℝ := 1 / (n19 b)
def i20 : RationalInterval := ⟨(934933663227856673631396501 / 500000000000000000000000000000 : ℚ), (373973465300093463228252223 / 200000000000000000000000000000 : ℚ)⟩
theorem b20 (b : ℝ) (hb : rootInterval.Contains b) : i20.Contains (n20 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_inv_of_positive (b19 b hb) (by norm_num [i19]))
    (by norm_num [i20, i19, RationalInterval.inv]) (by norm_num [i20, i19, RationalInterval.inv])

def n21 (b : ℝ) : ℝ := (n12 b) * (n20 b)
def i21 : RationalInterval := ⟨(-130484977699596982211455117131 / 125000000000000000000000000000 : ℚ), (-1043879821221412633154938188809 / 1000000000000000000000000000000 : ℚ)⟩
theorem b21 (b : ℝ) (hb : rootInterval.Contains b) : i21.Contains (n21 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b12 b hb) (b20 b hb))
    (by norm_num [i21, i12, i20, RationalInterval.mul]) (by norm_num [i21, i12, i20, RationalInterval.mul])

def n22 (b : ℝ) : ℝ := ((3087 : ℚ) : ℝ)
def i22 : RationalInterval := ⟨(3087 : ℚ), (3087 : ℚ)⟩
theorem b22 (b : ℝ) (hb : rootInterval.Contains b) : i22.Contains (n22 b) := by
  exact RationalInterval.contains_point (3087 : ℚ)

def n23 (b : ℝ) : ℝ := (n0 b) * (n22 b)
def i23 : RationalInterval := ⟨(70832016974817 / 25000000000 : ℚ), (56665613580471 / 20000000000 : ℚ)⟩
theorem b23 (b : ℝ) (hb : rootInterval.Contains b) : i23.Contains (n23 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b0 b hb) (b22 b hb))
    (by norm_num [i23, i0, i22, RationalInterval.mul]) (by norm_num [i23, i0, i22, RationalInterval.mul])

def n24 (b : ℝ) : ℝ := (n23 b) * (n0 b)
def i24 : RationalInterval := ⟨(1625259031007697969683247 / 625000000000000000000 : ℚ), (1040165779867592946029343 / 400000000000000000000 : ℚ)⟩
theorem b24 (b : ℝ) (hb : rootInterval.Contains b) : i24.Contains (n24 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b23 b hb) (b0 b hb))
    (by norm_num [i24, i23, i0, RationalInterval.mul]) (by norm_num [i24, i23, i0, RationalInterval.mul])

def n25 (b : ℝ) : ℝ := ((2233 : ℚ) : ℝ)
def i25 : RationalInterval := ⟨(2233 : ℚ), (2233 : ℚ)⟩
theorem b25 (b : ℝ) (hb : rootInterval.Contains b) : i25.Contains (n25 b) := by
  exact RationalInterval.contains_point (2233 : ℚ)

def n26 (b : ℝ) : ℝ := (n0 b) * (n25 b)
def i26 : RationalInterval := ⟨(51236765113303 / 25000000000 : ℚ), (40989412091089 / 20000000000 : ℚ)⟩
theorem b26 (b : ℝ) (hb : rootInterval.Contains b) : i26.Contains (n26 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b0 b hb) (b25 b hb))
    (by norm_num [i26, i0, i25, RationalInterval.mul]) (by norm_num [i26, i0, i25, RationalInterval.mul])

def n27 (b : ℝ) : ℝ := -(n26 b)
def i27 : RationalInterval := ⟨(-40989412091089 / 20000000000 : ℚ), (-51236765113303 / 25000000000 : ℚ)⟩
theorem b27 (b : ℝ) (hb : rootInterval.Contains b) : i27.Contains (n27 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b26 b hb))
    (by norm_num [i27, i26, RationalInterval.neg]) (by norm_num [i27, i26, RationalInterval.neg])

def n28 (b : ℝ) : ℝ := (n24 b) + (n27 b)
def i28 : RationalInterval := ⟨(344339903161166719683247 / 625000000000000000000 : ℚ), (220377538054744946029343 / 400000000000000000000 : ℚ)⟩
theorem b28 (b : ℝ) (hb : rootInterval.Contains b) : i28.Contains (n28 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b24 b hb) (b27 b hb))
    (by norm_num [i28, i24, i27, RationalInterval.add]) (by norm_num [i28, i24, i27, RationalInterval.add])

def n29 (b : ℝ) : ℝ := (n28 b) + (n9 b)
def i29 : RationalInterval := ⟨(184339903161166719683247 / 625000000000000000000 : ℚ), (117977538054744946029343 / 400000000000000000000 : ℚ)⟩
theorem b29 (b : ℝ) (hb : rootInterval.Contains b) : i29.Contains (n29 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b28 b hb) (b9 b hb))
    (by norm_num [i29, i28, i9, RationalInterval.add]) (by norm_num [i29, i28, i9, RationalInterval.add])

def n30 (b : ℝ) : ℝ := -(n29 b)
def i30 : RationalInterval := ⟨(-117977538054744946029343 / 400000000000000000000 : ℚ), (-184339903161166719683247 / 625000000000000000000 : ℚ)⟩
theorem b30 (b : ℝ) (hb : rootInterval.Contains b) : i30.Contains (n30 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b29 b hb))
    (by norm_num [i30, i29, RationalInterval.neg]) (by norm_num [i30, i29, RationalInterval.neg])

def n31 (b : ℝ) : ℝ := ((320 : ℚ) : ℝ)
def i31 : RationalInterval := ⟨(320 : ℚ), (320 : ℚ)⟩
theorem b31 (b : ℝ) (hb : rootInterval.Contains b) : i31.Contains (n31 b) := by
  exact RationalInterval.contains_point (320 : ℚ)

def n32 (b : ℝ) : ℝ := (n17 b) * (n31 b)
def i32 : RationalInterval := ⟨(10445259791 / 39062500 : ℚ), (8356207833 / 31250000 : ℚ)⟩
theorem b32 (b : ℝ) (hb : rootInterval.Contains b) : i32.Contains (n32 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b17 b hb) (b31 b hb))
    (by norm_num [i32, i17, i31, RationalInterval.mul]) (by norm_num [i32, i17, i31, RationalInterval.mul])

def n33 (b : ℝ) : ℝ := 1 / (n32 b)
def i33 : RationalInterval := ⟨(747946930582285338905117201 / 200000000000000000000000000000 : ℚ), (373973465300093463228252223 / 100000000000000000000000000000 : ℚ)⟩
theorem b33 (b : ℝ) (hb : rootInterval.Contains b) : i33.Contains (n33 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_inv_of_positive (b32 b hb) (by norm_num [i32]))
    (by norm_num [i33, i32, RationalInterval.inv]) (by norm_num [i33, i32, RationalInterval.inv])

def n34 (b : ℝ) : ℝ := (n30 b) * (n33 b)
def i34 : RationalInterval := ⟨(-1103011718347665378395568078607 / 1000000000000000000000000000000 : ℚ), (-1103011718025842929529532920869 / 1000000000000000000000000000000 : ℚ)⟩
theorem b34 (b : ℝ) (hb : rootInterval.Contains b) : i34.Contains (n34 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b30 b hb) (b33 b hb))
    (by norm_num [i34, i30, i33, RationalInterval.mul]) (by norm_num [i34, i30, i33, RationalInterval.mul])

def n35 (b : ℝ) : ℝ := ((15876 : ℚ) : ℝ)
def i35 : RationalInterval := ⟨(15876 : ℚ), (15876 : ℚ)⟩
theorem b35 (b : ℝ) (hb : rootInterval.Contains b) : i35.Contains (n35 b) := by
  exact RationalInterval.contains_point (15876 : ℚ)

def n36 (b : ℝ) : ℝ := (n0 b) * (n35 b)
def i36 : RationalInterval := ⟨(91069736110479 / 6250000000 : ℚ), (72855788889177 / 5000000000 : ℚ)⟩
theorem b36 (b : ℝ) (hb : rootInterval.Contains b) : i36.Contains (n36 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b0 b hb) (b35 b hb))
    (by norm_num [i36, i0, i35, RationalInterval.mul]) (by norm_num [i36, i0, i35, RationalInterval.mul])

def n37 (b : ℝ) : ℝ := (n36 b) * (n0 b)
def i37 : RationalInterval := ⟨(2089618754152754532449889 / 156250000000000000000 : ℚ), (1337356002686905216323441 / 100000000000000000000 : ℚ)⟩
theorem b37 (b : ℝ) (hb : rootInterval.Contains b) : i37.Contains (n37 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b36 b hb) (b0 b hb))
    (by norm_num [i37, i36, i0, RationalInterval.mul]) (by norm_num [i37, i36, i0, RationalInterval.mul])

def n38 (b : ℝ) : ℝ := (n37 b) * (n0 b)
def i38 : RationalInterval := ⟨(6137196182807131244200376677646489 / 500000000000000000000000000000 : ℚ), (12274392366015469289202453572856677 / 1000000000000000000000000000000 : ℚ)⟩
theorem b38 (b : ℝ) (hb : rootInterval.Contains b) : i38.Contains (n38 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b37 b hb) (b0 b hb))
    (by norm_num [i38, i37, i0, RationalInterval.mul]) (by norm_num [i38, i37, i0, RationalInterval.mul])

def n39 (b : ℝ) : ℝ := ((4316 : ℚ) : ℝ)
def i39 : RationalInterval := ⟨(4316 : ℚ), (4316 : ℚ)⟩
theorem b39 (b : ℝ) (hb : rootInterval.Contains b) : i39.Contains (n39 b) := by
  exact RationalInterval.contains_point (4316 : ℚ)

def n40 (b : ℝ) : ℝ := (n0 b) * (n39 b)
def i40 : RationalInterval := ⟨(24757935314489 / 6250000000 : ℚ), (19806348251807 / 5000000000 : ℚ)⟩
theorem b40 (b : ℝ) (hb : rootInterval.Contains b) : i40.Contains (n40 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b0 b hb) (b39 b hb))
    (by norm_num [i40, i0, i39, RationalInterval.mul]) (by norm_num [i40, i0, i39, RationalInterval.mul])

def n41 (b : ℝ) : ℝ := (n40 b) * (n0 b)
def i41 : RationalInterval := ⟨(568077257679723391411799 / 156250000000000000000 : ℚ), (363569444922945509804231 / 100000000000000000000 : ℚ)⟩
theorem b41 (b : ℝ) (hb : rootInterval.Contains b) : i41.Contains (n41 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b40 b hb) (b0 b hb))
    (by norm_num [i41, i40, i0, RationalInterval.mul]) (by norm_num [i41, i40, i0, RationalInterval.mul])

def n42 (b : ℝ) : ℝ := -(n41 b)
def i42 : RationalInterval := ⟨(-363569444922945509804231 / 100000000000000000000 : ℚ), (-568077257679723391411799 / 156250000000000000000 : ℚ)⟩
theorem b42 (b : ℝ) (hb : rootInterval.Contains b) : i42.Contains (n42 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b41 b hb))
    (by norm_num [i42, i41, RationalInterval.neg]) (by norm_num [i42, i41, RationalInterval.neg])

def n43 (b : ℝ) : ℝ := (n38 b) + (n42 b)
def i43 : RationalInterval := ⟨(4319348958192403695179221677646489 / 500000000000000000000000000000 : ℚ), (8638697916865239584166939972856677 / 1000000000000000000000000000000 : ℚ)⟩
theorem b43 (b : ℝ) (hb : rootInterval.Contains b) : i43.Contains (n43 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b38 b hb) (b42 b hb))
    (by norm_num [i43, i38, i42, RationalInterval.add]) (by norm_num [i43, i38, i42, RationalInterval.add])

def n44 (b : ℝ) : ℝ := ((6815 : ℚ) : ℝ)
def i44 : RationalInterval := ⟨(6815 : ℚ), (6815 : ℚ)⟩
theorem b44 (b : ℝ) (hb : rootInterval.Contains b) : i44.Contains (n44 b) := by
  exact RationalInterval.contains_point (6815 : ℚ)

def n45 (b : ℝ) : ℝ := (n0 b) * (n44 b)
def i45 : RationalInterval := ⟨(31274389095133 / 5000000000 : ℚ), (25019511276379 / 4000000000 : ℚ)⟩
theorem b45 (b : ℝ) (hb : rootInterval.Contains b) : i45.Contains (n45 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b0 b hb) (b44 b hb))
    (by norm_num [i45, i0, i44, RationalInterval.mul]) (by norm_num [i45, i0, i44, RationalInterval.mul])

def n46 (b : ℝ) : ℝ := -(n45 b)
def i46 : RationalInterval := ⟨(-25019511276379 / 4000000000 : ℚ), (-31274389095133 / 5000000000 : ℚ)⟩
theorem b46 (b : ℝ) (hb : rootInterval.Contains b) : i46.Contains (n46 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b45 b hb))
    (by norm_num [i46, i45, RationalInterval.neg]) (by norm_num [i46, i45, RationalInterval.neg])

def n47 (b : ℝ) : ℝ := (n43 b) + (n46 b)
def i47 : RationalInterval := ⟨(1191910048645028695179221677646489 / 500000000000000000000000000000 : ℚ), (2383820097838639584166939972856677 / 1000000000000000000000000000000 : ℚ)⟩
theorem b47 (b : ℝ) (hb : rootInterval.Contains b) : i47.Contains (n47 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b43 b hb) (b46 b hb))
    (by norm_num [i47, i43, i46, RationalInterval.add]) (by norm_num [i47, i43, i46, RationalInterval.add])

def n48 (b : ℝ) : ℝ := ((2304 : ℚ) : ℝ)
def i48 : RationalInterval := ⟨(2304 : ℚ), (2304 : ℚ)⟩
theorem b48 (b : ℝ) (hb : rootInterval.Contains b) : i48.Contains (n48 b) := by
  exact RationalInterval.contains_point (2304 : ℚ)

def n49 (b : ℝ) : ℝ := ((-2304 : ℚ) : ℝ)
def i49 : RationalInterval := ⟨(-2304 : ℚ), (-2304 : ℚ)⟩
theorem b49 (b : ℝ) (hb : rootInterval.Contains b) : i49.Contains (n49 b) := by
  exact RationalInterval.contains_point (-2304 : ℚ)

def n50 (b : ℝ) : ℝ := (n47 b) + (n49 b)
def i50 : RationalInterval := ⟨(39910048645028695179221677646489 / 500000000000000000000000000000 : ℚ), (79820097838639584166939972856677 / 1000000000000000000000000000000 : ℚ)⟩
theorem b50 (b : ℝ) (hb : rootInterval.Contains b) : i50.Contains (n50 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b47 b hb) (b49 b hb))
    (by norm_num [i50, i47, i49, RationalInterval.add]) (by norm_num [i50, i47, i49, RationalInterval.add])

def n51 (b : ℝ) : ℝ := ((1280 : ℚ) : ℝ)
def i51 : RationalInterval := ⟨(1280 : ℚ), (1280 : ℚ)⟩
theorem b51 (b : ℝ) (hb : rootInterval.Contains b) : i51.Contains (n51 b) := by
  exact RationalInterval.contains_point (1280 : ℚ)

def n52 (b : ℝ) : ℝ := (n0 b) * (n51 b)
def i52 : RationalInterval := ⟨(22945259791 / 19531250 : ℚ), (18356207833 / 15625000 : ℚ)⟩
theorem b52 (b : ℝ) (hb : rootInterval.Contains b) : i52.Contains (n52 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b0 b hb) (b51 b hb))
    (by norm_num [i52, i0, i51, RationalInterval.mul]) (by norm_num [i52, i0, i51, RationalInterval.mul])

def n53 (b : ℝ) : ℝ := (n52 b) * (n17 b)
def i53 : RationalInterval := ⟨(239669199488981363681 / 244140625000000000 : ℚ), (153388287678290555889 / 156250000000000000 : ℚ)⟩
theorem b53 (b : ℝ) (hb : rootInterval.Contains b) : i53.Contains (n53 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b52 b hb) (b17 b hb))
    (by norm_num [i53, i52, i17, RationalInterval.mul]) (by norm_num [i53, i52, i17, RationalInterval.mul])

def n54 (b : ℝ) : ℝ := 1 / (n53 b)
def i54 : RationalInterval := ⟨(1018656654722630883857237161 / 1000000000000000000000000000000 : ℚ), (1018656654758110489757398971 / 1000000000000000000000000000000 : ℚ)⟩
theorem b54 (b : ℝ) (hb : rootInterval.Contains b) : i54.Contains (n54 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_inv_of_positive (b53 b hb) (by norm_num [i53]))
    (by norm_num [i54, i53, RationalInterval.inv]) (by norm_num [i54, i53, RationalInterval.inv])

def n55 (b : ℝ) : ℝ := (n50 b) * (n54 b)
def i55 : RationalInterval := ⟨(40654636642562398092394300829 / 500000000000000000000000000000 : ℚ), (16261854769354736836876201677 / 200000000000000000000000000000 : ℚ)⟩
theorem b55 (b : ℝ) (hb : rootInterval.Contains b) : i55.Contains (n55 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b50 b hb) (b54 b hb))
    (by norm_num [i55, i50, i54, RationalInterval.mul]) (by norm_num [i55, i50, i54, RationalInterval.mul])

def n56 (b : ℝ) : ℝ := -(n21 b)
def i56 : RationalInterval := ⟨(1043879821221412633154938188809 / 1000000000000000000000000000000 : ℚ), (130484977699596982211455117131 / 125000000000000000000000000000 : ℚ)⟩
theorem b56 (b : ℝ) (hb : rootInterval.Contains b) : i56.Contains (n56 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b21 b hb))
    (by norm_num [i56, i21, RationalInterval.neg]) (by norm_num [i56, i21, RationalInterval.neg])

def n57 (b : ℝ) : ℝ := ((4 : ℚ) : ℝ)
def i57 : RationalInterval := ⟨(4 : ℚ), (4 : ℚ)⟩
theorem b57 (b : ℝ) (hb : rootInterval.Contains b) : i57.Contains (n57 b) := by
  exact RationalInterval.contains_point (4 : ℚ)

def n58 (b : ℝ) : ℝ := ((1 / 4 : ℚ) : ℝ)
def i58 : RationalInterval := ⟨(1 / 4 : ℚ), (1 / 4 : ℚ)⟩
theorem b58 (b : ℝ) (hb : rootInterval.Contains b) : i58.Contains (n58 b) := by
  exact RationalInterval.contains_point (1 / 4 : ℚ)

def n59 (b : ℝ) : ℝ := (n0 b) * (n58 b)
def i59 : RationalInterval := ⟨(22945259791 / 100000000000 : ℚ), (18356207833 / 80000000000 : ℚ)⟩
theorem b59 (b : ℝ) (hb : rootInterval.Contains b) : i59.Contains (n59 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b0 b hb) (b58 b hb))
    (by norm_num [i59, i0, i58, RationalInterval.mul]) (by norm_num [i59, i0, i58, RationalInterval.mul])

def n60 (b : ℝ) : ℝ := ((1 / 8 : ℚ) : ℝ)
def i60 : RationalInterval := ⟨(1 / 8 : ℚ), (1 / 8 : ℚ)⟩
theorem b60 (b : ℝ) (hb : rootInterval.Contains b) : i60.Contains (n60 b) := by
  exact RationalInterval.contains_point (1 / 8 : ℚ)

def n61 (b : ℝ) : ℝ := (n59 b) + (n60 b)
def i61 : RationalInterval := ⟨(35445259791 / 100000000000 : ℚ), (28356207833 / 80000000000 : ℚ)⟩
theorem b61 (b : ℝ) (hb : rootInterval.Contains b) : i61.Contains (n61 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b59 b hb) (b60 b hb))
    (by norm_num [i61, i59, i60, RationalInterval.add]) (by norm_num [i61, i59, i60, RationalInterval.add])

def n62 (b : ℝ) : ℝ := ((3 / 2 : ℚ) : ℝ)
def i62 : RationalInterval := ⟨(3 / 2 : ℚ), (3 / 2 : ℚ)⟩
theorem b62 (b : ℝ) (hb : rootInterval.Contains b) : i62.Contains (n62 b) := by
  exact RationalInterval.contains_point (3 / 2 : ℚ)

def n63 (b : ℝ) : ℝ := (n0 b) + (n62 b)
def i63 : RationalInterval := ⟨(60445259791 / 25000000000 : ℚ), (48356207833 / 20000000000 : ℚ)⟩
theorem b63 (b : ℝ) (hb : rootInterval.Contains b) : i63.Contains (n63 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b0 b hb) (b62 b hb))
    (by norm_num [i63, i0, i62, RationalInterval.add]) (by norm_num [i63, i0, i62, RationalInterval.add])

def n64 (b : ℝ) : ℝ := ((1 / 2 : ℚ) : ℝ)
def i64 : RationalInterval := ⟨(1 / 2 : ℚ), (1 / 2 : ℚ)⟩
theorem b64 (b : ℝ) (hb : rootInterval.Contains b) : i64.Contains (n64 b) := by
  exact RationalInterval.contains_point (1 / 2 : ℚ)

def n65 (b : ℝ) : ℝ := (n0 b) + (n64 b)
def i65 : RationalInterval := ⟨(35445259791 / 25000000000 : ℚ), (28356207833 / 20000000000 : ℚ)⟩
theorem b65 (b : ℝ) (hb : rootInterval.Contains b) : i65.Contains (n65 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b0 b hb) (b64 b hb))
    (by norm_num [i65, i0, i64, RationalInterval.add]) (by norm_num [i65, i0, i64, RationalInterval.add])

def n66 (b : ℝ) : ℝ := ((0 : ℚ) : ℝ)
def i66 : RationalInterval := ⟨(0 : ℚ), (0 : ℚ)⟩
theorem b66 (b : ℝ) (hb : rootInterval.Contains b) : i66.Contains (n66 b) := by
  exact RationalInterval.contains_point (0 : ℚ)

def n67 (b : ℝ) : ℝ := (n55 b) * (n64 b)
def i67 : RationalInterval := ⟨(40654636642562398092394300829 / 1000000000000000000000000000000 : ℚ), (40654636923386842092190504193 / 1000000000000000000000000000000 : ℚ)⟩
theorem b67 (b : ℝ) (hb : rootInterval.Contains b) : i67.Contains (n67 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b55 b hb) (b64 b hb))
    (by norm_num [i67, i55, i64, RationalInterval.mul]) (by norm_num [i67, i55, i64, RationalInterval.mul])

def n68 (b : ℝ) : ℝ := (n21 b) + (n67 b)
def i68 : RationalInterval := ⟨(-1003225184954213459599246636219 / 1000000000000000000000000000000 : ℚ), (-125403148037253223882843460577 / 125000000000000000000000000000 : ℚ)⟩
theorem b68 (b : ℝ) (hb : rootInterval.Contains b) : i68.Contains (n68 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b21 b hb) (b67 b hb))
    (by norm_num [i68, i21, i67, RationalInterval.add]) (by norm_num [i68, i21, i67, RationalInterval.add])

def n69 (b : ℝ) : ℝ := (n21 b) * (n64 b)
def i69 : RationalInterval := ⟨(-130484977699596982211455117131 / 250000000000000000000000000000 : ℚ), (-130484977652676579144367273601 / 250000000000000000000000000000 : ℚ)⟩
theorem b69 (b : ℝ) (hb : rootInterval.Contains b) : i69.Contains (n69 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b21 b hb) (b64 b hb))
    (by norm_num [i69, i21, i64, RationalInterval.mul]) (by norm_num [i69, i21, i64, RationalInterval.mul])

def n70 (b : ℝ) : ℝ := (n55 b) * (n61 b)
def i70 : RationalInterval := ⟨(28820283150086644166257576281 / 1000000000000000000000000000000 : ℚ), (14410141674683912407796331039 / 500000000000000000000000000000 : ℚ)⟩
theorem b70 (b : ℝ) (hb : rootInterval.Contains b) : i70.Contains (n70 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b55 b hb) (b61 b hb))
    (by norm_num [i70, i55, i61, RationalInterval.mul]) (by norm_num [i70, i55, i61, RationalInterval.mul])

def n71 (b : ℝ) : ℝ := (n69 b) + (n70 b)
def i71 : RationalInterval := ⟨(-493119627648301284679562892243 / 1000000000000000000000000000000 : ℚ), (-246559813630669245880938216163 / 500000000000000000000000000000 : ℚ)⟩
theorem b71 (b : ℝ) (hb : rootInterval.Contains b) : i71.Contains (n71 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b69 b hb) (b70 b hb))
    (by norm_num [i71, i69, i70, RationalInterval.add]) (by norm_num [i71, i69, i70, RationalInterval.add])

def n72 (b : ℝ) : ℝ := (n56 b) * (n64 b)
def i72 : RationalInterval := ⟨(130484977652676579144367273601 / 250000000000000000000000000000 : ℚ), (130484977699596982211455117131 / 250000000000000000000000000000 : ℚ)⟩
theorem b72 (b : ℝ) (hb : rootInterval.Contains b) : i72.Contains (n72 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b56 b hb) (b64 b hb))
    (by norm_num [i72, i56, i64, RationalInterval.mul]) (by norm_num [i72, i56, i64, RationalInterval.mul])

def n73 (b : ℝ) : ℝ := (n34 b) + (n72 b)
def i73 : RationalInterval := ⟨(-581071807736959061818098984203 / 1000000000000000000000000000000 : ℚ), (-116214361445491000136742490469 / 200000000000000000000000000000 : ℚ)⟩
theorem b73 (b : ℝ) (hb : rootInterval.Contains b) : i73.Contains (n73 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b34 b hb) (b72 b hb))
    (by norm_num [i73, i34, i72, RationalInterval.add]) (by norm_num [i73, i34, i72, RationalInterval.add])

def n74 (b : ℝ) : ℝ := (n34 b) * (n64 b)
def i74 : RationalInterval := ⟨(-68938232396729086149723004913 / 125000000000000000000000000000 : ℚ), (-275752929506460732382383230217 / 500000000000000000000000000000 : ℚ)⟩
theorem b74 (b : ℝ) (hb : rootInterval.Contains b) : i74.Contains (n74 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b34 b hb) (b64 b hb))
    (by norm_num [i74, i34, i64, RationalInterval.mul]) (by norm_num [i74, i34, i64, RationalInterval.mul])

def n75 (b : ℝ) : ℝ := (n56 b) * (n61 b)
def i75 : RationalInterval := ⟨(46250739317219507142732705071 / 125000000000000000000000000000 : ℚ), (11562684833544194587273828921 / 31250000000000000000000000000 : ℚ)⟩
theorem b75 (b : ℝ) (hb : rootInterval.Contains b) : i75.Contains (n75 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b56 b hb) (b61 b hb))
    (by norm_num [i75, i56, i61, RationalInterval.mul]) (by norm_num [i75, i56, i61, RationalInterval.mul])

def n76 (b : ℝ) : ℝ := (n74 b) + (n75 b)
def i76 : RationalInterval := ⟨(-11343746539754789503495149921 / 62500000000000000000000000000 : ℚ), (-90749972169753618986001967481 / 500000000000000000000000000000 : ℚ)⟩
theorem b76 (b : ℝ) (hb : rootInterval.Contains b) : i76.Contains (n76 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b74 b hb) (b75 b hb))
    (by norm_num [i76, i74, i75, RationalInterval.add]) (by norm_num [i76, i74, i75, RationalInterval.add])

def n77 (b : ℝ) : ℝ := (n68 b) * (n21 b)
def i77 : RationalInterval := ⟨(261811631507460475782684623227 / 250000000000000000000000000000 : ℚ), (1047246527091396809611158160457 / 1000000000000000000000000000000 : ℚ)⟩
theorem b77 (b : ℝ) (hb : rootInterval.Contains b) : i77.Contains (n77 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b68 b hb) (b21 b hb))
    (by norm_num [i77, i68, i21, RationalInterval.mul]) (by norm_num [i77, i68, i21, RationalInterval.mul])

def n78 (b : ℝ) : ℝ := (n71 b) * (n55 b)
def i78 : RationalInterval := ⟨(-40095198843674800989643526097 / 1000000000000000000000000000000 : ℚ), (-801903970705020939793654487 / 20000000000000000000000000000 : ℚ)⟩
theorem b78 (b : ℝ) (hb : rootInterval.Contains b) : i78.Contains (n78 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b71 b hb) (b55 b hb))
    (by norm_num [i78, i71, i55, RationalInterval.mul]) (by norm_num [i78, i71, i55, RationalInterval.mul])

def n79 (b : ℝ) : ℝ := (n77 b) + (n78 b)
def i79 : RationalInterval := ⟨(1007151327186167102141094966811 / 1000000000000000000000000000000 : ℚ), (1007151328556145762621475436107 / 1000000000000000000000000000000 : ℚ)⟩
theorem b79 (b : ℝ) (hb : rootInterval.Contains b) : i79.Contains (n79 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b77 b hb) (b78 b hb))
    (by norm_num [i79, i77, i78, RationalInterval.add]) (by norm_num [i79, i77, i78, RationalInterval.add])

def n80 (b : ℝ) : ℝ := (n68 b) * (n34 b)
def i80 : RationalInterval := ⟨(553284567049679164774248463449 / 500000000000000000000000000000 : ℚ), (1106569135146001402954359017669 / 1000000000000000000000000000000 : ℚ)⟩
theorem b80 (b : ℝ) (hb : rootInterval.Contains b) : i80.Contains (n80 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b68 b hb) (b34 b hb))
    (by norm_num [i80, i68, i34, RationalInterval.mul]) (by norm_num [i80, i68, i34, RationalInterval.mul])

def n81 (b : ℝ) : ℝ := (n71 b) * (n56 b)
def i81 : RationalInterval := ⟨(-64344703616922160592471221177 / 125000000000000000000000000000 : ℚ), (-514757628346335660133112141279 / 1000000000000000000000000000000 : ℚ)⟩
theorem b81 (b : ℝ) (hb : rootInterval.Contains b) : i81.Contains (n81 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b71 b hb) (b56 b hb))
    (by norm_num [i81, i71, i56, RationalInterval.mul]) (by norm_num [i81, i71, i56, RationalInterval.mul])

def n82 (b : ℝ) : ℝ := (n80 b) + (n81 b)
def i82 : RationalInterval := ⟨(295905752581990522404363578741 / 500000000000000000000000000000 : ℚ), (59181150679966574282124687639 / 100000000000000000000000000000 : ℚ)⟩
theorem b82 (b : ℝ) (hb : rootInterval.Contains b) : i82.Contains (n82 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b80 b hb) (b81 b hb))
    (by norm_num [i82, i80, i81, RationalInterval.add]) (by norm_num [i82, i80, i81, RationalInterval.add])

def n83 (b : ℝ) : ℝ := (n73 b) * (n21 b)
def i83 : RationalInterval := ⟨(606569134245398871289598087339 / 1000000000000000000000000000000 : ℚ), (151642283748843216744415281619 / 250000000000000000000000000000 : ℚ)⟩
theorem b83 (b : ℝ) (hb : rootInterval.Contains b) : i83.Contains (n83 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b73 b hb) (b21 b hb))
    (by norm_num [i83, i73, i21, RationalInterval.mul]) (by norm_num [i83, i73, i21, RationalInterval.mul])

def n84 (b : ℝ) : ℝ := (n76 b) * (n55 b)
def i84 : RationalInterval := ⟨(-1844703587698627165438417179 / 125000000000000000000000000000 : ℚ), (-14757628575535933335094111187 / 1000000000000000000000000000000 : ℚ)⟩
theorem b84 (b : ℝ) (hb : rootInterval.Contains b) : i84.Contains (n84 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b76 b hb) (b55 b hb))
    (by norm_num [i84, i76, i55, RationalInterval.mul]) (by norm_num [i84, i76, i55, RationalInterval.mul])

def n85 (b : ℝ) : ℝ := (n83 b) + (n84 b)
def i85 : RationalInterval := ⟨(591811505543809853966090749907 / 1000000000000000000000000000000 : ℚ), (591811506419836933642567015289 / 1000000000000000000000000000000 : ℚ)⟩
theorem b85 (b : ℝ) (hb : rootInterval.Contains b) : i85.Contains (n85 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b83 b hb) (b84 b hb))
    (by norm_num [i85, i83, i84, RationalInterval.add]) (by norm_num [i85, i83, i84, RationalInterval.add])

def n86 (b : ℝ) : ℝ := (n73 b) * (n34 b)
def i86 : RationalInterval := ⟨(160232253096584138709402576107 / 250000000000000000000000000000 : ℚ), (640929013135327456783516219377 / 1000000000000000000000000000000 : ℚ)⟩
theorem b86 (b : ℝ) (hb : rootInterval.Contains b) : i86.Contains (n86 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b73 b hb) (b34 b hb))
    (by norm_num [i86, i73, i34, RationalInterval.mul]) (by norm_num [i86, i73, i34, RationalInterval.mul])

def n87 (b : ℝ) : ℝ := (n76 b) * (n56 b)
def i87 : RationalInterval := ⟨(-94732064913266184971999556289 / 500000000000000000000000000000 : ℚ), (-94732064724410579698052443383 / 500000000000000000000000000000 : ℚ)⟩
theorem b87 (b : ℝ) (hb : rootInterval.Contains b) : i87.Contains (n87 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b76 b hb) (b56 b hb))
    (by norm_num [i87, i76, i56, RationalInterval.mul]) (by norm_num [i87, i76, i56, RationalInterval.mul])

def n88 (b : ℝ) : ℝ := (n86 b) + (n87 b)
def i88 : RationalInterval := ⟨(9029297651196083697872223837 / 20000000000000000000000000000 : ℚ), (451464883686506297387411332611 / 1000000000000000000000000000000 : ℚ)⟩
theorem b88 (b : ℝ) (hb : rootInterval.Contains b) : i88.Contains (n88 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b86 b hb) (b87 b hb))
    (by norm_num [i88, i86, i87, RationalInterval.add]) (by norm_num [i88, i86, i87, RationalInterval.add])

def n89 (b : ℝ) : ℝ := ((8 / 9 : ℚ) : ℝ)
def i89 : RationalInterval := ⟨(8 / 9 : ℚ), (8 / 9 : ℚ)⟩
theorem b89 (b : ℝ) (hb : rootInterval.Contains b) : i89.Contains (n89 b) := by
  exact RationalInterval.contains_point (8 / 9 : ℚ)

