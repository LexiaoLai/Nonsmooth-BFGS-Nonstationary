import BFGS.Counterexample.Certificates.IntervalTrace3

/-! Generated arithmetic proofs. Each bound is checked by the Lean kernel. -/
namespace BFGS.Counterexample.Trace
noncomputable section
open BFGS RationalInterval
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false

def n360 (b : ℝ) : ℝ := ((-3 / 5 : ℚ) : ℝ)
def i360 : RationalInterval := ⟨(-3 / 5 : ℚ), (-3 / 5 : ℚ)⟩
theorem b360 (b : ℝ) (hb : rootInterval.Contains b) : i360.Contains (n360 b) := by
  exact RationalInterval.contains_point (-3 / 5 : ℚ)

def n361 (b : ℝ) : ℝ := (n55 b) + (n360 b)
def i361 : RationalInterval := ⟨(-259345363357437601907605699171 / 500000000000000000000000000000 : ℚ), (-103738145230645263163123798323 / 200000000000000000000000000000 : ℚ)⟩
theorem b361 (b : ℝ) (hb : rootInterval.Contains b) : i361.Contains (n361 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b55 b hb) (b360 b hb))
    (by norm_num [i361, i55, i360, RationalInterval.add]) (by norm_num [i361, i55, i360, RationalInterval.add])

def n362 (b : ℝ) : ℝ := (n21 b) * (n302 b)
def i362 : RationalInterval := ⟨(59200946326040969142697862491 / 40000000000000000000000000000 : ℚ), (11562684833544194587273828921 / 7812500000000000000000000000 : ℚ)⟩
theorem b362 (b : ℝ) (hb : rootInterval.Contains b) : i362.Contains (n362 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b21 b hb) (b302 b hb))
    (by norm_num [i362, i21, i302, RationalInterval.mul]) (by norm_num [i362, i21, i302, RationalInterval.mul])

def n363 (b : ℝ) : ℝ := (n361 b) * (n303 b)
def i363 : RationalInterval := ⟨(476059738510728635568287592723 / 1000000000000000000000000000000 : ℚ), (23802986951570136434725637387 / 50000000000000000000000000000 : ℚ)⟩
theorem b363 (b : ℝ) (hb : rootInterval.Contains b) : i363.Contains (n363 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b361 b hb) (b303 b hb))
    (by norm_num [i363, i361, i303, RationalInterval.mul]) (by norm_num [i363, i361, i303, RationalInterval.mul])

def n364 (b : ℝ) : ℝ := (n362 b) + (n363 b)
def i364 : RationalInterval := ⟨(978041698330876432067867077499 / 500000000000000000000000000000 : ℚ), (489020849431264908966390712407 / 250000000000000000000000000000 : ℚ)⟩
theorem b364 (b : ℝ) (hb : rootInterval.Contains b) : i364.Contains (n364 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b362 b hb) (b363 b hb))
    (by norm_num [i364, i362, i363, RationalInterval.add]) (by norm_num [i364, i362, i363, RationalInterval.add])

def n365 (b : ℝ) : ℝ := (n21 b) * (n358 b)
def i365 : RationalInterval := ⟨(-626327892958065514614984562229 / 1000000000000000000000000000000 : ℚ), (-125265578546569515978592582657 / 200000000000000000000000000000 : ℚ)⟩
theorem b365 (b : ℝ) (hb : rootInterval.Contains b) : i365.Contains (n365 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b21 b hb) (b358 b hb))
    (by norm_num [i365, i21, i358, RationalInterval.mul]) (by norm_num [i365, i21, i358, RationalInterval.mul])

def n366 (b : ℝ) : ℝ := (n55 b) * (n358 b)
def i366 : RationalInterval := ⟨(24392781985537438855436580497 / 500000000000000000000000000000 : ℚ), (48785564308064210510628605031 / 1000000000000000000000000000000 : ℚ)⟩
theorem b366 (b : ℝ) (hb : rootInterval.Contains b) : i366.Contains (n366 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b55 b hb) (b358 b hb))
    (by norm_num [i366, i55, i358, RationalInterval.mul]) (by norm_num [i366, i55, i358, RationalInterval.mul])

def n367 (b : ℝ) : ℝ := -(n365 b)
def i367 : RationalInterval := ⟨(125265578546569515978592582657 / 200000000000000000000000000000 : ℚ), (626327892958065514614984562229 / 1000000000000000000000000000000 : ℚ)⟩
theorem b367 (b : ℝ) (hb : rootInterval.Contains b) : i367.Contains (n367 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b365 b hb))
    (by norm_num [i367, i365, RationalInterval.neg]) (by norm_num [i367, i365, RationalInterval.neg])

def n368 (b : ℝ) : ℝ := -(n366 b)
def i368 : RationalInterval := ⟨(-48785564308064210510628605031 / 1000000000000000000000000000000 : ℚ), (-24392781985537438855436580497 / 500000000000000000000000000000 : ℚ)⟩
theorem b368 (b : ℝ) (hb : rootInterval.Contains b) : i368.Contains (n368 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b366 b hb))
    (by norm_num [i368, i366, RationalInterval.neg]) (by norm_num [i368, i366, RationalInterval.neg])

def n369 (b : ℝ) : ℝ := (n34 b) + (n367 b)
def i369 : RationalInterval := ⟨(-238341912807408899251302582661 / 500000000000000000000000000000 : ℚ), (-5958547813347217686431854483 / 12500000000000000000000000000 : ℚ)⟩
theorem b369 (b : ℝ) (hb : rootInterval.Contains b) : i369.Contains (n369 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b34 b hb) (b367 b hb))
    (by norm_num [i369, i34, i367, RationalInterval.add]) (by norm_num [i369, i34, i367, RationalInterval.add])

def n370 (b : ℝ) : ℝ := (n56 b) + (n368 b)
def i370 : RationalInterval := ⟨(497547128456674211322154791889 / 500000000000000000000000000000 : ℚ), (497547128812850489990383888027 / 500000000000000000000000000000 : ℚ)⟩
theorem b370 (b : ℝ) (hb : rootInterval.Contains b) : i370.Contains (n370 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b56 b hb) (b368 b hb))
    (by norm_num [i370, i56, i368, RationalInterval.add]) (by norm_num [i370, i56, i368, RationalInterval.add])

def n371 (b : ℝ) : ℝ := (n369 b) * (n310 b)
def i371 : RationalInterval := ⟨(-17003421137947786987696850959 / 40000000000000000000000000000 : ℚ), (-212542763498765843870335924983 / 500000000000000000000000000000 : ℚ)⟩
theorem b371 (b : ℝ) (hb : rootInterval.Contains b) : i371.Contains (n371 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b369 b hb) (b310 b hb))
    (by norm_num [i371, i369, i310, RationalInterval.mul]) (by norm_num [i371, i369, i310, RationalInterval.mul])

def n372 (b : ℝ) : ℝ := (n370 b) * (n311 b)
def i372 : RationalInterval := ⟨(256987207886754175149838411241 / 500000000000000000000000000000 : ℚ), (256987208726063538309413668141 / 500000000000000000000000000000 : ℚ)⟩
theorem b372 (b : ℝ) (hb : rootInterval.Contains b) : i372.Contains (n372 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b370 b hb) (b311 b hb))
    (by norm_num [i372, i370, i311, RationalInterval.mul]) (by norm_num [i372, i370, i311, RationalInterval.mul])

def n373 (b : ℝ) : ℝ := (n371 b) + (n372 b)
def i373 : RationalInterval := ⟨(88888887324813675607255548507 / 1000000000000000000000000000000 : ℚ), (22222222613648847219538871579 / 250000000000000000000000000000 : ℚ)⟩
theorem b373 (b : ℝ) (hb : rootInterval.Contains b) : i373.Contains (n373 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b371 b hb) (b372 b hb))
    (by norm_num [i373, i371, i372, RationalInterval.add]) (by norm_num [i373, i371, i372, RationalInterval.add])

def n374 (b : ℝ) : ℝ := (n34 b) * (n358 b)
def i374 : RationalInterval := ⟨(-132361406201719845407468169433 / 200000000000000000000000000000 : ℚ), (-661807030815505757717719752521 / 1000000000000000000000000000000 : ℚ)⟩
theorem b374 (b : ℝ) (hb : rootInterval.Contains b) : i374.Contains (n374 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b34 b hb) (b358 b hb))
    (by norm_num [i374, i34, i358, RationalInterval.mul]) (by norm_num [i374, i34, i358, RationalInterval.mul])

def n375 (b : ℝ) : ℝ := (n56 b) * (n358 b)
def i375 : RationalInterval := ⟨(125265578546569515978592582657 / 200000000000000000000000000000 : ℚ), (626327892958065514614984562229 / 1000000000000000000000000000000 : ℚ)⟩
theorem b375 (b : ℝ) (hb : rootInterval.Contains b) : i375.Contains (n375 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b56 b hb) (b358 b hb))
    (by norm_num [i375, i56, i358, RationalInterval.mul]) (by norm_num [i375, i56, i358, RationalInterval.mul])

def n376 (b : ℝ) : ℝ := -(n374 b)
def i376 : RationalInterval := ⟨(661807030815505757717719752521 / 1000000000000000000000000000000 : ℚ), (132361406201719845407468169433 / 200000000000000000000000000000 : ℚ)⟩
theorem b376 (b : ℝ) (hb : rootInterval.Contains b) : i376.Contains (n376 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b374 b hb))
    (by norm_num [i376, i374, RationalInterval.neg]) (by norm_num [i376, i374, RationalInterval.neg])

def n377 (b : ℝ) : ℝ := -(n375 b)
def i377 : RationalInterval := ⟨(-626327892958065514614984562229 / 1000000000000000000000000000000 : ℚ), (-125265578546569515978592582657 / 200000000000000000000000000000 : ℚ)⟩
theorem b377 (b : ℝ) (hb : rootInterval.Contains b) : i377.Contains (n377 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b375 b hb))
    (by norm_num [i377, i375, RationalInterval.neg]) (by norm_num [i377, i375, RationalInterval.neg])

def n378 (b : ℝ) : ℝ := (n376 b) + (n15 b)
def i378 : RationalInterval := ⟨(1661807030815505757717719752521 / 1000000000000000000000000000000 : ℚ), (332361406201719845407468169433 / 200000000000000000000000000000 : ℚ)⟩
theorem b378 (b : ℝ) (hb : rootInterval.Contains b) : i378.Contains (n378 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b376 b hb) (b15 b hb))
    (by norm_num [i378, i376, i15, RationalInterval.add]) (by norm_num [i378, i376, i15, RationalInterval.add])

def n379 (b : ℝ) : ℝ := (n378 b) * (n318 b)
def i379 : RationalInterval := ⟨(1037999500995230592352372613511 / 500000000000000000000000000000 : ℚ), (2075999016479169850816931326559 / 1000000000000000000000000000000 : ℚ)⟩
theorem b379 (b : ℝ) (hb : rootInterval.Contains b) : i379.Contains (n379 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b378 b hb) (b318 b hb))
    (by norm_num [i379, i378, i318, RationalInterval.mul]) (by norm_num [i379, i378, i318, RationalInterval.mul])

def n380 (b : ℝ) : ℝ := (n377 b) * (n319 b)
def i380 : RationalInterval := ⟨(-67451642699848396250079833579 / 200000000000000000000000000000 : ℚ), (-337258209939442752853015651171 / 1000000000000000000000000000000 : ℚ)⟩
theorem b380 (b : ℝ) (hb : rootInterval.Contains b) : i380.Contains (n380 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b377 b hb) (b319 b hb))
    (by norm_num [i380, i377, i319, RationalInterval.mul]) (by norm_num [i380, i377, i319, RationalInterval.mul])

def n381 (b : ℝ) : ℝ := (n379 b) + (n380 b)
def i381 : RationalInterval := ⟨(1738740788491219203454346059127 / 1000000000000000000000000000000 : ℚ), (434685201634931774490978918847 / 250000000000000000000000000000 : ℚ)⟩
theorem b381 (b : ℝ) (hb : rootInterval.Contains b) : i381.Contains (n381 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b379 b hb) (b380 b hb))
    (by norm_num [i381, i379, i380, RationalInterval.add]) (by norm_num [i381, i379, i380, RationalInterval.add])

def n382 (b : ℝ) : ℝ := ((6 : ℚ) : ℝ)
def i382 : RationalInterval := ⟨(6 : ℚ), (6 : ℚ)⟩
theorem b382 (b : ℝ) (hb : rootInterval.Contains b) : i382.Contains (n382 b) := by
  exact RationalInterval.contains_point (6 : ℚ)

def n383 (b : ℝ) : ℝ := (n246 b) + (n15 b)
def i383 : RationalInterval := ⟨(480536192972018355220525544051 / 200000000000000000000000000000 : ℚ), (600670241379549079864077856239 / 250000000000000000000000000000 : ℚ)⟩
theorem b383 (b : ℝ) (hb : rootInterval.Contains b) : i383.Contains (n383 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b246 b hb) (b15 b hb))
    (by norm_num [i383, i246, i15, RationalInterval.add]) (by norm_num [i383, i246, i15, RationalInterval.add])

def n384 (b : ℝ) : ℝ := (n247 b) + (n15 b)
def i384 : RationalInterval := ⟨(517533511973714065330197221559 / 250000000000000000000000000000 : ℚ), (129383378039003633973820424999 / 62500000000000000000000000000 : ℚ)⟩
theorem b384 (b : ℝ) (hb : rootInterval.Contains b) : i384.Contains (n384 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b247 b hb) (b15 b hb))
    (by norm_num [i384, i247, i15, RationalInterval.add]) (by norm_num [i384, i247, i15, RationalInterval.add])

def n385 (b : ℝ) : ℝ := 1 / (n383 b)
def i385 : RationalInterval := ⟨(104050435154665424947512654383 / 250000000000000000000000000000 : ℚ), (208100870366330564059906563877 / 500000000000000000000000000000 : ℚ)⟩
theorem b385 (b : ℝ) (hb : rootInterval.Contains b) : i385.Contains (n385 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_inv_of_positive (b383 b hb) (by norm_num [i383]))
    (by norm_num [i385, i383, RationalInterval.inv]) (by norm_num [i385, i383, RationalInterval.inv])

def n386 (b : ℝ) : ℝ := (n384 b) * (n385 b)
def i386 : RationalInterval := ⟨(430796697023897580937748431763 / 500000000000000000000000000000 : ℚ), (215398348646821088160943331991 / 250000000000000000000000000000 : ℚ)⟩
theorem b386 (b : ℝ) (hb : rootInterval.Contains b) : i386.Contains (n386 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b384 b hb) (b385 b hb))
    (by norm_num [i386, i384, i385, RationalInterval.mul]) (by norm_num [i386, i384, i385, RationalInterval.mul])

def n387 (b : ℝ) : ℝ := -(n246 b)
def i387 : RationalInterval := ⟨(-350670241379549079864077856239 / 250000000000000000000000000000 : ℚ), (-280536192972018355220525544051 / 200000000000000000000000000000 : ℚ)⟩
theorem b387 (b : ℝ) (hb : rootInterval.Contains b) : i387.Contains (n387 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b246 b hb))
    (by norm_num [i387, i246, RationalInterval.neg]) (by norm_num [i387, i246, RationalInterval.neg])

def n388 (b : ℝ) : ℝ := (n259 b) + (n387 b)
def i388 : RationalInterval := ⟨(3369483059499512728959965591623 / 1000000000000000000000000000000 : ℚ), (1684741534525281220995748739849 / 500000000000000000000000000000 : ℚ)⟩
theorem b388 (b : ℝ) (hb : rootInterval.Contains b) : i388.Contains (n388 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b259 b hb) (b387 b hb))
    (by norm_num [i388, i259, i387, RationalInterval.add]) (by norm_num [i388, i259, i387, RationalInterval.add])

def n389 (b : ℝ) : ℝ := -(n247 b)
def i389 : RationalInterval := ⟨(-66883378039003633973820424999 / 62500000000000000000000000000 : ℚ), (-267533511973714065330197221559 / 250000000000000000000000000000 : ℚ)⟩
theorem b389 (b : ℝ) (hb : rootInterval.Contains b) : i389.Contains (n389 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b247 b hb))
    (by norm_num [i389, i247, RationalInterval.neg]) (by norm_num [i389, i247, RationalInterval.neg])

def n390 (b : ℝ) : ℝ := (n259 b) + (n389 b)
def i390 : RationalInterval := ⟨(740405995278730180967030043319 / 200000000000000000000000000000 : ℚ), (3702029986015797956773336313717 / 1000000000000000000000000000000 : ℚ)⟩
theorem b390 (b : ℝ) (hb : rootInterval.Contains b) : i390.Contains (n390 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b259 b hb) (b389 b hb))
    (by norm_num [i390, i259, i389, RationalInterval.add]) (by norm_num [i390, i259, i389, RationalInterval.add])

def n391 (b : ℝ) : ℝ := 1 / (n388 b)
def i391 : RationalInterval := ⟨(59356285786696381005937447519 / 200000000000000000000000000000 : ℚ), (296781429774730883461783800623 / 1000000000000000000000000000000 : ℚ)⟩
theorem b391 (b : ℝ) (hb : rootInterval.Contains b) : i391.Contains (n391 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_inv_of_positive (b388 b hb) (by norm_num [i388]))
    (by norm_num [i391, i388, RationalInterval.inv]) (by norm_num [i391, i388, RationalInterval.inv])

def n392 (b : ℝ) : ℝ := (n390 b) * (n391 b)
def i392 : RationalInterval := ⟨(1098693746348692000511421305919 / 1000000000000000000000000000000 : ℚ), (549346876159347747927252630123 / 500000000000000000000000000000 : ℚ)⟩
theorem b392 (b : ℝ) (hb : rootInterval.Contains b) : i392.Contains (n392 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b390 b hb) (b391 b hb))
    (by norm_num [i392, i390, i391, RationalInterval.mul]) (by norm_num [i392, i390, i391, RationalInterval.mul])

def n393 (b : ℝ) : ℝ := -(n259 b)
def i393 : RationalInterval := ⟨(-4772164033910654218094125199953 / 1000000000000000000000000000000 : ℚ), (-4772164025017709048416277016579 / 1000000000000000000000000000000 : ℚ)⟩
theorem b393 (b : ℝ) (hb : rootInterval.Contains b) : i393.Contains (n393 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b259 b hb))
    (by norm_num [i393, i259, RationalInterval.neg]) (by norm_num [i393, i259, RationalInterval.neg])

def n394 (b : ℝ) : ℝ := (n382 b) + (n393 b)
def i394 : RationalInterval := ⟨(1227835966089345781905874800047 / 1000000000000000000000000000000 : ℚ), (1227835974982290951583722983421 / 1000000000000000000000000000000 : ℚ)⟩
theorem b394 (b : ℝ) (hb : rootInterval.Contains b) : i394.Contains (n394 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b382 b hb) (b393 b hb))
    (by norm_num [i394, i382, i393, RationalInterval.add]) (by norm_num [i394, i382, i393, RationalInterval.add])

def n395 (b : ℝ) : ℝ := 1 / (n394 b)
def i395 : RationalInterval := ⟨(814441033147300457366227779999 / 1000000000000000000000000000000 : ℚ), (162888207809223455920526690817 / 200000000000000000000000000000 : ℚ)⟩
theorem b395 (b : ℝ) (hb : rootInterval.Contains b) : i395.Contains (n395 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_inv_of_positive (b394 b hb) (by norm_num [i394]))
    (by norm_num [i395, i394, RationalInterval.inv]) (by norm_num [i395, i394, RationalInterval.inv])

def n396 (b : ℝ) : ℝ := (n394 b) * (n395 b)
def i396 : RationalInterval := ⟨(62499999547326284267829884843 / 62500000000000000000000000000 : ℚ), (1000000007242779504172576408633 / 1000000000000000000000000000000 : ℚ)⟩
theorem b396 (b : ℝ) (hb : rootInterval.Contains b) : i396.Contains (n396 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b394 b hb) (b395 b hb))
    (by norm_num [i396, i394, i395, RationalInterval.mul]) (by norm_num [i396, i394, i395, RationalInterval.mul])

def n397 (b : ℝ) : ℝ := (n272 b) + (n15 b)
def i397 : RationalInterval := ⟨(1279050971470655456126052160319 / 1000000000000000000000000000000 : ℚ), (639525486658067645808533855091 / 500000000000000000000000000000 : ℚ)⟩
theorem b397 (b : ℝ) (hb : rootInterval.Contains b) : i397.Contains (n397 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b272 b hb) (b15 b hb))
    (by norm_num [i397, i272, i15, RationalInterval.add]) (by norm_num [i397, i272, i15, RationalInterval.add])

def n398 (b : ℝ) : ℝ := (n273 b) + (n15 b)
def i398 : RationalInterval := ⟨(2052004467330947044077714970583 / 1000000000000000000000000000000 : ℚ), (2052004471270993752731922832631 / 1000000000000000000000000000000 : ℚ)⟩
theorem b398 (b : ℝ) (hb : rootInterval.Contains b) : i398.Contains (n398 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b273 b hb) (b15 b hb))
    (by norm_num [i398, i273, i15, RationalInterval.add]) (by norm_num [i398, i273, i15, RationalInterval.add])

def n399 (b : ℝ) : ℝ := 1 / (n397 b)
def i399 : RationalInterval := ⟨(31273186788087015492972915523 / 40000000000000000000000000000 : ℚ), (390914835415119511942621649679 / 500000000000000000000000000000 : ℚ)⟩
theorem b399 (b : ℝ) (hb : rootInterval.Contains b) : i399.Contains (n399 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_inv_of_positive (b397 b hb) (by norm_num [i397]))
    (by norm_num [i399, i397, RationalInterval.inv]) (by norm_num [i399, i397, RationalInterval.inv])

def n400 (b : ℝ) : ℝ := (n398 b) * (n399 b)
def i400 : RationalInterval := ⟨(802158987460371336283578459333 / 500000000000000000000000000000 : ℚ), (802158990157989857753322728327 / 500000000000000000000000000000 : ℚ)⟩
theorem b400 (b : ℝ) (hb : rootInterval.Contains b) : i400.Contains (n400 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b398 b hb) (b399 b hb))
    (by norm_num [i400, i398, i399, RationalInterval.mul]) (by norm_num [i400, i398, i399, RationalInterval.mul])

def n401 (b : ℝ) : ℝ := -(n272 b)
def i401 : RationalInterval := ⟨(-139525486658067645808533855091 / 500000000000000000000000000000 : ℚ), (-279050971470655456126052160319 / 1000000000000000000000000000000 : ℚ)⟩
theorem b401 (b : ℝ) (hb : rootInterval.Contains b) : i401.Contains (n401 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b272 b hb))
    (by norm_num [i401, i272, RationalInterval.neg]) (by norm_num [i401, i272, RationalInterval.neg])

def n402 (b : ℝ) : ℝ := (n288 b) + (n401 b)
def i402 : RationalInterval := ⟨(3050919485000322653409173506453 / 1000000000000000000000000000000 : ℚ), (3050919507196572513142395981941 / 1000000000000000000000000000000 : ℚ)⟩
theorem b402 (b : ℝ) (hb : rootInterval.Contains b) : i402.Contains (n402 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b288 b hb) (b401 b hb))
    (by norm_num [i402, i288, i401, RationalInterval.add]) (by norm_num [i402, i288, i401, RationalInterval.add])

def n403 (b : ℝ) : ℝ := -(n273 b)
def i403 : RationalInterval := ⟨(-1052004471270993752731922832631 / 1000000000000000000000000000000 : ℚ), (-1052004467330947044077714970583 / 1000000000000000000000000000000 : ℚ)⟩
theorem b403 (b : ℝ) (hb : rootInterval.Contains b) : i403.Contains (n403 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b273 b hb))
    (by norm_num [i403, i273, RationalInterval.neg]) (by norm_num [i403, i273, RationalInterval.neg])

def n404 (b : ℝ) : ℝ := (n289 b) + (n403 b)
def i404 : RationalInterval := ⟨(1671723193187228056221242797849 / 500000000000000000000000000000 : ℚ), (3343446422494523434689500334991 / 1000000000000000000000000000000 : ℚ)⟩
theorem b404 (b : ℝ) (hb : rootInterval.Contains b) : i404.Contains (n404 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b289 b hb) (b403 b hb))
    (by norm_num [i404, i289, i403, RationalInterval.add]) (by norm_num [i404, i289, i403, RationalInterval.add])

def n405 (b : ℝ) : ℝ := 1 / (n402 b)
def i405 : RationalInterval := ⟨(32777003707937202555587826729 / 100000000000000000000000000000 : ℚ), (327770039463986131341431322671 / 1000000000000000000000000000000 : ℚ)⟩
theorem b405 (b : ℝ) (hb : rootInterval.Contains b) : i405.Contains (n405 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_inv_of_positive (b402 b hb) (by norm_num [i402]))
    (by norm_num [i405, i402, RationalInterval.inv]) (by norm_num [i405, i402, RationalInterval.inv])

def n406 (b : ℝ) : ℝ := (n404 b) * (n405 b)
def i406 : RationalInterval := ⟨(547940773017423943927085919013 / 500000000000000000000000000000 : ℚ), (1095881565846753194395174109153 / 1000000000000000000000000000000 : ℚ)⟩
theorem b406 (b : ℝ) (hb : rootInterval.Contains b) : i406.Contains (n406 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b404 b hb) (b405 b hb))
    (by norm_num [i406, i404, i405, RationalInterval.mul]) (by norm_num [i406, i404, i405, RationalInterval.mul])

def n407 (b : ℝ) : ℝ := -(n288 b)
def i407 : RationalInterval := ⟨(-166498523933361398463422407113 / 50000000000000000000000000000 : ℚ), (-665994091663291589005248243327 / 200000000000000000000000000000 : ℚ)⟩
theorem b407 (b : ℝ) (hb : rootInterval.Contains b) : i407.Contains (n407 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b288 b hb))
    (by norm_num [i407, i288, RationalInterval.neg]) (by norm_num [i407, i288, RationalInterval.neg])

def n408 (b : ℝ) : ℝ := (n382 b) + (n407 b)
def i408 : RationalInterval := ⟨(133501476066638601536577592887 / 50000000000000000000000000000 : ℚ), (534005908336708410994751756673 / 200000000000000000000000000000 : ℚ)⟩
theorem b408 (b : ℝ) (hb : rootInterval.Contains b) : i408.Contains (n408 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b382 b hb) (b407 b hb))
    (by norm_num [i408, i382, i407, RationalInterval.add]) (by norm_num [i408, i382, i407, RationalInterval.add])

def n409 (b : ℝ) : ℝ := -(n289 b)
def i409 : RationalInterval := ⟨(-2197725444912735239383607652787 / 500000000000000000000000000000 : ℚ), (-4395450857645449865174408428329 / 1000000000000000000000000000000 : ℚ)⟩
theorem b409 (b : ℝ) (hb : rootInterval.Contains b) : i409.Contains (n409 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b289 b hb))
    (by norm_num [i409, i289, RationalInterval.neg]) (by norm_num [i409, i289, RationalInterval.neg])

def n410 (b : ℝ) : ℝ := (n382 b) + (n409 b)
def i410 : RationalInterval := ⟨(802274555087264760616392347213 / 500000000000000000000000000000 : ℚ), (1604549142354550134825591571671 / 1000000000000000000000000000000 : ℚ)⟩
theorem b410 (b : ℝ) (hb : rootInterval.Contains b) : i410.Contains (n410 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b382 b hb) (b409 b hb))
    (by norm_num [i410, i382, i409, RationalInterval.add]) (by norm_num [i410, i382, i409, RationalInterval.add])

def n411 (b : ℝ) : ℝ := 1 / (n408 b)
def i411 : RationalInterval := ⟨(187263845659450434565679006069 / 500000000000000000000000000000 : ℚ), (374527694173523581294017818147 / 1000000000000000000000000000000 : ℚ)⟩
theorem b411 (b : ℝ) (hb : rootInterval.Contains b) : i411.Contains (n411 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_inv_of_positive (b408 b hb) (by norm_num [i408]))
    (by norm_num [i411, i408, RationalInterval.inv]) (by norm_num [i411, i408, RationalInterval.inv])

def n412 (b : ℝ) : ℝ := (n410 b) * (n411 b)
def i412 : RationalInterval := ⟨(600948073841463254397254912581 / 1000000000000000000000000000000 : ℚ), (150237022618538626486806063127 / 250000000000000000000000000000 : ℚ)⟩
theorem b412 (b : ℝ) (hb : rootInterval.Contains b) : i412.Contains (n412 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b410 b hb) (b411 b hb))
    (by norm_num [i412, i410, i411, RationalInterval.mul]) (by norm_num [i412, i410, i411, RationalInterval.mul])

def n413 (b : ℝ) : ℝ := ((-2 : ℚ) : ℝ)
def i413 : RationalInterval := ⟨(-2 : ℚ), (-2 : ℚ)⟩
theorem b413 (b : ℝ) (hb : rootInterval.Contains b) : i413.Contains (n413 b) := by
  exact RationalInterval.contains_point (-2 : ℚ)

def n414 (b : ℝ) : ℝ := ((7 : ℚ) : ℝ)
def i414 : RationalInterval := ⟨(7 : ℚ), (7 : ℚ)⟩
theorem b414 (b : ℝ) (hb : rootInterval.Contains b) : i414.Contains (n414 b) := by
  exact RationalInterval.contains_point (7 : ℚ)

def n415 (b : ℝ) : ℝ := ((1 / 100 : ℚ) : ℝ)
def i415 : RationalInterval := ⟨(1 / 100 : ℚ), (1 / 100 : ℚ)⟩
theorem b415 (b : ℝ) (hb : rootInterval.Contains b) : i415.Contains (n415 b) := by
  exact RationalInterval.contains_point (1 / 100 : ℚ)

def n416 (b : ℝ) : ℝ := ((-1 / 100 : ℚ) : ℝ)
def i416 : RationalInterval := ⟨(-1 / 100 : ℚ), (-1 / 100 : ℚ)⟩
theorem b416 (b : ℝ) (hb : rootInterval.Contains b) : i416.Contains (n416 b) := by
  exact RationalInterval.contains_point (-1 / 100 : ℚ)

def n417 (b : ℝ) : ℝ := ((99 / 100 : ℚ) : ℝ)
def i417 : RationalInterval := ⟨(99 / 100 : ℚ), (99 / 100 : ℚ)⟩
theorem b417 (b : ℝ) (hb : rootInterval.Contains b) : i417.Contains (n417 b) := by
  exact RationalInterval.contains_point (99 / 100 : ℚ)

def n418 (b : ℝ) : ℝ := ((3 : ℚ) : ℝ)
def i418 : RationalInterval := ⟨(3 : ℚ), (3 : ℚ)⟩
theorem b418 (b : ℝ) (hb : rootInterval.Contains b) : i418.Contains (n418 b) := by
  exact RationalInterval.contains_point (3 : ℚ)

def n419 (b : ℝ) : ℝ := ((297 / 100 : ℚ) : ℝ)
def i419 : RationalInterval := ⟨(297 / 100 : ℚ), (297 / 100 : ℚ)⟩
theorem b419 (b : ℝ) (hb : rootInterval.Contains b) : i419.Contains (n419 b) := by
  exact RationalInterval.contains_point (297 / 100 : ℚ)

def n420 (b : ℝ) : ℝ := ((-297 / 100 : ℚ) : ℝ)
def i420 : RationalInterval := ⟨(-297 / 100 : ℚ), (-297 / 100 : ℚ)⟩
theorem b420 (b : ℝ) (hb : rootInterval.Contains b) : i420.Contains (n420 b) := by
  exact RationalInterval.contains_point (-297 / 100 : ℚ)

def n421 (b : ℝ) : ℝ := ((1 / 50 : ℚ) : ℝ)
def i421 : RationalInterval := ⟨(1 / 50 : ℚ), (1 / 50 : ℚ)⟩
theorem b421 (b : ℝ) (hb : rootInterval.Contains b) : i421.Contains (n421 b) := by
  exact RationalInterval.contains_point (1 / 50 : ℚ)

def n422 (b : ℝ) : ℝ := ((-1 / 50 : ℚ) : ℝ)
def i422 : RationalInterval := ⟨(-1 / 50 : ℚ), (-1 / 50 : ℚ)⟩
theorem b422 (b : ℝ) (hb : rootInterval.Contains b) : i422.Contains (n422 b) := by
  exact RationalInterval.contains_point (-1 / 50 : ℚ)

def n423 (b : ℝ) : ℝ := ((99 / 50 : ℚ) : ℝ)
def i423 : RationalInterval := ⟨(99 / 50 : ℚ), (99 / 50 : ℚ)⟩
theorem b423 (b : ℝ) (hb : rootInterval.Contains b) : i423.Contains (n423 b) := by
  exact RationalInterval.contains_point (99 / 50 : ℚ)

def n424 (b : ℝ) : ℝ := ((99 / 25 : ℚ) : ℝ)
def i424 : RationalInterval := ⟨(99 / 25 : ℚ), (99 / 25 : ℚ)⟩
theorem b424 (b : ℝ) (hb : rootInterval.Contains b) : i424.Contains (n424 b) := by
  exact RationalInterval.contains_point (99 / 25 : ℚ)

def n425 (b : ℝ) : ℝ := ((5 : ℚ) : ℝ)
def i425 : RationalInterval := ⟨(5 : ℚ), (5 : ℚ)⟩
theorem b425 (b : ℝ) (hb : rootInterval.Contains b) : i425.Contains (n425 b) := by
  exact RationalInterval.contains_point (5 : ℚ)

def n426 (b : ℝ) : ℝ := ((99 / 125 : ℚ) : ℝ)
def i426 : RationalInterval := ⟨(99 / 125 : ℚ), (99 / 125 : ℚ)⟩
theorem b426 (b : ℝ) (hb : rootInterval.Contains b) : i426.Contains (n426 b) := by
  exact RationalInterval.contains_point (99 / 125 : ℚ)

def n427 (b : ℝ) : ℝ := ((401 / 500 : ℚ) : ℝ)
def i427 : RationalInterval := ⟨(401 / 500 : ℚ), (401 / 500 : ℚ)⟩
theorem b427 (b : ℝ) (hb : rootInterval.Contains b) : i427.Contains (n427 b) := by
  exact RationalInterval.contains_point (401 / 500 : ℚ)

def n428 (b : ℝ) : ℝ := ((-401 / 500 : ℚ) : ℝ)
def i428 : RationalInterval := ⟨(-401 / 500 : ℚ), (-401 / 500 : ℚ)⟩
theorem b428 (b : ℝ) (hb : rootInterval.Contains b) : i428.Contains (n428 b) := by
  exact RationalInterval.contains_point (-401 / 500 : ℚ)

def n429 (b : ℝ) : ℝ := ((99 / 500 : ℚ) : ℝ)
def i429 : RationalInterval := ⟨(99 / 500 : ℚ), (99 / 500 : ℚ)⟩
theorem b429 (b : ℝ) (hb : rootInterval.Contains b) : i429.Contains (n429 b) := by
  exact RationalInterval.contains_point (99 / 500 : ℚ)

def n430 (b : ℝ) : ℝ := (n383 b) * (n415 b)
def i430 : RationalInterval := ⟨(12013404824300458880513138601 / 500000000000000000000000000000 : ℚ), (96107238620727852778252457 / 4000000000000000000000000000 : ℚ)⟩
theorem b430 (b : ℝ) (hb : rootInterval.Contains b) : i430.Contains (n430 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b383 b hb) (b415 b hb))
    (by norm_num [i430, i383, i415, RationalInterval.mul]) (by norm_num [i430, i383, i415, RationalInterval.mul])

def n431 (b : ℝ) : ℝ := (n383 b) * (n241 b)
def i431 : RationalInterval := ⟨(30033512060751147201282846503 / 250000000000000000000000000000 : ℚ), (7508378017244363498300973203 / 62500000000000000000000000000 : ℚ)⟩
theorem b431 (b : ℝ) (hb : rootInterval.Contains b) : i431.Contains (n431 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b383 b hb) (b241 b hb))
    (by norm_num [i431, i383, i241, RationalInterval.mul]) (by norm_num [i431, i383, i241, RationalInterval.mul])

def n432 (b : ℝ) : ℝ := (n383 b) * (n383 b)
def i432 : RationalInterval := ⟨(577287581890102157220922533099 / 100000000000000000000000000000 : ℚ), (2886437911031726045525002322603 / 500000000000000000000000000000 : ℚ)⟩
theorem b432 (b : ℝ) (hb : rootInterval.Contains b) : i432.Contains (n432 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b383 b hb) (b383 b hb))
    (by norm_num [i432, i383, i383, RationalInterval.mul]) (by norm_num [i432, i383, i383, RationalInterval.mul])

def n433 (b : ℝ) : ℝ := (n432 b) * (n254 b)
def i433 : RationalInterval := ⟨(135719568324427222618913612827 / 31250000000000000000000000000 : ℚ), (271439137249573411878118854547 / 62500000000000000000000000000 : ℚ)⟩
theorem b433 (b : ℝ) (hb : rootInterval.Contains b) : i433.Contains (n433 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b432 b hb) (b254 b hb))
    (by norm_num [i433, i432, i254, RationalInterval.mul]) (by norm_num [i433, i432, i254, RationalInterval.mul])

def n434 (b : ℝ) : ℝ := -(n430 b)
def i434 : RationalInterval := ⟨(-96107238620727852778252457 / 4000000000000000000000000000 : ℚ), (-12013404824300458880513138601 / 500000000000000000000000000000 : ℚ)⟩
theorem b434 (b : ℝ) (hb : rootInterval.Contains b) : i434.Contains (n434 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b430 b hb))
    (by norm_num [i434, i430, RationalInterval.neg]) (by norm_num [i434, i430, RationalInterval.neg])

def n435 (b : ℝ) : ℝ := (n383 b) + (n434 b)
def i435 : RationalInterval := ⟨(475730831040981962581612921201 / 200000000000000000000000000000 : ℚ), (1189327077934797700847642573877 / 500000000000000000000000000000 : ℚ)⟩
theorem b435 (b : ℝ) (hb : rootInterval.Contains b) : i435.Contains (n435 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b383 b hb) (b434 b hb))
    (by norm_num [i435, i383, i434, RationalInterval.add]) (by norm_num [i435, i383, i434, RationalInterval.add])

def n436 (b : ℝ) : ℝ := ((46 : ℚ) : ℝ)
def i436 : RationalInterval := ⟨(46 : ℚ), (46 : ℚ)⟩
theorem b436 (b : ℝ) (hb : rootInterval.Contains b) : i436.Contains (n436 b) := by
  exact RationalInterval.contains_point (46 : ℚ)

def n437 (b : ℝ) : ℝ := (n435 b) * (n436 b)
def i437 : RationalInterval := ⟨(10941809113942585139377097187623 / 100000000000000000000000000000 : ℚ), (27354522792500347119495779199171 / 250000000000000000000000000000 : ℚ)⟩
theorem b437 (b : ℝ) (hb : rootInterval.Contains b) : i437.Contains (n437 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b435 b hb) (b436 b hb))
    (by norm_num [i437, i435, i436, RationalInterval.mul]) (by norm_num [i437, i435, i436, RationalInterval.mul])

def n438 (b : ℝ) : ℝ := (n431 b) + (n434 b)
def i438 : RationalInterval := ⟨(48053619293911312805284135881 / 500000000000000000000000000000 : ℚ), (48053619313654449105894647023 / 500000000000000000000000000000 : ℚ)⟩
theorem b438 (b : ℝ) (hb : rootInterval.Contains b) : i438.Contains (n438 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b431 b hb) (b434 b hb))
    (by norm_num [i438, i431, i434, RationalInterval.add]) (by norm_num [i438, i431, i434, RationalInterval.add])

def n439 (b : ℝ) : ℝ := (n438 b) * (n436 b)
def i439 : RationalInterval := ⟨(1105233243759960194521535125263 / 250000000000000000000000000000 : ℚ), (1105233244214052329435576881529 / 250000000000000000000000000000 : ℚ)⟩
theorem b439 (b : ℝ) (hb : rootInterval.Contains b) : i439.Contains (n439 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b438 b hb) (b436 b hb))
    (by norm_num [i439, i438, i436, RationalInterval.mul]) (by norm_num [i439, i438, i436, RationalInterval.mul])

def n440 (b : ℝ) : ℝ := -(n439 b)
def i440 : RationalInterval := ⟨(-1105233244214052329435576881529 / 250000000000000000000000000000 : ℚ), (-1105233243759960194521535125263 / 250000000000000000000000000000 : ℚ)⟩
theorem b440 (b : ℝ) (hb : rootInterval.Contains b) : i440.Contains (n440 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b439 b hb))
    (by norm_num [i440, i439, RationalInterval.neg]) (by norm_num [i440, i439, RationalInterval.neg])

def n441 (b : ℝ) : ℝ := (n433 b) + (n440 b)
def i441 : RationalInterval := ⟨(-19476697618634548484267978913 / 250000000000000000000000000000 : ℚ), (-779067790466661880362388283 / 10000000000000000000000000000 : ℚ)⟩
theorem b441 (b : ℝ) (hb : rootInterval.Contains b) : i441.Contains (n441 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b433 b hb) (b440 b hb))
    (by norm_num [i441, i433, i440, RationalInterval.add]) (by norm_num [i441, i433, i440, RationalInterval.add])

def n442 (b : ℝ) : ℝ := (n383 b) + (n431 b)
def i442 : RationalInterval := ⟨(2522815013103096364907759106267 / 1000000000000000000000000000000 : ℚ), (630703753448526533857281749051 / 250000000000000000000000000000 : ℚ)⟩
theorem b442 (b : ℝ) (hb : rootInterval.Contains b) : i442.Contains (n442 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b383 b hb) (b431 b hb))
    (by norm_num [i442, i383, i431, RationalInterval.add]) (by norm_num [i442, i383, i431, RationalInterval.add])

def n443 (b : ℝ) : ℝ := (n430 b) * (n13 b)
def i443 : RationalInterval := ⟨(12013404824300458880513138601 / 250000000000000000000000000000 : ℚ), (96107238620727852778252457 / 2000000000000000000000000000 : ℚ)⟩
theorem b443 (b : ℝ) (hb : rootInterval.Contains b) : i443.Contains (n443 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b430 b hb) (b13 b hb))
    (by norm_num [i443, i430, i13, RationalInterval.mul]) (by norm_num [i443, i430, i13, RationalInterval.mul])

def n444 (b : ℝ) : ℝ := -(n443 b)
def i444 : RationalInterval := ⟨(-96107238620727852778252457 / 2000000000000000000000000000 : ℚ), (-12013404824300458880513138601 / 250000000000000000000000000000 : ℚ)⟩
theorem b444 (b : ℝ) (hb : rootInterval.Contains b) : i444.Contains (n444 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b443 b hb))
    (by norm_num [i444, i443, RationalInterval.neg]) (by norm_num [i444, i443, RationalInterval.neg])

def n445 (b : ℝ) : ℝ := (n442 b) + (n444 b)
def i445 : RationalInterval := ⟨(2474761393792732438518632877767 / 1000000000000000000000000000000 : ℚ), (12373806972484521499535372209 / 5000000000000000000000000000 : ℚ)⟩
theorem b445 (b : ℝ) (hb : rootInterval.Contains b) : i445.Contains (n445 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b442 b hb) (b444 b hb))
    (by norm_num [i445, i442, i444, RationalInterval.add]) (by norm_num [i445, i442, i444, RationalInterval.add])

def n446 (b : ℝ) : ℝ := (n445 b) * (n13 b)
def i446 : RationalInterval := ⟨(2474761393792732438518632877767 / 500000000000000000000000000000 : ℚ), (12373806972484521499535372209 / 2500000000000000000000000000 : ℚ)⟩
theorem b446 (b : ℝ) (hb : rootInterval.Contains b) : i446.Contains (n446 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b445 b hb) (b13 b hb))
    (by norm_num [i446, i445, i13, RationalInterval.mul]) (by norm_num [i446, i445, i13, RationalInterval.mul])

def n447 (b : ℝ) : ℝ := ((48 : ℚ) : ℝ)
def i447 : RationalInterval := ⟨(48 : ℚ), (48 : ℚ)⟩
theorem b447 (b : ℝ) (hb : rootInterval.Contains b) : i447.Contains (n447 b) := by
  exact RationalInterval.contains_point (48 : ℚ)

def n448 (b : ℝ) : ℝ := ((1 / 48 : ℚ) : ℝ)
def i448 : RationalInterval := ⟨(1 / 48 : ℚ), (1 / 48 : ℚ)⟩
theorem b448 (b : ℝ) (hb : rootInterval.Contains b) : i448.Contains (n448 b) := by
  exact RationalInterval.contains_point (1 / 48 : ℚ)

def n449 (b : ℝ) : ℝ := (n446 b) * (n448 b)
def i449 : RationalInterval := ⟨(51557529037348592469138184953 / 500000000000000000000000000000 : ℚ), (103115058104037679162794768409 / 1000000000000000000000000000000 : ℚ)⟩
theorem b449 (b : ℝ) (hb : rootInterval.Contains b) : i449.Contains (n449 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b446 b hb) (b448 b hb))
    (by norm_num [i449, i446, i448, RationalInterval.mul]) (by norm_num [i449, i446, i448, RationalInterval.mul])

