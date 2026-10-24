import BFGS.Counterexample.Certificates.IntervalTrace5

/-! Generated arithmetic proofs. Each bound is checked by the Lean kernel. -/
namespace BFGS.Counterexample.Trace
noncomputable section
open BFGS RationalInterval
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false

def n540 (b : ℝ) : ℝ := ((1 / 697 : ℚ) : ℝ)
def i540 : RationalInterval := ⟨(1 / 697 : ℚ), (1 / 697 : ℚ)⟩
theorem b540 (b : ℝ) (hb : rootInterval.Contains b) : i540.Contains (n540 b) := by
  exact RationalInterval.contains_point (1 / 697 : ℚ)

def n541 (b : ℝ) : ℝ := (n538 b) * (n540 b)
def i541 : RationalInterval := ⟨(8735561781997104403340948683 / 1000000000000000000000000000000 : ℚ), (2183890464151612992774697521 / 250000000000000000000000000000 : ℚ)⟩
theorem b541 (b : ℝ) (hb : rootInterval.Contains b) : i541.Contains (n541 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b538 b hb) (b540 b hb))
    (by norm_num [i541, i538, i540, RationalInterval.mul]) (by norm_num [i541, i538, i540, RationalInterval.mul])

def n542 (b : ℝ) : ℝ := (n519 b) + (n541 b)
def i542 : RationalInterval := ⟨(39244756632000330937432683747 / 1000000000000000000000000000000 : ℚ), (2452797308035761068907671869 / 62500000000000000000000000000 : ℚ)⟩
theorem b542 (b : ℝ) (hb : rootInterval.Contains b) : i542.Contains (n542 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b519 b hb) (b541 b hb))
    (by norm_num [i542, i519, i541, RationalInterval.add]) (by norm_num [i542, i519, i541, RationalInterval.add])

def n543 (b : ℝ) : ℝ := -(n524 b)
def i543 : RationalInterval := ⟨(-19629647619641848830409252509 / 500000000000000000000000000000 : ℚ), (-39259293981468396646584424181 / 1000000000000000000000000000000 : ℚ)⟩
theorem b543 (b : ℝ) (hb : rootInterval.Contains b) : i543.Contains (n543 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b524 b hb))
    (by norm_num [i543, i524, RationalInterval.neg]) (by norm_num [i543, i524, RationalInterval.neg])

def n544 (b : ℝ) : ℝ := (n523 b) + (n543 b)
def i544 : RationalInterval := ⟨(-20269039694558074191997323351453 / 500000000000000000000000000000 : ℚ), (-5067259806994075797316405896457 / 125000000000000000000000000000 : ℚ)⟩
theorem b544 (b : ℝ) (hb : rootInterval.Contains b) : i544.Contains (n544 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b523 b hb) (b543 b hb))
    (by norm_num [i544, i523, i543, RationalInterval.add]) (by norm_num [i544, i523, i543, RationalInterval.add])

def n545 (b : ℝ) : ℝ := ((485112 : ℚ) : ℝ)
def i545 : RationalInterval := ⟨(485112 : ℚ), (485112 : ℚ)⟩
theorem b545 (b : ℝ) (hb : rootInterval.Contains b) : i545.Contains (n545 b) := by
  exact RationalInterval.contains_point (485112 : ℚ)

def n546 (b : ℝ) : ℝ := ((1 / 485112 : ℚ) : ℝ)
def i546 : RationalInterval := ⟨(1 / 485112 : ℚ), (1 / 485112 : ℚ)⟩
theorem b546 (b : ℝ) (hb : rootInterval.Contains b) : i546.Contains (n546 b) := by
  exact RationalInterval.contains_point (1 / 485112 : ℚ)

def n547 (b : ℝ) : ℝ := (n544 b) * (n546 b)
def i547 : RationalInterval := ⟨(-20891092876034889048299489 / 250000000000000000000000000000 : ℚ), (-16712873916107045951669407 / 200000000000000000000000000000 : ℚ)⟩
theorem b547 (b : ℝ) (hb : rootInterval.Contains b) : i547.Contains (n547 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b544 b hb) (b546 b hb))
    (by norm_num [i547, i544, i546, RationalInterval.mul]) (by norm_num [i547, i544, i546, RationalInterval.mul])

def n548 (b : ℝ) : ℝ := (n542 b) + (n547 b)
def i548 : RationalInterval := ⟨(39161192260496191381239485791 / 1000000000000000000000000000000 : ℚ), (39161192558991641872764402869 / 1000000000000000000000000000000 : ℚ)⟩
theorem b548 (b : ℝ) (hb : rootInterval.Contains b) : i548.Contains (n548 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b542 b hb) (b547 b hb))
    (by norm_num [i548, i542, i547, RationalInterval.add]) (by norm_num [i548, i542, i547, RationalInterval.add])

def n549 (b : ℝ) : ℝ := -(n548 b)
def i549 : RationalInterval := ⟨(-39161192558991641872764402869 / 1000000000000000000000000000000 : ℚ), (-39161192260496191381239485791 / 1000000000000000000000000000000 : ℚ)⟩
theorem b549 (b : ℝ) (hb : rootInterval.Contains b) : i549.Contains (n549 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b548 b hb))
    (by norm_num [i549, i548, RationalInterval.neg]) (by norm_num [i549, i548, RationalInterval.neg])

def n550 (b : ℝ) : ℝ := (n404 b) + (n549 b)
def i550 : RationalInterval := ⟨(3304285193815464470569721192829 / 1000000000000000000000000000000 : ℚ), (8260713075585068108270652123 / 2500000000000000000000000000 : ℚ)⟩
theorem b550 (b : ℝ) (hb : rootInterval.Contains b) : i550.Contains (n550 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b404 b hb) (b549 b hb))
    (by norm_num [i550, i404, i549, RationalInterval.add]) (by norm_num [i550, i404, i549, RationalInterval.add])

def n551 (b : ℝ) : ℝ := (n408 b) * (n415 b)
def i551 : RationalInterval := ⟨(26700295213327720307315518577 / 1000000000000000000000000000000 : ℚ), (13350147708417710274868793917 / 500000000000000000000000000000 : ℚ)⟩
theorem b551 (b : ℝ) (hb : rootInterval.Contains b) : i551.Contains (n551 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b408 b hb) (b415 b hb))
    (by norm_num [i551, i408, i415, RationalInterval.mul]) (by norm_num [i551, i408, i415, RationalInterval.mul])

def n552 (b : ℝ) : ℝ := (n408 b) * (n291 b)
def i552 : RationalInterval := ⟨(131996812343326762411725721969 / 50000000000000000000000000000 : ℚ), (659984067008282800702181624067 / 250000000000000000000000000000 : ℚ)⟩
theorem b552 (b : ℝ) (hb : rootInterval.Contains b) : i552.Contains (n552 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b408 b hb) (b291 b hb))
    (by norm_num [i552, i408, i291, RationalInterval.mul]) (by norm_num [i552, i408, i291, RationalInterval.mul])

def n553 (b : ℝ) : ℝ := (n408 b) * (n408 b)
def i553 : RationalInterval := ⟨(7129057644788511732743462597053 / 1000000000000000000000000000000 : ℚ), (891132219182853205007349200463 / 125000000000000000000000000000 : ℚ)⟩
theorem b553 (b : ℝ) (hb : rootInterval.Contains b) : i553.Contains (n553 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b408 b hb) (b408 b hb))
    (by norm_num [i553, i408, i408, RationalInterval.mul]) (by norm_num [i553, i408, i408, RationalInterval.mul])

def n554 (b : ℝ) : ℝ := (n553 b) * (n298 b)
def i554 : RationalInterval := ⟨(6013718763298988575904026957 / 200000000000000000000000000000 : ℚ), (30068594800699730798015047561 / 1000000000000000000000000000000 : ℚ)⟩
theorem b554 (b : ℝ) (hb : rootInterval.Contains b) : i554.Contains (n554 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b553 b hb) (b298 b hb))
    (by norm_num [i554, i553, i298, RationalInterval.mul]) (by norm_num [i554, i553, i298, RationalInterval.mul])

def n555 (b : ℝ) : ℝ := -(n551 b)
def i555 : RationalInterval := ⟨(-13350147708417710274868793917 / 500000000000000000000000000000 : ℚ), (-26700295213327720307315518577 / 1000000000000000000000000000000 : ℚ)⟩
theorem b555 (b : ℝ) (hb : rootInterval.Contains b) : i555.Contains (n555 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b551 b hb))
    (by norm_num [i555, i551, RationalInterval.neg]) (by norm_num [i555, i551, RationalInterval.neg])

def n556 (b : ℝ) : ℝ := (n552 b) + (n555 b)
def i556 : RationalInterval := ⟨(1306617975724849913842388425773 / 500000000000000000000000000000 : ℚ), (2613235972819803482501410977691 / 1000000000000000000000000000000 : ℚ)⟩
theorem b556 (b : ℝ) (hb : rootInterval.Contains b) : i556.Contains (n556 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b552 b hb) (b555 b hb))
    (by norm_num [i556, i552, i555, RationalInterval.add]) (by norm_num [i556, i552, i555, RationalInterval.add])

def n557 (b : ℝ) : ℝ := (n556 b) * (n425 b)
def i557 : RationalInterval := ⟨(1306617975724849913842388425773 / 100000000000000000000000000000 : ℚ), (2613235972819803482501410977691 / 200000000000000000000000000000 : ℚ)⟩
theorem b557 (b : ℝ) (hb : rootInterval.Contains b) : i557.Contains (n557 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b556 b hb) (b425 b hb))
    (by norm_num [i557, i556, i425, RationalInterval.mul]) (by norm_num [i557, i556, i425, RationalInterval.mul])

def n558 (b : ℝ) : ℝ := (n554 b) + (n557 b)
def i558 : RationalInterval := ⟨(2619249670212998816260680878503 / 200000000000000000000000000000 : ℚ), (818515528681232321456566871001 / 62500000000000000000000000000 : ℚ)⟩
theorem b558 (b : ℝ) (hb : rootInterval.Contains b) : i558.Contains (n558 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b554 b hb) (b557 b hb))
    (by norm_num [i558, i554, i557, RationalInterval.add]) (by norm_num [i558, i554, i557, RationalInterval.add])

def n559 (b : ℝ) : ℝ := (n408 b) + (n555 b)
def i559 : RationalInterval := ⟨(1321664612957968305090907134953 / 500000000000000000000000000000 : ℚ), (660832311617553583666610816197 / 250000000000000000000000000000 : ℚ)⟩
theorem b559 (b : ℝ) (hb : rootInterval.Contains b) : i559.Contains (n559 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b408 b hb) (b555 b hb))
    (by norm_num [i559, i408, i555, RationalInterval.add]) (by norm_num [i559, i408, i555, RationalInterval.add])

def n560 (b : ℝ) : ℝ := (n559 b) * (n425 b)
def i560 : RationalInterval := ⟨(1321664612957968305090907134953 / 100000000000000000000000000000 : ℚ), (660832311617553583666610816197 / 50000000000000000000000000000 : ℚ)⟩
theorem b560 (b : ℝ) (hb : rootInterval.Contains b) : i560.Contains (n560 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b559 b hb) (b425 b hb))
    (by norm_num [i560, i559, i425, RationalInterval.mul]) (by norm_num [i560, i559, i425, RationalInterval.mul])

def n561 (b : ℝ) : ℝ := -(n560 b)
def i561 : RationalInterval := ⟨(-660832311617553583666610816197 / 50000000000000000000000000000 : ℚ), (-1321664612957968305090907134953 / 100000000000000000000000000000 : ℚ)⟩
theorem b561 (b : ℝ) (hb : rootInterval.Contains b) : i561.Contains (n561 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b560 b hb))
    (by norm_num [i561, i560, RationalInterval.neg]) (by norm_num [i561, i560, RationalInterval.neg])

def n562 (b : ℝ) : ℝ := (n552 b) + (n408 b)
def i562 : RationalInterval := ⟨(33187286051245670493537914357 / 6250000000000000000000000000 : ℚ), (5309965809716673257782485279633 / 1000000000000000000000000000000 : ℚ)⟩
theorem b562 (b : ℝ) (hb : rootInterval.Contains b) : i562.Contains (n562 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b552 b hb) (b408 b hb))
    (by norm_num [i562, i552, i408, RationalInterval.add]) (by norm_num [i562, i552, i408, RationalInterval.add])

def n563 (b : ℝ) : ℝ := (n551 b) * (n13 b)
def i563 : RationalInterval := ⟨(26700295213327720307315518577 / 500000000000000000000000000000 : ℚ), (13350147708417710274868793917 / 250000000000000000000000000000 : ℚ)⟩
theorem b563 (b : ℝ) (hb : rootInterval.Contains b) : i563.Contains (n563 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b551 b hb) (b13 b hb))
    (by norm_num [i563, i551, i13, RationalInterval.mul]) (by norm_num [i563, i551, i13, RationalInterval.mul])

def n564 (b : ℝ) : ℝ := -(n563 b)
def i564 : RationalInterval := ⟨(-13350147708417710274868793917 / 250000000000000000000000000000 : ℚ), (-26700295213327720307315518577 / 500000000000000000000000000000 : ℚ)⟩
theorem b564 (b : ℝ) (hb : rootInterval.Contains b) : i564.Contains (n564 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b563 b hb))
    (by norm_num [i564, i563, RationalInterval.neg]) (by norm_num [i564, i563, RationalInterval.neg])

def n565 (b : ℝ) : ℝ := (n562 b) + (n564 b)
def i565 : RationalInterval := ⟨(1314141294341409109466647780363 / 250000000000000000000000000000 : ℚ), (5256565219290017817167854242479 / 1000000000000000000000000000000 : ℚ)⟩
theorem b565 (b : ℝ) (hb : rootInterval.Contains b) : i565.Contains (n565 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b562 b hb) (b564 b hb))
    (by norm_num [i565, i562, i564, RationalInterval.add]) (by norm_num [i565, i562, i564, RationalInterval.add])

def n566 (b : ℝ) : ℝ := (n565 b) * (n13 b)
def i566 : RationalInterval := ⟨(1314141294341409109466647780363 / 125000000000000000000000000000 : ℚ), (5256565219290017817167854242479 / 500000000000000000000000000000 : ℚ)⟩
theorem b566 (b : ℝ) (hb : rootInterval.Contains b) : i566.Contains (n566 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b565 b hb) (b13 b hb))
    (by norm_num [i566, i565, i13, RationalInterval.mul]) (by norm_num [i566, i565, i13, RationalInterval.mul])

def n567 (b : ℝ) : ℝ := ((1 / 7 : ℚ) : ℝ)
def i567 : RationalInterval := ⟨(1 / 7 : ℚ), (1 / 7 : ℚ)⟩
theorem b567 (b : ℝ) (hb : rootInterval.Contains b) : i567.Contains (n567 b) := by
  exact RationalInterval.contains_point (1 / 7 : ℚ)

def n568 (b : ℝ) : ℝ := (n566 b) * (n567 b)
def i568 : RationalInterval := ⟨(15018757649616104108190260347 / 10000000000000000000000000000 : ℚ), (1501875776940005090619386926423 / 1000000000000000000000000000000 : ℚ)⟩
theorem b568 (b : ℝ) (hb : rootInterval.Contains b) : i568.Contains (n568 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b566 b hb) (b567 b hb))
    (by norm_num [i568, i566, i567, RationalInterval.mul]) (by norm_num [i568, i566, i567, RationalInterval.mul])

def n569 (b : ℝ) : ℝ := (n551 b) + (n568 b)
def i569 : RationalInterval := ⟨(1528576060174938131126341553277 / 1000000000000000000000000000000 : ℚ), (1528576072356840511169124514257 / 1000000000000000000000000000000 : ℚ)⟩
theorem b569 (b : ℝ) (hb : rootInterval.Contains b) : i569.Contains (n569 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b551 b hb) (b568 b hb))
    (by norm_num [i569, i551, i568, RationalInterval.add]) (by norm_num [i569, i551, i568, RationalInterval.add])

def n570 (b : ℝ) : ℝ := ((42 : ℚ) : ℝ)
def i570 : RationalInterval := ⟨(42 : ℚ), (42 : ℚ)⟩
theorem b570 (b : ℝ) (hb : rootInterval.Contains b) : i570.Contains (n570 b) := by
  exact RationalInterval.contains_point (42 : ℚ)

def n571 (b : ℝ) : ℝ := ((1 / 42 : ℚ) : ℝ)
def i571 : RationalInterval := ⟨(1 / 42 : ℚ), (1 / 42 : ℚ)⟩
theorem b571 (b : ℝ) (hb : rootInterval.Contains b) : i571.Contains (n571 b) := by
  exact RationalInterval.contains_point (1 / 42 : ℚ)

def n572 (b : ℝ) : ℝ := (n554 b) * (n571 b)
def i572 : RationalInterval := ⟨(5727351203141893881813359 / 8000000000000000000000000000 : ℚ), (143183784765236813323881179 / 200000000000000000000000000000 : ℚ)⟩
theorem b572 (b : ℝ) (hb : rootInterval.Contains b) : i572.Contains (n572 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b554 b hb) (b571 b hb))
    (by norm_num [i572, i554, i571, RationalInterval.mul]) (by norm_num [i572, i554, i571, RationalInterval.mul])

def n573 (b : ℝ) : ℝ := (n569 b) + (n572 b)
def i573 : RationalInterval := ⟨(95580748692208179241348013947 / 62500000000000000000000000000 : ℚ), (191161498910083336904467990019 / 125000000000000000000000000000 : ℚ)⟩
theorem b573 (b : ℝ) (hb : rootInterval.Contains b) : i573.Contains (n573 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b569 b hb) (b572 b hb))
    (by norm_num [i573, i569, i572, RationalInterval.add]) (by norm_num [i573, i569, i572, RationalInterval.add])

def n574 (b : ℝ) : ℝ := -(n573 b)
def i574 : RationalInterval := ⟨(-191161498910083336904467990019 / 125000000000000000000000000000 : ℚ), (-95580748692208179241348013947 / 62500000000000000000000000000 : ℚ)⟩
theorem b574 (b : ℝ) (hb : rootInterval.Contains b) : i574.Contains (n574 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b573 b hb))
    (by norm_num [i574, i573, RationalInterval.neg]) (by norm_num [i574, i573, RationalInterval.neg])

def n575 (b : ℝ) : ℝ := (n410 b) + (n574 b)
def i575 : RationalInterval := ⟨(37628559446931412998520387137 / 500000000000000000000000000000 : ℚ), (75257163279219266964023348519 / 1000000000000000000000000000000 : ℚ)⟩
theorem b575 (b : ℝ) (hb : rootInterval.Contains b) : i575.Contains (n575 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b410 b hb) (b574 b hb))
    (by norm_num [i575, i410, i574, RationalInterval.add]) (by norm_num [i575, i410, i574, RationalInterval.add])

def n576 (b : ℝ) : ℝ := (n184 b) * (n64 b)
def i576 : RationalInterval := ⟨(-45812428885582802222877501927 / 100000000000000000000000000000 : ℚ), (-14316384014993942109778000117 / 31250000000000000000000000000 : ℚ)⟩
theorem b576 (b : ℝ) (hb : rootInterval.Contains b) : i576.Contains (n576 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b184 b hb) (b64 b hb))
    (by norm_num [i576, i184, i64, RationalInterval.mul]) (by norm_num [i576, i184, i64, RationalInterval.mul])

def n577 (b : ℝ) : ℝ := (n182 b) + (n576 b)
def i577 : RationalInterval := ⟨(23214090558122231160382861049 / 31250000000000000000000000000 : ℚ), (46428181185424186223472203651 / 62500000000000000000000000000 : ℚ)⟩
theorem b577 (b : ℝ) (hb : rootInterval.Contains b) : i577.Contains (n577 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b182 b hb) (b576 b hb))
    (by norm_num [i577, i182, i576, RationalInterval.add]) (by norm_num [i577, i182, i576, RationalInterval.add])

def n578 (b : ℝ) : ℝ := (n182 b) * (n64 b)
def i578 : RationalInterval := ⟨(600487593357869709680513286419 / 1000000000000000000000000000000 : ℚ), (15012189843082414088605640777 / 25000000000000000000000000000 : ℚ)⟩
theorem b578 (b : ℝ) (hb : rootInterval.Contains b) : i578.Contains (n578 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b182 b hb) (b64 b hb))
    (by norm_num [i578, i182, i64, RationalInterval.mul]) (by norm_num [i578, i182, i64, RationalInterval.mul])

def n579 (b : ℝ) : ℝ := (n61 b) * (n184 b)
def i579 : RationalInterval := ⟨(-162383344351764814645306103993 / 500000000000000000000000000000 : ℚ), (-324766688434675147118269347509 / 1000000000000000000000000000000 : ℚ)⟩
theorem b579 (b : ℝ) (hb : rootInterval.Contains b) : i579.Contains (n579 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b61 b hb) (b184 b hb))
    (by norm_num [i579, i61, i184, RationalInterval.mul]) (by norm_num [i579, i61, i184, RationalInterval.mul])

def n580 (b : ℝ) : ℝ := (n578 b) + (n579 b)
def i580 : RationalInterval := ⟨(275720904654340080389901078433 / 1000000000000000000000000000000 : ℚ), (275720905288621416425956283571 / 1000000000000000000000000000000 : ℚ)⟩
theorem b580 (b : ℝ) (hb : rootInterval.Contains b) : i580.Contains (n580 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b578 b hb) (b579 b hb))
    (by norm_num [i580, i578, i579, RationalInterval.add]) (by norm_num [i580, i578, i579, RationalInterval.add])

def n581 (b : ℝ) : ℝ := -(n577 b)
def i581 : RationalInterval := ⟨(-46428181185424186223472203651 / 62500000000000000000000000000 : ℚ), (-23214090558122231160382861049 / 31250000000000000000000000000 : ℚ)⟩
theorem b581 (b : ℝ) (hb : rootInterval.Contains b) : i581.Contains (n581 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b577 b hb))
    (by norm_num [i581, i577, RationalInterval.neg]) (by norm_num [i581, i577, RationalInterval.neg])

def n582 (b : ℝ) : ℝ := -(n580 b)
def i582 : RationalInterval := ⟨(-275720905288621416425956283571 / 1000000000000000000000000000000 : ℚ), (-275720904654340080389901078433 / 1000000000000000000000000000000 : ℚ)⟩
theorem b582 (b : ℝ) (hb : rootInterval.Contains b) : i582.Contains (n582 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b580 b hb))
    (by norm_num [i582, i580, RationalInterval.neg]) (by norm_num [i582, i580, RationalInterval.neg])

def n583 (b : ℝ) : ℝ := (n581 b) + (n15 b)
def i583 : RationalInterval := ⟨(16071818814575813776527796349 / 62500000000000000000000000000 : ℚ), (8035909441877768839617138951 / 31250000000000000000000000000 : ℚ)⟩
theorem b583 (b : ℝ) (hb : rootInterval.Contains b) : i583.Contains (n583 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b581 b hb) (b15 b hb))
    (by norm_num [i583, i581, i15, RationalInterval.add]) (by norm_num [i583, i581, i15, RationalInterval.add])

def n584 (b : ℝ) : ℝ := (n196 b) * (n583 b)
def i584 : RationalInterval := ⟨(385471127791327399176175225799 / 1000000000000000000000000000000 : ℚ), (192735564876806051263881944643 / 500000000000000000000000000000 : ℚ)⟩
theorem b584 (b : ℝ) (hb : rootInterval.Contains b) : i584.Contains (n584 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b196 b hb) (b583 b hb))
    (by norm_num [i584, i196, i583, RationalInterval.mul]) (by norm_num [i584, i196, i583, RationalInterval.mul])

def n585 (b : ℝ) : ℝ := (n197 b) * (n582 b)
def i585 : RationalInterval := ⟨(21454832224592647681942607171 / 200000000000000000000000000000 : ℚ), (107274161581338569688373427159 / 1000000000000000000000000000000 : ℚ)⟩
theorem b585 (b : ℝ) (hb : rootInterval.Contains b) : i585.Contains (n585 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b197 b hb) (b582 b hb))
    (by norm_num [i585, i197, i582, RationalInterval.mul]) (by norm_num [i585, i197, i582, RationalInterval.mul])

def n586 (b : ℝ) : ℝ := (n584 b) + (n585 b)
def i586 : RationalInterval := ⟨(246372644457145318792944130827 / 500000000000000000000000000000 : ℚ), (98549058266990134443227463289 / 200000000000000000000000000000 : ℚ)⟩
theorem b586 (b : ℝ) (hb : rootInterval.Contains b) : i586.Contains (n586 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b584 b hb) (b585 b hb))
    (by norm_num [i586, i584, i585, RationalInterval.add]) (by norm_num [i586, i584, i585, RationalInterval.add])

def n587 (b : ℝ) : ℝ := (n198 b) * (n583 b)
def i587 : RationalInterval := ⟨(-50024234296989323055186082883 / 500000000000000000000000000000 : ℚ), (-100048467965984630406368118671 / 1000000000000000000000000000000 : ℚ)⟩
theorem b587 (b : ℝ) (hb : rootInterval.Contains b) : i587.Contains (n587 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b198 b hb) (b583 b hb))
    (by norm_num [i587, i198, i583, RationalInterval.mul]) (by norm_num [i587, i198, i583, RationalInterval.mul])

def n588 (b : ℝ) : ℝ := (n199 b) * (n582 b)
def i588 : RationalInterval := ⟨(-27842851921948303339919214029 / 1000000000000000000000000000000 : ℚ), (-27842851769948128716798326593 / 1000000000000000000000000000000 : ℚ)⟩
theorem b588 (b : ℝ) (hb : rootInterval.Contains b) : i588.Contains (n588 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b199 b hb) (b582 b hb))
    (by norm_num [i588, i199, i582, RationalInterval.mul]) (by norm_num [i588, i199, i582, RationalInterval.mul])

def n589 (b : ℝ) : ℝ := (n587 b) + (n588 b)
def i589 : RationalInterval := ⟨(-25578264103185389890058275959 / 200000000000000000000000000000 : ℚ), (-7993207483495797445197902829 / 62500000000000000000000000000 : ℚ)⟩
theorem b589 (b : ℝ) (hb : rootInterval.Contains b) : i589.Contains (n589 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b587 b hb) (b588 b hb))
    (by norm_num [i589, i587, i588, RationalInterval.add]) (by norm_num [i589, i587, i588, RationalInterval.add])

def n590 (b : ℝ) : ℝ := -(n182 b)
def i590 : RationalInterval := ⟨(-15012189843082414088605640777 / 12500000000000000000000000000 : ℚ), (-600487593357869709680513286419 / 500000000000000000000000000000 : ℚ)⟩
theorem b590 (b : ℝ) (hb : rootInterval.Contains b) : i590.Contains (n590 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b182 b hb))
    (by norm_num [i590, i182, RationalInterval.neg]) (by norm_num [i590, i182, RationalInterval.neg])

def n591 (b : ℝ) : ℝ := -(n184 b)
def i591 : RationalInterval := ⟨(14316384014993942109778000117 / 15625000000000000000000000000 : ℚ), (916248577711656044457550038539 / 1000000000000000000000000000000 : ℚ)⟩
theorem b591 (b : ℝ) (hb : rootInterval.Contains b) : i591.Contains (n591 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b184 b hb))
    (by norm_num [i591, i184, RationalInterval.neg]) (by norm_num [i591, i184, RationalInterval.neg])

def n592 (b : ℝ) : ℝ := (n586 b) + (n590 b)
def i592 : RationalInterval := ⟨(-354114949266151244751281500253 / 500000000000000000000000000000 : ℚ), (-708229895380788747144889256393 / 1000000000000000000000000000000 : ℚ)⟩
theorem b592 (b : ℝ) (hb : rootInterval.Contains b) : i592.Contains (n592 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b586 b hb) (b590 b hb))
    (by norm_num [i592, i586, i590, RationalInterval.add]) (by norm_num [i592, i586, i590, RationalInterval.add])

def n593 (b : ℝ) : ℝ := (n589 b) + (n591 b)
def i593 : RationalInterval := ⟨(788357256443685345575500627693 / 1000000000000000000000000000000 : ℚ), (31534290319028931413375343731 / 40000000000000000000000000000 : ℚ)⟩
theorem b593 (b : ℝ) (hb : rootInterval.Contains b) : i593.Contains (n593 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b589 b hb) (b591 b hb))
    (by norm_num [i593, i589, i591, RationalInterval.add]) (by norm_num [i593, i589, i591, RationalInterval.add])

def n594 (b : ℝ) : ℝ := (n581 b) * (n16 b)
def i594 : RationalInterval := ⟨(23214090558122231160382861049 / 31250000000000000000000000000 : ℚ), (46428181185424186223472203651 / 62500000000000000000000000000 : ℚ)⟩
theorem b594 (b : ℝ) (hb : rootInterval.Contains b) : i594.Contains (n594 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b581 b hb) (b16 b hb))
    (by norm_num [i594, i581, i16, RationalInterval.mul]) (by norm_num [i594, i581, i16, RationalInterval.mul])

def n595 (b : ℝ) : ℝ := (n594 b) + (n582 b)
def i595 : RationalInterval := ⟨(467129992571289980706295269997 / 1000000000000000000000000000000 : ℚ), (467129994312446899185654179983 / 1000000000000000000000000000000 : ℚ)⟩
theorem b595 (b : ℝ) (hb : rootInterval.Contains b) : i595.Contains (n595 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b594 b hb) (b582 b hb))
    (by norm_num [i595, i594, i582, RationalInterval.add]) (by norm_num [i595, i594, i582, RationalInterval.add])

def n596 (b : ℝ) : ℝ := (n592 b) * (n16 b)
def i596 : RationalInterval := ⟨(708229895380788747144889256393 / 1000000000000000000000000000000 : ℚ), (354114949266151244751281500253 / 500000000000000000000000000000 : ℚ)⟩
theorem b596 (b : ℝ) (hb : rootInterval.Contains b) : i596.Contains (n596 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b592 b hb) (b16 b hb))
    (by norm_num [i596, i592, i16, RationalInterval.mul]) (by norm_num [i596, i592, i16, RationalInterval.mul])

def n597 (b : ℝ) : ℝ := (n152 b) * (n593 b)
def i597 : RationalInterval := ⟨(-197089314493930821333595898319 / 500000000000000000000000000000 : ℚ), (-197089314110921336393875156923 / 500000000000000000000000000000 : ℚ)⟩
theorem b597 (b : ℝ) (hb : rootInterval.Contains b) : i597.Contains (n597 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b152 b hb) (b593 b hb))
    (by norm_num [i597, i152, i593, RationalInterval.mul]) (by norm_num [i597, i152, i593, RationalInterval.mul])

def n598 (b : ℝ) : ℝ := (n596 b) + (n597 b)
def i598 : RationalInterval := ⟨(62810253278585420895539491951 / 200000000000000000000000000000 : ℚ), (15702563515522990835740634333 / 50000000000000000000000000000 : ℚ)⟩
theorem b598 (b : ℝ) (hb : rootInterval.Contains b) : i598.Contains (n598 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b596 b hb) (b597 b hb))
    (by norm_num [i598, i596, i597, RationalInterval.add]) (by norm_num [i598, i596, i597, RationalInterval.add])

def n599 (b : ℝ) : ℝ := (n595 b) + (n598 b)
def i599 : RationalInterval := ⟨(97647657370527135647999091219 / 125000000000000000000000000000 : ℚ), (781181264622906715900466866643 / 1000000000000000000000000000000 : ℚ)⟩
theorem b599 (b : ℝ) (hb : rootInterval.Contains b) : i599.Contains (n599 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b595 b hb) (b598 b hb))
    (by norm_num [i599, i595, i598, RationalInterval.add]) (by norm_num [i599, i595, i598, RationalInterval.add])

def n600 (b : ℝ) : ℝ := (n61 b) + (n152 b)
def i600 : RationalInterval := ⟨(-14554740209 / 100000000000 : ℚ), (-11643792167 / 80000000000 : ℚ)⟩
theorem b600 (b : ℝ) (hb : rootInterval.Contains b) : i600.Contains (n600 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b61 b hb) (b152 b hb))
    (by norm_num [i600, i61, i152, RationalInterval.add]) (by norm_num [i600, i61, i152, RationalInterval.add])

def n601 (b : ℝ) : ℝ := (n600 b) + (n64 b)
def i601 : RationalInterval := ⟨(35445259791 / 100000000000 : ℚ), (28356207833 / 80000000000 : ℚ)⟩
theorem b601 (b : ℝ) (hb : rootInterval.Contains b) : i601.Contains (n601 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b600 b hb) (b64 b hb))
    (by norm_num [i601, i600, i64, RationalInterval.add]) (by norm_num [i601, i600, i64, RationalInterval.add])

def n602 (b : ℝ) : ℝ := (n600 b) * (n16 b)
def i602 : RationalInterval := ⟨(11643792167 / 80000000000 : ℚ), (14554740209 / 100000000000 : ℚ)⟩
theorem b602 (b : ℝ) (hb : rootInterval.Contains b) : i602.Contains (n602 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b600 b hb) (b16 b hb))
    (by norm_num [i602, i600, i16, RationalInterval.mul]) (by norm_num [i602, i600, i16, RationalInterval.mul])

def n603 (b : ℝ) : ℝ := (n600 b) * (n152 b)
def i603 : RationalInterval := ⟨(11643792167 / 160000000000 : ℚ), (14554740209 / 200000000000 : ℚ)⟩
theorem b603 (b : ℝ) (hb : rootInterval.Contains b) : i603.Contains (n603 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b600 b hb) (b152 b hb))
    (by norm_num [i603, i600, i152, RationalInterval.mul]) (by norm_num [i603, i600, i152, RationalInterval.mul])

def n604 (b : ℝ) : ℝ := (n152 b) * (n600 b)
def i604 : RationalInterval := ⟨(11643792167 / 160000000000 : ℚ), (14554740209 / 200000000000 : ℚ)⟩
theorem b604 (b : ℝ) (hb : rootInterval.Contains b) : i604.Contains (n604 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b152 b hb) (b600 b hb))
    (by norm_num [i604, i152, i600, RationalInterval.mul]) (by norm_num [i604, i152, i600, RationalInterval.mul])

def n605 (b : ℝ) : ℝ := (n58 b) + (n602 b)
def i605 : RationalInterval := ⟨(31643792167 / 80000000000 : ℚ), (39554740209 / 100000000000 : ℚ)⟩
theorem b605 (b : ℝ) (hb : rootInterval.Contains b) : i605.Contains (n605 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b58 b hb) (b602 b hb))
    (by norm_num [i605, i58, i602, RationalInterval.add]) (by norm_num [i605, i58, i602, RationalInterval.add])

def n606 (b : ℝ) : ℝ := (n602 b) + (n58 b)
def i606 : RationalInterval := ⟨(31643792167 / 80000000000 : ℚ), (39554740209 / 100000000000 : ℚ)⟩
theorem b606 (b : ℝ) (hb : rootInterval.Contains b) : i606.Contains (n606 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b602 b hb) (b58 b hb))
    (by norm_num [i606, i602, i58, RationalInterval.add]) (by norm_num [i606, i602, i58, RationalInterval.add])

def n607 (b : ℝ) : ℝ := (n603 b) + (n604 b)
def i607 : RationalInterval := ⟨(11643792167 / 80000000000 : ℚ), (14554740209 / 100000000000 : ℚ)⟩
theorem b607 (b : ℝ) (hb : rootInterval.Contains b) : i607.Contains (n607 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b603 b hb) (b604 b hb))
    (by norm_num [i607, i603, i604, RationalInterval.add]) (by norm_num [i607, i603, i604, RationalInterval.add])

def n608 (b : ℝ) : ℝ := (n593 b) * (n64 b)
def i608 : RationalInterval := ⟨(197089314110921336393875156923 / 500000000000000000000000000000 : ℚ), (197089314493930821333595898319 / 500000000000000000000000000000 : ℚ)⟩
theorem b608 (b : ℝ) (hb : rootInterval.Contains b) : i608.Contains (n608 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b593 b hb) (b64 b hb))
    (by norm_num [i608, i593, i64, RationalInterval.mul]) (by norm_num [i608, i593, i64, RationalInterval.mul])

def n609 (b : ℝ) : ℝ := (n592 b) + (n608 b)
def i609 : RationalInterval := ⟨(-15702563515522990835740634333 / 50000000000000000000000000000 : ℚ), (-62810253278585420895539491951 / 200000000000000000000000000000 : ℚ)⟩
theorem b609 (b : ℝ) (hb : rootInterval.Contains b) : i609.Contains (n609 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b592 b hb) (b608 b hb))
    (by norm_num [i609, i592, i608, RationalInterval.add]) (by norm_num [i609, i592, i608, RationalInterval.add])

def n610 (b : ℝ) : ℝ := (n592 b) * (n64 b)
def i610 : RationalInterval := ⟨(-354114949266151244751281500253 / 1000000000000000000000000000000 : ℚ), (-88528736922598593393111157049 / 250000000000000000000000000000 : ℚ)⟩
theorem b610 (b : ℝ) (hb : rootInterval.Contains b) : i610.Contains (n610 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b592 b hb) (b64 b hb))
    (by norm_num [i610, i592, i64, RationalInterval.mul]) (by norm_num [i610, i592, i64, RationalInterval.mul])

def n611 (b : ℝ) : ℝ := (n61 b) * (n593 b)
def i611 : RationalInterval := ⟨(139717638813832179176916160767 / 500000000000000000000000000000 : ℚ), (279435278172670079342991775899 / 1000000000000000000000000000000 : ℚ)⟩
theorem b611 (b : ℝ) (hb : rootInterval.Contains b) : i611.Contains (n611 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b61 b hb) (b593 b hb))
    (by norm_num [i611, i61, i593, RationalInterval.mul]) (by norm_num [i611, i61, i593, RationalInterval.mul])

def n612 (b : ℝ) : ℝ := (n610 b) + (n611 b)
def i612 : RationalInterval := ⟨(-74679671638486886397449178719 / 1000000000000000000000000000000 : ℚ), (-74679669517724294229452852297 / 1000000000000000000000000000000 : ℚ)⟩
theorem b612 (b : ℝ) (hb : rootInterval.Contains b) : i612.Contains (n612 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b610 b hb) (b611 b hb))
    (by norm_num [i612, i610, i611, RationalInterval.add]) (by norm_num [i612, i610, i611, RationalInterval.add])

def n613 (b : ℝ) : ℝ := (n592 b) * (n152 b)
def i613 : RationalInterval := ⟨(88528736922598593393111157049 / 250000000000000000000000000000 : ℚ), (354114949266151244751281500253 / 1000000000000000000000000000000 : ℚ)⟩
theorem b613 (b : ℝ) (hb : rootInterval.Contains b) : i613.Contains (n613 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b592 b hb) (b152 b hb))
    (by norm_num [i613, i592, i152, RationalInterval.mul]) (by norm_num [i613, i592, i152, RationalInterval.mul])

def n614 (b : ℝ) : ℝ := (n593 b) * (n600 b)
def i614 : RationalInterval := ⟨(-114743350817162456469139328953 / 1000000000000000000000000000000 : ℚ), (-114743350592207421292808778947 / 1000000000000000000000000000000 : ℚ)⟩
theorem b614 (b : ℝ) (hb : rootInterval.Contains b) : i614.Contains (n614 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b593 b hb) (b600 b hb))
    (by norm_num [i614, i593, i600, RationalInterval.mul]) (by norm_num [i614, i593, i600, RationalInterval.mul])

def n615 (b : ℝ) : ℝ := (n613 b) + (n614 b)
def i615 : RationalInterval := ⟨(239371596873231917103305299243 / 1000000000000000000000000000000 : ℚ), (119685799336971911729236360653 / 500000000000000000000000000000 : ℚ)⟩
theorem b615 (b : ℝ) (hb : rootInterval.Contains b) : i615.Contains (n615 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b613 b hb) (b614 b hb))
    (by norm_num [i615, i613, i614, RationalInterval.add]) (by norm_num [i615, i613, i614, RationalInterval.add])

def n616 (b : ℝ) : ℝ := (n615 b) * (n13 b)
def i616 : RationalInterval := ⟨(239371596873231917103305299243 / 500000000000000000000000000000 : ℚ), (119685799336971911729236360653 / 250000000000000000000000000000 : ℚ)⟩
theorem b616 (b : ℝ) (hb : rootInterval.Contains b) : i616.Contains (n616 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b615 b hb) (b13 b hb))
    (by norm_num [i616, i615, i13, RationalInterval.mul]) (by norm_num [i616, i615, i13, RationalInterval.mul])

def n617 (b : ℝ) : ℝ := (n581 b) * (n152 b)
def i617 : RationalInterval := ⟨(23214090558122231160382861049 / 62500000000000000000000000000 : ℚ), (46428181185424186223472203651 / 125000000000000000000000000000 : ℚ)⟩
theorem b617 (b : ℝ) (hb : rootInterval.Contains b) : i617.Contains (n617 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b581 b hb) (b152 b hb))
    (by norm_num [i617, i581, i152, RationalInterval.mul]) (by norm_num [i617, i581, i152, RationalInterval.mul])

def n618 (b : ℝ) : ℝ := (n582 b) * (n16 b)
def i618 : RationalInterval := ⟨(275720904654340080389901078433 / 1000000000000000000000000000000 : ℚ), (275720905288621416425956283571 / 1000000000000000000000000000000 : ℚ)⟩
theorem b618 (b : ℝ) (hb : rootInterval.Contains b) : i618.Contains (n618 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b582 b hb) (b16 b hb))
    (by norm_num [i618, i582, i16, RationalInterval.mul]) (by norm_num [i618, i582, i16, RationalInterval.mul])

def n619 (b : ℝ) : ℝ := (n582 b) * (n152 b)
def i619 : RationalInterval := ⟨(8616278270448127512184408701 / 62500000000000000000000000000 : ℚ), (68930226322155354106489070893 / 500000000000000000000000000000 : ℚ)⟩
theorem b619 (b : ℝ) (hb : rootInterval.Contains b) : i619.Contains (n619 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b582 b hb) (b152 b hb))
    (by norm_num [i619, i582, i152, RationalInterval.mul]) (by norm_num [i619, i582, i152, RationalInterval.mul])

def n620 (b : ℝ) : ℝ := (n152 b) * (n581 b)
def i620 : RationalInterval := ⟨(23214090558122231160382861049 / 62500000000000000000000000000 : ℚ), (46428181185424186223472203651 / 125000000000000000000000000000 : ℚ)⟩
theorem b620 (b : ℝ) (hb : rootInterval.Contains b) : i620.Contains (n620 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b152 b hb) (b581 b hb))
    (by norm_num [i620, i152, i581, RationalInterval.mul]) (by norm_num [i620, i152, i581, RationalInterval.mul])

def n621 (b : ℝ) : ℝ := (n152 b) * (n582 b)
def i621 : RationalInterval := ⟨(8616278270448127512184408701 / 62500000000000000000000000000 : ℚ), (68930226322155354106489070893 / 500000000000000000000000000000 : ℚ)⟩
theorem b621 (b : ℝ) (hb : rootInterval.Contains b) : i621.Contains (n621 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b152 b hb) (b582 b hb))
    (by norm_num [i621, i152, i582, RationalInterval.mul]) (by norm_num [i621, i152, i582, RationalInterval.mul])

def n622 (b : ℝ) : ℝ := (n594 b) + (n594 b)
def i622 : RationalInterval := ⟨(23214090558122231160382861049 / 15625000000000000000000000000 : ℚ), (46428181185424186223472203651 / 31250000000000000000000000000 : ℚ)⟩
theorem b622 (b : ℝ) (hb : rootInterval.Contains b) : i622.Contains (n622 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b594 b hb) (b594 b hb))
    (by norm_num [i622, i594, i594, RationalInterval.add]) (by norm_num [i622, i594, i594, RationalInterval.add])

def n623 (b : ℝ) : ℝ := (n617 b) + (n618 b)
def i623 : RationalInterval := ⟨(647146353584295778956026855217 / 1000000000000000000000000000000 : ℚ), (647146354772014906213733912779 / 1000000000000000000000000000000 : ℚ)⟩
theorem b623 (b : ℝ) (hb : rootInterval.Contains b) : i623.Contains (n623 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b617 b hb) (b618 b hb))
    (by norm_num [i623, i617, i618, RationalInterval.add]) (by norm_num [i623, i617, i618, RationalInterval.add])

def n624 (b : ℝ) : ℝ := (n618 b) + (n620 b)
def i624 : RationalInterval := ⟨(647146353584295778956026855217 / 1000000000000000000000000000000 : ℚ), (647146354772014906213733912779 / 1000000000000000000000000000000 : ℚ)⟩
theorem b624 (b : ℝ) (hb : rootInterval.Contains b) : i624.Contains (n624 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b618 b hb) (b620 b hb))
    (by norm_num [i624, i618, i620, RationalInterval.add]) (by norm_num [i624, i618, i620, RationalInterval.add])

def n625 (b : ℝ) : ℝ := (n619 b) + (n621 b)
def i625 : RationalInterval := ⟨(8616278270448127512184408701 / 31250000000000000000000000000 : ℚ), (68930226322155354106489070893 / 250000000000000000000000000000 : ℚ)⟩
theorem b625 (b : ℝ) (hb : rootInterval.Contains b) : i625.Contains (n625 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b619 b hb) (b621 b hb))
    (by norm_num [i625, i619, i621, RationalInterval.add]) (by norm_num [i625, i619, i621, RationalInterval.add])

def n626 (b : ℝ) : ℝ := (n609 b) * (n16 b)
def i626 : RationalInterval := ⟨(62810253278585420895539491951 / 200000000000000000000000000000 : ℚ), (15702563515522990835740634333 / 50000000000000000000000000000 : ℚ)⟩
theorem b626 (b : ℝ) (hb : rootInterval.Contains b) : i626.Contains (n626 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b609 b hb) (b16 b hb))
    (by norm_num [i626, i609, i16, RationalInterval.mul]) (by norm_num [i626, i609, i16, RationalInterval.mul])

def n627 (b : ℝ) : ℝ := (n609 b) * (n152 b)
def i627 : RationalInterval := ⟨(157025633196463552238848729877 / 1000000000000000000000000000000 : ℚ), (15702563515522990835740634333 / 100000000000000000000000000000 : ℚ)⟩
theorem b627 (b : ℝ) (hb : rootInterval.Contains b) : i627.Contains (n627 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b609 b hb) (b152 b hb))
    (by norm_num [i627, i609, i152, RationalInterval.mul]) (by norm_num [i627, i609, i152, RationalInterval.mul])

def n628 (b : ℝ) : ℝ := (n612 b) * (n16 b)
def i628 : RationalInterval := ⟨(74679669517724294229452852297 / 1000000000000000000000000000000 : ℚ), (74679671638486886397449178719 / 1000000000000000000000000000000 : ℚ)⟩
theorem b628 (b : ℝ) (hb : rootInterval.Contains b) : i628.Contains (n628 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b612 b hb) (b16 b hb))
    (by norm_num [i628, i612, i16, RationalInterval.mul]) (by norm_num [i628, i612, i16, RationalInterval.mul])

def n629 (b : ℝ) : ℝ := (n612 b) * (n152 b)
def i629 : RationalInterval := ⟨(9334958689715536778681606537 / 250000000000000000000000000000 : ℚ), (466747947740543039984057367 / 12500000000000000000000000000 : ℚ)⟩
theorem b629 (b : ℝ) (hb : rootInterval.Contains b) : i629.Contains (n629 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b612 b hb) (b152 b hb))
    (by norm_num [i629, i612, i152, RationalInterval.mul]) (by norm_num [i629, i612, i152, RationalInterval.mul])

