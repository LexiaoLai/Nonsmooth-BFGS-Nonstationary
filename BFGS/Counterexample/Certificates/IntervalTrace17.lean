import BFGS.Counterexample.Certificates.IntervalTrace16

/-! Generated arithmetic proofs. Each bound is checked by the Lean kernel. -/
namespace BFGS.Counterexample.Trace
noncomputable section
open BFGS RationalInterval
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false

def n1530 (b : ℝ) : ℝ := (n1490 b) * (n1501 b)
def i1530 : RationalInterval := ⟨(307265794957328964442650977791 / 1000000000000000000000000000000 : ℚ), (76816450193092446764454404021 / 250000000000000000000000000000 : ℚ)⟩
theorem b1530 (b : ℝ) (hb : rootInterval.Contains b) : i1530.Contains (n1530 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1490 b hb) (b1501 b hb))
    (by norm_num [i1530, i1490, i1501, RationalInterval.mul]) (by norm_num [i1530, i1490, i1501, RationalInterval.mul])

def n1531 (b : ℝ) : ℝ := (n1491 b) * (n1504 b)
def i1531 : RationalInterval := ⟨(414767706447180618664416743199 / 1000000000000000000000000000000 : ℚ), (41476771295003728202648270697 / 100000000000000000000000000000 : ℚ)⟩
theorem b1531 (b : ℝ) (hb : rootInterval.Contains b) : i1531.Contains (n1531 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1491 b hb) (b1504 b hb))
    (by norm_num [i1531, i1491, i1504, RationalInterval.mul]) (by norm_num [i1531, i1491, i1504, RationalInterval.mul])

def n1532 (b : ℝ) : ℝ := (n1530 b) + (n1531 b)
def i1532 : RationalInterval := ⟨(72203350140450958310706772099 / 100000000000000000000000000000 : ℚ), (361016756861203534542150161527 / 500000000000000000000000000000 : ℚ)⟩
theorem b1532 (b : ℝ) (hb : rootInterval.Contains b) : i1532.Contains (n1532 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1530 b hb) (b1531 b hb))
    (by norm_num [i1532, i1530, i1531, RationalInterval.add]) (by norm_num [i1532, i1530, i1531, RationalInterval.add])

def n1533 (b : ℝ) : ℝ := (n1532 b) * (n13 b)
def i1533 : RationalInterval := ⟨(72203350140450958310706772099 / 50000000000000000000000000000 : ℚ), (361016756861203534542150161527 / 250000000000000000000000000000 : ℚ)⟩
theorem b1533 (b : ℝ) (hb : rootInterval.Contains b) : i1533.Contains (n1533 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1532 b hb) (b13 b hb))
    (by norm_num [i1533, i1532, i13, RationalInterval.mul]) (by norm_num [i1533, i1532, i13, RationalInterval.mul])

def n1534 (b : ℝ) : ℝ := (n1479 b) * (n310 b)
def i1534 : RationalInterval := ⟨(373328664417553724711479696969 / 500000000000000000000000000000 : ℚ), (18666433517510361096763572673 / 25000000000000000000000000000 : ℚ)⟩
theorem b1534 (b : ℝ) (hb : rootInterval.Contains b) : i1534.Contains (n1534 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1479 b hb) (b310 b hb))
    (by norm_num [i1534, i1479, i310, RationalInterval.mul]) (by norm_num [i1534, i1479, i310, RationalInterval.mul])

def n1535 (b : ℝ) : ℝ := (n1479 b) * (n311 b)
def i1535 : RationalInterval := ⟨(43246673849815891422475055829 / 100000000000000000000000000000 : ℚ), (108116686373338989624724778249 / 250000000000000000000000000000 : ℚ)⟩
theorem b1535 (b : ℝ) (hb : rootInterval.Contains b) : i1535.Contains (n1535 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1479 b hb) (b311 b hb))
    (by norm_num [i1535, i1479, i311, RationalInterval.mul]) (by norm_num [i1535, i1479, i311, RationalInterval.mul])

def n1536 (b : ℝ) : ℝ := (n1480 b) * (n310 b)
def i1536 : RationalInterval := ⟨(263528248051911947175693569621 / 500000000000000000000000000000 : ℚ), (527056504334857172373035235951 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1536 (b : ℝ) (hb : rootInterval.Contains b) : i1536.Contains (n1536 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1480 b hb) (b310 b hb))
    (by norm_num [i1536, i1480, i310, RationalInterval.mul]) (by norm_num [i1536, i1480, i310, RationalInterval.mul])

def n1537 (b : ℝ) : ℝ := (n1480 b) * (n311 b)
def i1537 : RationalInterval := ⟨(61054621731202636399663726367 / 200000000000000000000000000000 : ℚ), (152636556755059047720239799371 / 500000000000000000000000000000 : ℚ)⟩
theorem b1537 (b : ℝ) (hb : rootInterval.Contains b) : i1537.Contains (n1537 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1480 b hb) (b311 b hb))
    (by norm_num [i1537, i1480, i311, RationalInterval.mul]) (by norm_num [i1537, i1480, i311, RationalInterval.mul])

def n1538 (b : ℝ) : ℝ := (n310 b) * (n1479 b)
def i1538 : RationalInterval := ⟨(373328664417553724711479696969 / 500000000000000000000000000000 : ℚ), (18666433517510361096763572673 / 25000000000000000000000000000 : ℚ)⟩
theorem b1538 (b : ℝ) (hb : rootInterval.Contains b) : i1538.Contains (n1538 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b310 b hb) (b1479 b hb))
    (by norm_num [i1538, i310, i1479, RationalInterval.mul]) (by norm_num [i1538, i310, i1479, RationalInterval.mul])

def n1539 (b : ℝ) : ℝ := (n310 b) * (n1480 b)
def i1539 : RationalInterval := ⟨(263528248051911947175693569621 / 500000000000000000000000000000 : ℚ), (527056504334857172373035235951 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1539 (b : ℝ) (hb : rootInterval.Contains b) : i1539.Contains (n1539 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b310 b hb) (b1480 b hb))
    (by norm_num [i1539, i310, i1480, RationalInterval.mul]) (by norm_num [i1539, i310, i1480, RationalInterval.mul])

def n1540 (b : ℝ) : ℝ := (n311 b) * (n1479 b)
def i1540 : RationalInterval := ⟨(43246673849815891422475055829 / 100000000000000000000000000000 : ℚ), (108116686373338989624724778249 / 250000000000000000000000000000 : ℚ)⟩
theorem b1540 (b : ℝ) (hb : rootInterval.Contains b) : i1540.Contains (n1540 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b311 b hb) (b1479 b hb))
    (by norm_num [i1540, i311, i1479, RationalInterval.mul]) (by norm_num [i1540, i311, i1479, RationalInterval.mul])

def n1541 (b : ℝ) : ℝ := (n311 b) * (n1480 b)
def i1541 : RationalInterval := ⟨(61054621731202636399663726367 / 200000000000000000000000000000 : ℚ), (152636556755059047720239799371 / 500000000000000000000000000000 : ℚ)⟩
theorem b1541 (b : ℝ) (hb : rootInterval.Contains b) : i1541.Contains (n1541 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b311 b hb) (b1480 b hb))
    (by norm_num [i1541, i311, i1480, RationalInterval.mul]) (by norm_num [i1541, i311, i1480, RationalInterval.mul])

def n1542 (b : ℝ) : ℝ := (n1534 b) + (n1538 b)
def i1542 : RationalInterval := ⟨(373328664417553724711479696969 / 250000000000000000000000000000 : ℚ), (18666433517510361096763572673 / 12500000000000000000000000000 : ℚ)⟩
theorem b1542 (b : ℝ) (hb : rootInterval.Contains b) : i1542.Contains (n1542 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1534 b hb) (b1538 b hb))
    (by norm_num [i1542, i1534, i1538, RationalInterval.add]) (by norm_num [i1542, i1534, i1538, RationalInterval.add])

def n1543 (b : ℝ) : ℝ := (n1535 b) + (n1539 b)
def i1543 : RationalInterval := ⟨(239880808650495702144034424383 / 250000000000000000000000000000 : ℚ), (959523249828213130871934348947 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1543 (b : ℝ) (hb : rootInterval.Contains b) : i1543.Contains (n1543 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1535 b hb) (b1539 b hb))
    (by norm_num [i1543, i1535, i1539, RationalInterval.add]) (by norm_num [i1543, i1535, i1539, RationalInterval.add])

def n1544 (b : ℝ) : ℝ := (n1536 b) + (n1540 b)
def i1544 : RationalInterval := ⟨(239880808650495702144034424383 / 250000000000000000000000000000 : ℚ), (959523249828213130871934348947 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1544 (b : ℝ) (hb : rootInterval.Contains b) : i1544.Contains (n1544 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1536 b hb) (b1540 b hb))
    (by norm_num [i1544, i1536, i1540, RationalInterval.add]) (by norm_num [i1544, i1536, i1540, RationalInterval.add])

def n1545 (b : ℝ) : ℝ := (n1537 b) + (n1541 b)
def i1545 : RationalInterval := ⟨(61054621731202636399663726367 / 100000000000000000000000000000 : ℚ), (152636556755059047720239799371 / 250000000000000000000000000000 : ℚ)⟩
theorem b1545 (b : ℝ) (hb : rootInterval.Contains b) : i1545.Contains (n1545 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1537 b hb) (b1541 b hb))
    (by norm_num [i1545, i1537, i1541, RationalInterval.add]) (by norm_num [i1545, i1537, i1541, RationalInterval.add])

def n1546 (b : ℝ) : ℝ := (n1526 b) * (n310 b)
def i1546 : RationalInterval := ⟨(1088818766953942276793319503043 / 1000000000000000000000000000000 : ℚ), (108881878470664983538782569717 / 100000000000000000000000000000 : ℚ)⟩
theorem b1546 (b : ℝ) (hb : rootInterval.Contains b) : i1546.Contains (n1546 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1526 b hb) (b310 b hb))
    (by norm_num [i1546, i1526, i310, RationalInterval.mul]) (by norm_num [i1546, i1526, i310, RationalInterval.mul])

def n1547 (b : ℝ) : ℝ := (n1526 b) * (n311 b)
def i1547 : RationalInterval := ⟨(630647932827225397232291755343 / 1000000000000000000000000000000 : ℚ), (630647943288685732130977239477 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1547 (b : ℝ) (hb : rootInterval.Contains b) : i1547.Contains (n1547 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1526 b hb) (b311 b hb))
    (by norm_num [i1547, i1526, i311, RationalInterval.mul]) (by norm_num [i1547, i1526, i311, RationalInterval.mul])

def n1548 (b : ℝ) : ℝ := (n1529 b) * (n310 b)
def i1548 : RationalInterval := ⟨(367901046577602714329867328647 / 500000000000000000000000000000 : ℚ), (735802105027183593143569796873 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1548 (b : ℝ) (hb : rootInterval.Contains b) : i1548.Contains (n1548 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1529 b hb) (b310 b hb))
    (by norm_num [i1548, i1529, i310, RationalInterval.mul]) (by norm_num [i1548, i1529, i310, RationalInterval.mul])

def n1549 (b : ℝ) : ℝ := (n1529 b) * (n311 b)
def i1549 : RationalInterval := ⟨(21308967254322899070975426989 / 50000000000000000000000000000 : ℚ), (213089676041867079185587850099 / 500000000000000000000000000000 : ℚ)⟩
theorem b1549 (b : ℝ) (hb : rootInterval.Contains b) : i1549.Contains (n1549 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1529 b hb) (b311 b hb))
    (by norm_num [i1549, i1529, i311, RationalInterval.mul]) (by norm_num [i1549, i1529, i311, RationalInterval.mul])

def n1550 (b : ℝ) : ℝ := (n1501 b) * (n1479 b)
def i1550 : RationalInterval := ⟨(75929922398784868918454054027 / 200000000000000000000000000000 : ℚ), (75929923866812984332602227687 / 200000000000000000000000000000 : ℚ)⟩
theorem b1550 (b : ℝ) (hb : rootInterval.Contains b) : i1550.Contains (n1550 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1501 b hb) (b1479 b hb))
    (by norm_num [i1550, i1501, i1479, RationalInterval.mul]) (by norm_num [i1550, i1501, i1479, RationalInterval.mul])

def n1551 (b : ℝ) : ℝ := (n1501 b) * (n1480 b)
def i1551 : RationalInterval := ⟨(267990129497387703989705968219 / 1000000000000000000000000000000 : ℚ), (133995067302604500379749368717 / 500000000000000000000000000000 : ℚ)⟩
theorem b1551 (b : ℝ) (hb : rootInterval.Contains b) : i1551.Contains (n1551 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1501 b hb) (b1480 b hb))
    (by norm_num [i1551, i1501, i1480, RationalInterval.mul]) (by norm_num [i1551, i1501, i1480, RationalInterval.mul])

def n1552 (b : ℝ) : ℝ := (n1504 b) * (n1479 b)
def i1552 : RationalInterval := ⟨(59476828148832633430733781181 / 200000000000000000000000000000 : ℚ), (297384146263673467765448927971 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1552 (b : ℝ) (hb : rootInterval.Contains b) : i1552.Contains (n1552 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1504 b hb) (b1479 b hb))
    (by norm_num [i1552, i1504, i1479, RationalInterval.mul]) (by norm_num [i1552, i1504, i1479, RationalInterval.mul])

def n1553 (b : ℝ) : ℝ := (n1504 b) * (n1480 b)
def i1553 : RationalInterval := ⟨(262399894108719183936485423 / 1250000000000000000000000000 : ℚ), (2099199191255612260274006321 / 10000000000000000000000000000 : ℚ)⟩
theorem b1553 (b : ℝ) (hb : rootInterval.Contains b) : i1553.Contains (n1553 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1504 b hb) (b1480 b hb))
    (by norm_num [i1553, i1504, i1480, RationalInterval.mul]) (by norm_num [i1553, i1504, i1480, RationalInterval.mul])

def n1554 (b : ℝ) : ℝ := (n1546 b) + (n1550 b)
def i1554 : RationalInterval := ⟨(734234189473933310692794886589 / 500000000000000000000000000000 : ℚ), (293693680808142951410167367121 / 200000000000000000000000000000 : ℚ)⟩
theorem b1554 (b : ℝ) (hb : rootInterval.Contains b) : i1554.Contains (n1554 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1546 b hb) (b1550 b hb))
    (by norm_num [i1554, i1546, i1550, RationalInterval.add]) (by norm_num [i1554, i1546, i1550, RationalInterval.add])

def n1555 (b : ℝ) : ℝ := (n1547 b) + (n1551 b)
def i1555 : RationalInterval := ⟨(449319031162306550610998861781 / 500000000000000000000000000000 : ℚ), (898638077893894732890475976911 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1555 (b : ℝ) (hb : rootInterval.Contains b) : i1555.Contains (n1555 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1547 b hb) (b1551 b hb))
    (by norm_num [i1555, i1547, i1551, RationalInterval.add]) (by norm_num [i1555, i1547, i1551, RationalInterval.add])

def n1556 (b : ℝ) : ℝ := (n1548 b) + (n1552 b)
def i1556 : RationalInterval := ⟨(1033186233899368595813403563199 / 1000000000000000000000000000000 : ℚ), (258296562822714265227254681211 / 250000000000000000000000000000 : ℚ)⟩
theorem b1556 (b : ℝ) (hb : rootInterval.Contains b) : i1556.Contains (n1556 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1548 b hb) (b1552 b hb))
    (by norm_num [i1556, i1548, i1552, RationalInterval.add]) (by norm_num [i1556, i1548, i1552, RationalInterval.add])

def n1557 (b : ℝ) : ℝ := (n1549 b) + (n1553 b)
def i1557 : RationalInterval := ⟨(31804963018671666428434843909 / 50000000000000000000000000000 : ℚ), (318049635604647692199288166149 / 500000000000000000000000000000 : ℚ)⟩
theorem b1557 (b : ℝ) (hb : rootInterval.Contains b) : i1557.Contains (n1557 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1549 b hb) (b1553 b hb))
    (by norm_num [i1557, i1549, i1553, RationalInterval.add]) (by norm_num [i1557, i1549, i1553, RationalInterval.add])

def n1558 (b : ℝ) : ℝ := (n1479 b) * (n1501 b)
def i1558 : RationalInterval := ⟨(75929922398784868918454054027 / 200000000000000000000000000000 : ℚ), (75929923866812984332602227687 / 200000000000000000000000000000 : ℚ)⟩
theorem b1558 (b : ℝ) (hb : rootInterval.Contains b) : i1558.Contains (n1558 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1479 b hb) (b1501 b hb))
    (by norm_num [i1558, i1479, i1501, RationalInterval.mul]) (by norm_num [i1558, i1479, i1501, RationalInterval.mul])

def n1559 (b : ℝ) : ℝ := (n1479 b) * (n1504 b)
def i1559 : RationalInterval := ⟨(59476828148832633430733781181 / 200000000000000000000000000000 : ℚ), (297384146263673467765448927971 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1559 (b : ℝ) (hb : rootInterval.Contains b) : i1559.Contains (n1559 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1479 b hb) (b1504 b hb))
    (by norm_num [i1559, i1479, i1504, RationalInterval.mul]) (by norm_num [i1559, i1479, i1504, RationalInterval.mul])

def n1560 (b : ℝ) : ℝ := (n1480 b) * (n1501 b)
def i1560 : RationalInterval := ⟨(267990129497387703989705968219 / 1000000000000000000000000000000 : ℚ), (133995067302604500379749368717 / 500000000000000000000000000000 : ℚ)⟩
theorem b1560 (b : ℝ) (hb : rootInterval.Contains b) : i1560.Contains (n1560 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1480 b hb) (b1501 b hb))
    (by norm_num [i1560, i1480, i1501, RationalInterval.mul]) (by norm_num [i1560, i1480, i1501, RationalInterval.mul])

def n1561 (b : ℝ) : ℝ := (n1480 b) * (n1504 b)
def i1561 : RationalInterval := ⟨(262399894108719183936485423 / 1250000000000000000000000000 : ℚ), (2099199191255612260274006321 / 10000000000000000000000000000 : ℚ)⟩
theorem b1561 (b : ℝ) (hb : rootInterval.Contains b) : i1561.Contains (n1561 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1480 b hb) (b1504 b hb))
    (by norm_num [i1561, i1480, i1504, RationalInterval.mul]) (by norm_num [i1561, i1480, i1504, RationalInterval.mul])

def n1562 (b : ℝ) : ℝ := (n310 b) * (n1526 b)
def i1562 : RationalInterval := ⟨(1088818766953942276793319503043 / 1000000000000000000000000000000 : ℚ), (108881878470664983538782569717 / 100000000000000000000000000000 : ℚ)⟩
theorem b1562 (b : ℝ) (hb : rootInterval.Contains b) : i1562.Contains (n1562 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b310 b hb) (b1526 b hb))
    (by norm_num [i1562, i310, i1526, RationalInterval.mul]) (by norm_num [i1562, i310, i1526, RationalInterval.mul])

def n1563 (b : ℝ) : ℝ := (n310 b) * (n1529 b)
def i1563 : RationalInterval := ⟨(367901046577602714329867328647 / 500000000000000000000000000000 : ℚ), (735802105027183593143569796873 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1563 (b : ℝ) (hb : rootInterval.Contains b) : i1563.Contains (n1563 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b310 b hb) (b1529 b hb))
    (by norm_num [i1563, i310, i1529, RationalInterval.mul]) (by norm_num [i1563, i310, i1529, RationalInterval.mul])

def n1564 (b : ℝ) : ℝ := (n311 b) * (n1526 b)
def i1564 : RationalInterval := ⟨(630647932827225397232291755343 / 1000000000000000000000000000000 : ℚ), (630647943288685732130977239477 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1564 (b : ℝ) (hb : rootInterval.Contains b) : i1564.Contains (n1564 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b311 b hb) (b1526 b hb))
    (by norm_num [i1564, i311, i1526, RationalInterval.mul]) (by norm_num [i1564, i311, i1526, RationalInterval.mul])

def n1565 (b : ℝ) : ℝ := (n311 b) * (n1529 b)
def i1565 : RationalInterval := ⟨(21308967254322899070975426989 / 50000000000000000000000000000 : ℚ), (213089676041867079185587850099 / 500000000000000000000000000000 : ℚ)⟩
theorem b1565 (b : ℝ) (hb : rootInterval.Contains b) : i1565.Contains (n1565 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b311 b hb) (b1529 b hb))
    (by norm_num [i1565, i311, i1529, RationalInterval.mul]) (by norm_num [i1565, i311, i1529, RationalInterval.mul])

def n1566 (b : ℝ) : ℝ := (n1558 b) + (n1562 b)
def i1566 : RationalInterval := ⟨(734234189473933310692794886589 / 500000000000000000000000000000 : ℚ), (293693680808142951410167367121 / 200000000000000000000000000000 : ℚ)⟩
theorem b1566 (b : ℝ) (hb : rootInterval.Contains b) : i1566.Contains (n1566 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1558 b hb) (b1562 b hb))
    (by norm_num [i1566, i1558, i1562, RationalInterval.add]) (by norm_num [i1566, i1558, i1562, RationalInterval.add])

def n1567 (b : ℝ) : ℝ := (n1559 b) + (n1563 b)
def i1567 : RationalInterval := ⟨(1033186233899368595813403563199 / 1000000000000000000000000000000 : ℚ), (258296562822714265227254681211 / 250000000000000000000000000000 : ℚ)⟩
theorem b1567 (b : ℝ) (hb : rootInterval.Contains b) : i1567.Contains (n1567 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1559 b hb) (b1563 b hb))
    (by norm_num [i1567, i1559, i1563, RationalInterval.add]) (by norm_num [i1567, i1559, i1563, RationalInterval.add])

def n1568 (b : ℝ) : ℝ := (n1560 b) + (n1564 b)
def i1568 : RationalInterval := ⟨(449319031162306550610998861781 / 500000000000000000000000000000 : ℚ), (898638077893894732890475976911 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1568 (b : ℝ) (hb : rootInterval.Contains b) : i1568.Contains (n1568 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1560 b hb) (b1564 b hb))
    (by norm_num [i1568, i1560, i1564, RationalInterval.add]) (by norm_num [i1568, i1560, i1564, RationalInterval.add])

def n1569 (b : ℝ) : ℝ := (n1561 b) + (n1565 b)
def i1569 : RationalInterval := ⟨(31804963018671666428434843909 / 50000000000000000000000000000 : ℚ), (318049635604647692199288166149 / 500000000000000000000000000000 : ℚ)⟩
theorem b1569 (b : ℝ) (hb : rootInterval.Contains b) : i1569.Contains (n1569 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1561 b hb) (b1565 b hb))
    (by norm_num [i1569, i1561, i1565, RationalInterval.add]) (by norm_num [i1569, i1561, i1565, RationalInterval.add])

def n1570 (b : ℝ) : ℝ := (n1554 b) + (n1566 b)
def i1570 : RationalInterval := ⟨(734234189473933310692794886589 / 250000000000000000000000000000 : ℚ), (293693680808142951410167367121 / 100000000000000000000000000000 : ℚ)⟩
theorem b1570 (b : ℝ) (hb : rootInterval.Contains b) : i1570.Contains (n1570 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1554 b hb) (b1566 b hb))
    (by norm_num [i1570, i1554, i1566, RationalInterval.add]) (by norm_num [i1570, i1554, i1566, RationalInterval.add])

def n1571 (b : ℝ) : ℝ := (n1555 b) + (n1567 b)
def i1571 : RationalInterval := ⟨(1931824296223981697035401286761 / 1000000000000000000000000000000 : ℚ), (386364865836950358759898940351 / 200000000000000000000000000000 : ℚ)⟩
theorem b1571 (b : ℝ) (hb : rootInterval.Contains b) : i1571.Contains (n1571 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1555 b hb) (b1567 b hb))
    (by norm_num [i1571, i1555, i1567, RationalInterval.add]) (by norm_num [i1571, i1555, i1567, RationalInterval.add])

def n1572 (b : ℝ) : ℝ := (n1556 b) + (n1568 b)
def i1572 : RationalInterval := ⟨(1931824296223981697035401286761 / 1000000000000000000000000000000 : ℚ), (386364865836950358759898940351 / 200000000000000000000000000000 : ℚ)⟩
theorem b1572 (b : ℝ) (hb : rootInterval.Contains b) : i1572.Contains (n1572 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1556 b hb) (b1568 b hb))
    (by norm_num [i1572, i1556, i1568, RationalInterval.add]) (by norm_num [i1572, i1556, i1568, RationalInterval.add])

def n1573 (b : ℝ) : ℝ := (n1557 b) + (n1569 b)
def i1573 : RationalInterval := ⟨(31804963018671666428434843909 / 25000000000000000000000000000 : ℚ), (318049635604647692199288166149 / 250000000000000000000000000000 : ℚ)⟩
theorem b1573 (b : ℝ) (hb : rootInterval.Contains b) : i1573.Contains (n1573 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1557 b hb) (b1569 b hb))
    (by norm_num [i1573, i1557, i1569, RationalInterval.add]) (by norm_num [i1573, i1557, i1569, RationalInterval.add])

def n1574 (b : ℝ) : ℝ := 1 / (n329 b)
def i1574 : RationalInterval := ⟨(2249999993668850178262918015311 / 1000000000000000000000000000000 : ℚ), (450000001257971582021626260867 / 200000000000000000000000000000 : ℚ)⟩
theorem b1574 (b : ℝ) (hb : rootInterval.Contains b) : i1574.Contains (n1574 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_inv_of_positive (b329 b hb) (by norm_num [i329]))
    (by norm_num [i1574, i329, RationalInterval.inv]) (by norm_num [i1574, i329, RationalInterval.inv])

def n1575 (b : ℝ) : ℝ := (n16 b) * (n1574 b)
def i1575 : RationalInterval := ⟨(-450000001257971582021626260867 / 200000000000000000000000000000 : ℚ), (-2249999993668850178262918015311 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1575 (b : ℝ) (hb : rootInterval.Contains b) : i1575.Contains (n1575 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b16 b hb) (b1574 b hb))
    (by norm_num [i1575, i16, i1574, RationalInterval.mul]) (by norm_num [i1575, i16, i1574, RationalInterval.mul])

def n1576 (b : ℝ) : ℝ := (n1575 b) * (n1570 b)
def i1576 : RationalInterval := ⟨(-660810783665613162052747192141 / 100000000000000000000000000000 : ℚ), (-26432430746684852660121995793 / 4000000000000000000000000000 : ℚ)⟩
theorem b1576 (b : ℝ) (hb : rootInterval.Contains b) : i1576.Contains (n1576 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1575 b hb) (b1570 b hb))
    (by norm_num [i1576, i1575, i1570, RationalInterval.mul]) (by norm_num [i1576, i1575, i1570, RationalInterval.mul])

def n1577 (b : ℝ) : ℝ := (n1575 b) * (n1571 b)
def i1577 : RationalInterval := ⟨(-4346604752816592073910908685027 / 1000000000000000000000000000000 : ℚ), (-1086651163568322442415956827947 / 250000000000000000000000000000 : ℚ)⟩
theorem b1577 (b : ℝ) (hb : rootInterval.Contains b) : i1577.Contains (n1577 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1575 b hb) (b1571 b hb))
    (by norm_num [i1577, i1575, i1571, RationalInterval.mul]) (by norm_num [i1577, i1575, i1571, RationalInterval.mul])

def n1578 (b : ℝ) : ℝ := (n1575 b) * (n1572 b)
def i1578 : RationalInterval := ⟨(-4346604752816592073910908685027 / 1000000000000000000000000000000 : ℚ), (-1086651163568322442415956827947 / 250000000000000000000000000000 : ℚ)⟩
theorem b1578 (b : ℝ) (hb : rootInterval.Contains b) : i1578.Contains (n1578 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1575 b hb) (b1572 b hb))
    (by norm_num [i1578, i1575, i1572, RationalInterval.mul]) (by norm_num [i1578, i1575, i1572, RationalInterval.mul])

def n1579 (b : ℝ) : ℝ := (n1575 b) * (n1573 b)
def i1579 : RationalInterval := ⟨(-1431223364221888647526600830639 / 500000000000000000000000000000 : ℚ), (-2862446663625970540718431718573 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1579 (b : ℝ) (hb : rootInterval.Contains b) : i1579.Contains (n1579 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1575 b hb) (b1573 b hb))
    (by norm_num [i1579, i1575, i1573, RationalInterval.mul]) (by norm_num [i1579, i1575, i1573, RationalInterval.mul])

def n1580 (b : ℝ) : ℝ := (n329 b) * (n329 b)
def i1580 : RationalInterval := ⟨(12345678943321175487152193327 / 62500000000000000000000000000 : ℚ), (39506173061834617449328283981 / 200000000000000000000000000000 : ℚ)⟩
theorem b1580 (b : ℝ) (hb : rootInterval.Contains b) : i1580.Contains (n1580 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b329 b hb) (b329 b hb))
    (by norm_num [i1580, i329, i329, RationalInterval.mul]) (by norm_num [i1580, i329, i329, RationalInterval.mul])

def n1581 (b : ℝ) : ℝ := 1 / (n1580 b)
def i1581 : RationalInterval := ⟨(632812496438728230283323641771 / 125000000000000000000000000000 : ℚ), (2531250014152180317524451699431 / 500000000000000000000000000000 : ℚ)⟩
theorem b1581 (b : ℝ) (hb : rootInterval.Contains b) : i1581.Contains (n1581 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_inv_of_positive (b1580 b hb) (by norm_num [i1580]))
    (by norm_num [i1581, i1580, RationalInterval.inv]) (by norm_num [i1581, i1580, RationalInterval.inv])

def n1582 (b : ℝ) : ℝ := (n1498 b) * (n1581 b)
def i1582 : RationalInterval := ⟨(1092784918022181033487751974021 / 125000000000000000000000000000 : ℚ), (4371139788917999808922952527371 / 500000000000000000000000000000 : ℚ)⟩
theorem b1582 (b : ℝ) (hb : rootInterval.Contains b) : i1582.Contains (n1582 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1498 b hb) (b1581 b hb))
    (by norm_num [i1582, i1498, i1581, RationalInterval.mul]) (by norm_num [i1582, i1498, i1581, RationalInterval.mul])

def n1583 (b : ℝ) : ℝ := (n1582 b) * (n1516 b)
def i1583 : RationalInterval := ⟨(1413963194899534939538009569799 / 200000000000000000000000000000 : ℚ), (7069816219838715093642111404793 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1583 (b : ℝ) (hb : rootInterval.Contains b) : i1583.Contains (n1583 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1582 b hb) (b1516 b hb))
    (by norm_num [i1583, i1582, i1516, RationalInterval.mul]) (by norm_num [i1583, i1582, i1516, RationalInterval.mul])

def n1584 (b : ℝ) : ℝ := (n1582 b) * (n1517 b)
def i1584 : RationalInterval := ⟨(240818414033189362463003582269 / 50000000000000000000000000000 : ℚ), (2408184223121489512391767814991 / 500000000000000000000000000000 : ℚ)⟩
theorem b1584 (b : ℝ) (hb : rootInterval.Contains b) : i1584.Contains (n1584 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1582 b hb) (b1517 b hb))
    (by norm_num [i1584, i1582, i1517, RationalInterval.mul]) (by norm_num [i1584, i1582, i1517, RationalInterval.mul])

def n1585 (b : ℝ) : ℝ := (n1582 b) * (n1518 b)
def i1585 : RationalInterval := ⟨(240818414033189362463003582269 / 50000000000000000000000000000 : ℚ), (2408184223121489512391767814991 / 500000000000000000000000000000 : ℚ)⟩
theorem b1585 (b : ℝ) (hb : rootInterval.Contains b) : i1585.Contains (n1585 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1582 b hb) (b1518 b hb))
    (by norm_num [i1585, i1582, i1518, RationalInterval.mul]) (by norm_num [i1585, i1582, i1518, RationalInterval.mul])

def n1586 (b : ℝ) : ℝ := (n1582 b) * (n1519 b)
def i1586 : RationalInterval := ⟨(128302264993869416873669957301 / 40000000000000000000000000000 : ℚ), (1603778367292951607665766722973 / 500000000000000000000000000000 : ℚ)⟩
theorem b1586 (b : ℝ) (hb : rootInterval.Contains b) : i1586.Contains (n1586 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1582 b hb) (b1519 b hb))
    (by norm_num [i1586, i1582, i1519, RationalInterval.mul]) (by norm_num [i1586, i1582, i1519, RationalInterval.mul])

def n1587 (b : ℝ) : ℝ := (n1576 b) + (n1583 b)
def i1587 : RationalInterval := ⟨(92341627568308615432515185517 / 200000000000000000000000000000 : ℚ), (461708533167501928611612456543 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1587 (b : ℝ) (hb : rootInterval.Contains b) : i1587.Contains (n1587 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1576 b hb) (b1583 b hb))
    (by norm_num [i1587, i1576, i1583, RationalInterval.add]) (by norm_num [i1587, i1576, i1583, RationalInterval.add])

def n1588 (b : ℝ) : ℝ := (n1577 b) + (n1584 b)
def i1588 : RationalInterval := ⟨(469763527847195175349162960353 / 1000000000000000000000000000000 : ℚ), (234881895984844627559854159097 / 500000000000000000000000000000 : ℚ)⟩
theorem b1588 (b : ℝ) (hb : rootInterval.Contains b) : i1588.Contains (n1588 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1577 b hb) (b1584 b hb))
    (by norm_num [i1588, i1577, i1584, RationalInterval.add]) (by norm_num [i1588, i1577, i1584, RationalInterval.add])

def n1589 (b : ℝ) : ℝ := (n1578 b) + (n1585 b)
def i1589 : RationalInterval := ⟨(469763527847195175349162960353 / 1000000000000000000000000000000 : ℚ), (234881895984844627559854159097 / 500000000000000000000000000000 : ℚ)⟩
theorem b1589 (b : ℝ) (hb : rootInterval.Contains b) : i1589.Contains (n1589 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1578 b hb) (b1585 b hb))
    (by norm_num [i1589, i1578, i1585, RationalInterval.add]) (by norm_num [i1589, i1578, i1585, RationalInterval.add])

def n1590 (b : ℝ) : ℝ := (n1579 b) + (n1586 b)
def i1590 : RationalInterval := ⟨(345109896402958126788547271247 / 1000000000000000000000000000000 : ℚ), (345110070959932674613101727373 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1590 (b : ℝ) (hb : rootInterval.Contains b) : i1590.Contains (n1590 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1579 b hb) (b1586 b hb))
    (by norm_num [i1590, i1579, i1586, RationalInterval.add]) (by norm_num [i1590, i1579, i1586, RationalInterval.add])

def n1591 (b : ℝ) : ℝ := (n1498 b) + (n1533 b)
def i1591 : RationalInterval := ⟨(126837480257556029219098308163 / 40000000000000000000000000000 : ℚ), (792734264464070078108663702531 / 250000000000000000000000000000 : ℚ)⟩
theorem b1591 (b : ℝ) (hb : rootInterval.Contains b) : i1591.Contains (n1591 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1498 b hb) (b1533 b hb))
    (by norm_num [i1591, i1498, i1533, RationalInterval.add]) (by norm_num [i1591, i1498, i1533, RationalInterval.add])

def n1592 (b : ℝ) : ℝ := (n1591 b) * (n1581 b)
def i1592 : RationalInterval := ⟨(16052868504756387391396017780551 / 1000000000000000000000000000000 : ℚ), (16052868945148765118305527538761 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1592 (b : ℝ) (hb : rootInterval.Contains b) : i1592.Contains (n1592 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1591 b hb) (b1581 b hb))
    (by norm_num [i1592, i1591, i1581, RationalInterval.mul]) (by norm_num [i1592, i1591, i1581, RationalInterval.mul])

def n1593 (b : ℝ) : ℝ := (n329 b) + (n1507 b)
def i1593 : RationalInterval := ⟨(379756708940692322708543688427 / 500000000000000000000000000000 : ℚ), (379756711431832519178671867901 / 500000000000000000000000000000 : ℚ)⟩
theorem b1593 (b : ℝ) (hb : rootInterval.Contains b) : i1593.Contains (n1593 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b329 b hb) (b1507 b hb))
    (by norm_num [i1593, i329, i1507, RationalInterval.add]) (by norm_num [i1593, i329, i1507, RationalInterval.add])

def n1594 (b : ℝ) : ℝ := (n1593 b) * (n13 b)
def i1594 : RationalInterval := ⟨(379756708940692322708543688427 / 250000000000000000000000000000 : ℚ), (379756711431832519178671867901 / 250000000000000000000000000000 : ℚ)⟩
theorem b1594 (b : ℝ) (hb : rootInterval.Contains b) : i1594.Contains (n1594 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1593 b hb) (b13 b hb))
    (by norm_num [i1594, i1593, i13, RationalInterval.mul]) (by norm_num [i1594, i1593, i13, RationalInterval.mul])

def n1595 (b : ℝ) : ℝ := (n1594 b) * (n1498 b)
def i1595 : RationalInterval := ⟨(327895234673442614002417133237 / 125000000000000000000000000000 : ℚ), (2623161935276988026215050826989 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1595 (b : ℝ) (hb : rootInterval.Contains b) : i1595.Contains (n1595 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1594 b hb) (b1498 b hb))
    (by norm_num [i1595, i1594, i1498, RationalInterval.mul]) (by norm_num [i1595, i1594, i1498, RationalInterval.mul])

def n1596 (b : ℝ) : ℝ := (n1580 b) * (n329 b)
def i1596 : RationalInterval := ⟨(43895747231320618201861534253 / 500000000000000000000000000000 : ℚ), (21947873984999355679687539951 / 250000000000000000000000000000 : ℚ)⟩
theorem b1596 (b : ℝ) (hb : rootInterval.Contains b) : i1596.Contains (n1596 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1580 b hb) (b329 b hb))
    (by norm_num [i1596, i1580, i329, RationalInterval.mul]) (by norm_num [i1596, i1580, i329, RationalInterval.mul])

def n1597 (b : ℝ) : ℝ := 1 / (n1596 b)
def i1597 : RationalInterval := ⟨(5695312451922831176465704522149 / 500000000000000000000000000000 : ℚ), (11390625095527217276812854006643 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1597 (b : ℝ) (hb : rootInterval.Contains b) : i1597.Contains (n1597 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_inv_of_positive (b1596 b hb) (by norm_num [i1596]))
    (by norm_num [i1597, i1596, RationalInterval.inv]) (by norm_num [i1597, i1596, RationalInterval.inv])

def n1598 (b : ℝ) : ℝ := (n1595 b) * (n1597 b)
def i1598 : RationalInterval := ⟨(7469863251847266334932578240189 / 250000000000000000000000000000 : ℚ), (29879454169597801879575545438431 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1598 (b : ℝ) (hb : rootInterval.Contains b) : i1598.Contains (n1598 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1595 b hb) (b1597 b hb))
    (by norm_num [i1598, i1595, i1597, RationalInterval.mul]) (by norm_num [i1598, i1595, i1597, RationalInterval.mul])

def n1599 (b : ℝ) : ℝ := -(n1598 b)
def i1599 : RationalInterval := ⟨(-29879454169597801879575545438431 / 1000000000000000000000000000000 : ℚ), (-7469863251847266334932578240189 / 250000000000000000000000000000 : ℚ)⟩
theorem b1599 (b : ℝ) (hb : rootInterval.Contains b) : i1599.Contains (n1599 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b1598 b hb))
    (by norm_num [i1599, i1598, RationalInterval.neg]) (by norm_num [i1599, i1598, RationalInterval.neg])

def n1600 (b : ℝ) : ℝ := (n1592 b) + (n1599 b)
def i1600 : RationalInterval := ⟨(-345664641621035362204488191447 / 25000000000000000000000000000 : ℚ), (-2765316812448060044284957084399 / 200000000000000000000000000000 : ℚ)⟩
theorem b1600 (b : ℝ) (hb : rootInterval.Contains b) : i1600.Contains (n1600 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1592 b hb) (b1599 b hb))
    (by norm_num [i1600, i1592, i1599, RationalInterval.add]) (by norm_num [i1600, i1592, i1599, RationalInterval.add])

def n1601 (b : ℝ) : ℝ := (n1600 b) * (n1520 b)
def i1601 : RationalInterval := ⟨(-5497645867116952945545737237351 / 500000000000000000000000000000 : ℚ), (-2199058081992949045814157345849 / 200000000000000000000000000000 : ℚ)⟩
theorem b1601 (b : ℝ) (hb : rootInterval.Contains b) : i1601.Contains (n1601 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1600 b hb) (b1520 b hb))
    (by norm_num [i1601, i1600, i1520, RationalInterval.mul]) (by norm_num [i1601, i1600, i1520, RationalInterval.mul])

def n1602 (b : ℝ) : ℝ := (n1600 b) * (n1521 b)
def i1602 : RationalInterval := ⟨(-3184257203976281519275636891971 / 500000000000000000000000000000 : ℚ), (-1592128409780753137752572740413 / 250000000000000000000000000000 : ℚ)⟩
theorem b1602 (b : ℝ) (hb : rootInterval.Contains b) : i1602.Contains (n1602 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1600 b hb) (b1521 b hb))
    (by norm_num [i1602, i1600, i1521, RationalInterval.mul]) (by norm_num [i1602, i1600, i1521, RationalInterval.mul])

def n1603 (b : ℝ) : ℝ := (n1600 b) * (n1522 b)
def i1603 : RationalInterval := ⟨(-3184257203976281519275636891971 / 500000000000000000000000000000 : ℚ), (-1592128409780753137752572740413 / 250000000000000000000000000000 : ℚ)⟩
theorem b1603 (b : ℝ) (hb : rootInterval.Contains b) : i1603.Contains (n1603 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1600 b hb) (b1522 b hb))
    (by norm_num [i1603, i1600, i1522, RationalInterval.mul]) (by norm_num [i1603, i1600, i1522, RationalInterval.mul])

def n1604 (b : ℝ) : ℝ := (n1600 b) * (n1523 b)
def i1604 : RationalInterval := ⟨(-230541721542173177015205867309 / 62500000000000000000000000000 : ℚ), (-1844333549159338650535694459163 / 500000000000000000000000000000 : ℚ)⟩
theorem b1604 (b : ℝ) (hb : rootInterval.Contains b) : i1604.Contains (n1604 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1600 b hb) (b1523 b hb))
    (by norm_num [i1604, i1600, i1523, RationalInterval.mul]) (by norm_num [i1604, i1600, i1523, RationalInterval.mul])

def n1605 (b : ℝ) : ℝ := (n1587 b) + (n1601 b)
def i1605 : RationalInterval := ⟨(-10533583596392362813928898547117 / 1000000000000000000000000000000 : ℚ), (-5266790938398621650229587136351 / 500000000000000000000000000000 : ℚ)⟩
theorem b1605 (b : ℝ) (hb : rootInterval.Contains b) : i1605.Contains (n1605 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1587 b hb) (b1601 b hb))
    (by norm_num [i1605, i1587, i1601, RationalInterval.add]) (by norm_num [i1605, i1587, i1601, RationalInterval.add])

def n1606 (b : ℝ) : ℝ := (n1588 b) + (n1602 b)
def i1606 : RationalInterval := ⟨(-5898750880105367863202110823589 / 1000000000000000000000000000000 : ℚ), (-2949374923576661647945291321729 / 500000000000000000000000000000 : ℚ)⟩
theorem b1606 (b : ℝ) (hb : rootInterval.Contains b) : i1606.Contains (n1606 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1588 b hb) (b1602 b hb))
    (by norm_num [i1606, i1588, i1602, RationalInterval.add]) (by norm_num [i1606, i1588, i1602, RationalInterval.add])

def n1607 (b : ℝ) : ℝ := (n1589 b) + (n1603 b)
def i1607 : RationalInterval := ⟨(-5898750880105367863202110823589 / 1000000000000000000000000000000 : ℚ), (-2949374923576661647945291321729 / 500000000000000000000000000000 : ℚ)⟩
theorem b1607 (b : ℝ) (hb : rootInterval.Contains b) : i1607.Contains (n1607 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1589 b hb) (b1603 b hb))
    (by norm_num [i1607, i1589, i1603, RationalInterval.add]) (by norm_num [i1607, i1589, i1603, RationalInterval.add])

def n1608 (b : ℝ) : ℝ := (n1590 b) + (n1604 b)
def i1608 : RationalInterval := ⟨(-3343557648271812705454746605697 / 1000000000000000000000000000000 : ℚ), (-3343557027358744626458287190953 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1608 (b : ℝ) (hb : rootInterval.Contains b) : i1608.Contains (n1608 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1590 b hb) (b1604 b hb))
    (by norm_num [i1608, i1590, i1604, RationalInterval.add]) (by norm_num [i1608, i1590, i1604, RationalInterval.add])

def n1609 (b : ℝ) : ℝ := (n1593 b) * (n1581 b)
def i1609 : RationalInterval := ⟨(769007331277168043369600587133 / 200000000000000000000000000000 : ℚ), (769007344948969216915525026773 / 200000000000000000000000000000 : ℚ)⟩
theorem b1609 (b : ℝ) (hb : rootInterval.Contains b) : i1609.Contains (n1609 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1593 b hb) (b1581 b hb))
    (by norm_num [i1609, i1593, i1581, RationalInterval.mul]) (by norm_num [i1609, i1593, i1581, RationalInterval.mul])

def n1610 (b : ℝ) : ℝ := (n1609 b) * (n1542 b)
def i1610 : RationalInterval := ⟨(1148369919652049739359533364459 / 200000000000000000000000000000 : ℚ), (1148369958317367286177647896397 / 200000000000000000000000000000 : ℚ)⟩
theorem b1610 (b : ℝ) (hb : rootInterval.Contains b) : i1610.Contains (n1610 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1609 b hb) (b1542 b hb))
    (by norm_num [i1610, i1609, i1542, RationalInterval.mul]) (by norm_num [i1610, i1609, i1542, RationalInterval.mul])

def n1611 (b : ℝ) : ℝ := (n1609 b) * (n1543 b)
def i1611 : RationalInterval := ⟨(461175251212316765270825856823 / 125000000000000000000000000000 : ℚ), (737880426767200663039469736299 / 200000000000000000000000000000 : ℚ)⟩
theorem b1611 (b : ℝ) (hb : rootInterval.Contains b) : i1611.Contains (n1611 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1609 b hb) (b1543 b hb))
    (by norm_num [i1611, i1609, i1543, RationalInterval.mul]) (by norm_num [i1611, i1609, i1543, RationalInterval.mul])

def n1612 (b : ℝ) : ℝ := (n1609 b) * (n1544 b)
def i1612 : RationalInterval := ⟨(461175251212316765270825856823 / 125000000000000000000000000000 : ℚ), (737880426767200663039469736299 / 200000000000000000000000000000 : ℚ)⟩
theorem b1612 (b : ℝ) (hb : rootInterval.Contains b) : i1612.Contains (n1612 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1609 b hb) (b1544 b hb))
    (by norm_num [i1612, i1609, i1544, RationalInterval.mul]) (by norm_num [i1612, i1609, i1544, RationalInterval.mul])

def n1613 (b : ℝ) : ℝ := (n1609 b) * (n1545 b)
def i1613 : RationalInterval := ⟨(586893146495614111022217278967 / 250000000000000000000000000000 : ℚ), (1173786332523606105870413394159 / 500000000000000000000000000000 : ℚ)⟩
theorem b1613 (b : ℝ) (hb : rootInterval.Contains b) : i1613.Contains (n1613 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1609 b hb) (b1545 b hb))
    (by norm_num [i1613, i1609, i1545, RationalInterval.mul]) (by norm_num [i1613, i1609, i1545, RationalInterval.mul])

def n1614 (b : ℝ) : ℝ := (n1605 b) + (n1610 b)
def i1614 : RationalInterval := ⟨(-2395866999066057058565615862411 / 500000000000000000000000000000 : ℚ), (-4791732085210406869570934790717 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1614 (b : ℝ) (hb : rootInterval.Contains b) : i1614.Contains (n1614 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1605 b hb) (b1610 b hb))
    (by norm_num [i1614, i1605, i1610, RationalInterval.add]) (by norm_num [i1614, i1605, i1610, RationalInterval.add])

def n1615 (b : ℝ) : ℝ := (n1606 b) + (n1611 b)
def i1615 : RationalInterval := ⟨(-441869774081366748207100793801 / 200000000000000000000000000000 : ℚ), (-2209347713317319980693233961963 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1615 (b : ℝ) (hb : rootInterval.Contains b) : i1615.Contains (n1615 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1606 b hb) (b1611 b hb))
    (by norm_num [i1615, i1606, i1611, RationalInterval.add]) (by norm_num [i1615, i1606, i1611, RationalInterval.add])

def n1616 (b : ℝ) : ℝ := (n1607 b) + (n1612 b)
def i1616 : RationalInterval := ⟨(-441869774081366748207100793801 / 200000000000000000000000000000 : ℚ), (-2209347713317319980693233961963 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1616 (b : ℝ) (hb : rootInterval.Contains b) : i1616.Contains (n1616 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1607 b hb) (b1612 b hb))
    (by norm_num [i1616, i1607, i1612, RationalInterval.add]) (by norm_num [i1616, i1607, i1612, RationalInterval.add])

def n1617 (b : ℝ) : ℝ := (n1608 b) + (n1613 b)
def i1617 : RationalInterval := ⟨(-995985062289356261365877489829 / 1000000000000000000000000000000 : ℚ), (-199196872462306482943492080527 / 200000000000000000000000000000 : ℚ)⟩
theorem b1617 (b : ℝ) (hb : rootInterval.Contains b) : i1617.Contains (n1617 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1608 b hb) (b1613 b hb))
    (by norm_num [i1617, i1608, i1613, RationalInterval.add]) (by norm_num [i1617, i1608, i1613, RationalInterval.add])

def n1618 (b : ℝ) : ℝ := (n90 b) * (n211 b)
def i1618 : RationalInterval := ⟨(-480864103617149421244945087237 / 500000000000000000000000000000 : ℚ), (-961728196118245263013929588419 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1618 (b : ℝ) (hb : rootInterval.Contains b) : i1618.Contains (n1618 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b90 b hb) (b211 b hb))
    (by norm_num [i1618, i90, i211, RationalInterval.mul]) (by norm_num [i1618, i90, i211, RationalInterval.mul])

def n1619 (b : ℝ) : ℝ := (n91 b) * (n213 b)
def i1619 : RationalInterval := ⟨(-249611917221637940536476024717 / 125000000000000000000000000000 : ℚ), (-249611914845628837979988039161 / 125000000000000000000000000000 : ℚ)⟩
theorem b1619 (b : ℝ) (hb : rootInterval.Contains b) : i1619.Contains (n1619 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b91 b hb) (b213 b hb))
    (by norm_num [i1619, i91, i213, RationalInterval.mul]) (by norm_num [i1619, i91, i213, RationalInterval.mul])

