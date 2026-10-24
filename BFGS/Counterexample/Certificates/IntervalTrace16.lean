import BFGS.Counterexample.Certificates.IntervalTrace15

/-! Generated arithmetic proofs. Each bound is checked by the Lean kernel. -/
namespace BFGS.Counterexample.Trace
noncomputable section
open BFGS RationalInterval
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false

def n1440 (b : ℝ) : ℝ := (n1438 b) + (n1439 b)
def i1440 : RationalInterval := ⟨(1032900745608417897811300349273 / 1000000000000000000000000000000 : ℚ), (1032901008798115916886293285907 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1440 (b : ℝ) (hb : rootInterval.Contains b) : i1440.Contains (n1440 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1438 b hb) (b1439 b hb))
    (by norm_num [i1440, i1438, i1439, RationalInterval.add]) (by norm_num [i1440, i1438, i1439, RationalInterval.add])

def n1441 (b : ℝ) : ℝ := (n1251 b) * (n681 b)
def i1441 : RationalInterval := ⟨(78180795129385184263834271931 / 500000000000000000000000000000 : ℚ), (156361648742701525196352568921 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1441 (b : ℝ) (hb : rootInterval.Contains b) : i1441.Contains (n1441 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1251 b hb) (b681 b hb))
    (by norm_num [i1441, i1251, i681, RationalInterval.mul]) (by norm_num [i1441, i1251, i681, RationalInterval.mul])

def n1442 (b : ℝ) : ℝ := (n1440 b) + (n1441 b)
def i1442 : RationalInterval := ⟨(237852467173437653267793778627 / 200000000000000000000000000000 : ℚ), (297315664385204360520661463707 / 250000000000000000000000000000 : ℚ)⟩
theorem b1442 (b : ℝ) (hb : rootInterval.Contains b) : i1442.Contains (n1442 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1440 b hb) (b1441 b hb))
    (by norm_num [i1442, i1440, i1441, RationalInterval.add]) (by norm_num [i1442, i1440, i1441, RationalInterval.add])

def n1443 (b : ℝ) : ℝ := (n1328 b) * (n683 b)
def i1443 : RationalInterval := ⟨(-159346325771292185234702247697 / 250000000000000000000000000000 : ℚ), (-637385170913188922172699432909 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1443 (b : ℝ) (hb : rootInterval.Contains b) : i1443.Contains (n1443 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1328 b hb) (b683 b hb))
    (by norm_num [i1443, i1328, i683, RationalInterval.mul]) (by norm_num [i1443, i1328, i683, RationalInterval.mul])

def n1444 (b : ℝ) : ℝ := (n1442 b) + (n1443 b)
def i1444 : RationalInterval := ⟨(551877032782019525400159902347 / 1000000000000000000000000000000 : ℚ), (551877486627628519909946421919 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1444 (b : ℝ) (hb : rootInterval.Contains b) : i1444.Contains (n1444 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1442 b hb) (b1443 b hb))
    (by norm_num [i1444, i1442, i1443, RationalInterval.add]) (by norm_num [i1444, i1442, i1443, RationalInterval.add])

def n1445 (b : ℝ) : ℝ := (n1047 b) * (n689 b)
def i1445 : RationalInterval := ⟨(278031195768660878630475310281 / 200000000000000000000000000000 : ℚ), (347539069317318642244566109633 / 250000000000000000000000000000 : ℚ)⟩
theorem b1445 (b : ℝ) (hb : rootInterval.Contains b) : i1445.Contains (n1445 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1047 b hb) (b689 b hb))
    (by norm_num [i1445, i1047, i689, RationalInterval.mul]) (by norm_num [i1445, i1047, i689, RationalInterval.mul])

def n1446 (b : ℝ) : ℝ := (n1158 b) * (n691 b)
def i1446 : RationalInterval := ⟨(-237398505683917611837373222977 / 125000000000000000000000000000 : ℚ), (-1899187615953216385754958326357 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1446 (b : ℝ) (hb : rootInterval.Contains b) : i1446.Contains (n1446 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1158 b hb) (b691 b hb))
    (by norm_num [i1446, i1158, i691, RationalInterval.mul]) (by norm_num [i1446, i1158, i691, RationalInterval.mul])

def n1447 (b : ℝ) : ℝ := (n1445 b) + (n1446 b)
def i1447 : RationalInterval := ⟨(-509032066628036501546609232411 / 1000000000000000000000000000000 : ℚ), (-20361253547357672671067755513 / 40000000000000000000000000000 : ℚ)⟩
theorem b1447 (b : ℝ) (hb : rootInterval.Contains b) : i1447.Contains (n1447 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1445 b hb) (b1446 b hb))
    (by norm_num [i1447, i1445, i1446, RationalInterval.add]) (by norm_num [i1447, i1445, i1446, RationalInterval.add])

def n1448 (b : ℝ) : ℝ := (n1171 b) * (n776 b)
def i1448 : RationalInterval := ⟨(78597331074593805130950392937 / 125000000000000000000000000000 : ℚ), (314389342069405102678934988069 / 500000000000000000000000000000 : ℚ)⟩
theorem b1448 (b : ℝ) (hb : rootInterval.Contains b) : i1448.Contains (n1448 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1171 b hb) (b776 b hb))
    (by norm_num [i1448, i1171, i776, RationalInterval.mul]) (by norm_num [i1448, i1171, i776, RationalInterval.mul])

def n1449 (b : ℝ) : ℝ := (n1447 b) + (n1448 b)
def i1449 : RationalInterval := ⟨(23949316393742787900198782217 / 200000000000000000000000000000 : ℚ), (119747345454868388581176088313 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1449 (b : ℝ) (hb : rootInterval.Contains b) : i1449.Contains (n1449 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1447 b hb) (b1448 b hb))
    (by norm_num [i1449, i1447, i1448, RationalInterval.add]) (by norm_num [i1449, i1447, i1448, RationalInterval.add])

def n1450 (b : ℝ) : ℝ := (n1251 b) * (n777 b)
def i1450 : RationalInterval := ⟨(-540212379526407176358262568089 / 500000000000000000000000000000 : ℚ), (-108042456942090453133485516941 / 100000000000000000000000000000 : ℚ)⟩
theorem b1450 (b : ℝ) (hb : rootInterval.Contains b) : i1450.Contains (n1450 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1251 b hb) (b777 b hb))
    (by norm_num [i1450, i1251, i777, RationalInterval.mul]) (by norm_num [i1450, i1251, i777, RationalInterval.mul])

def n1451 (b : ℝ) : ℝ := (n1449 b) + (n1450 b)
def i1451 : RationalInterval := ⟨(-960678177084100413215531225093 / 1000000000000000000000000000000 : ℚ), (-960677223966036142753679081097 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1451 (b : ℝ) (hb : rootInterval.Contains b) : i1451.Contains (n1451 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1449 b hb) (b1450 b hb))
    (by norm_num [i1451, i1449, i1450, RationalInterval.add]) (by norm_num [i1451, i1449, i1450, RationalInterval.add])

def n1452 (b : ℝ) : ℝ := (n1328 b) * (n779 b)
def i1452 : RationalInterval := ⟨(2705205529062503349439639754851 / 1000000000000000000000000000000 : ℚ), (2705205861061031879218371686677 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1452 (b : ℝ) (hb : rootInterval.Contains b) : i1452.Contains (n1452 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1328 b hb) (b779 b hb))
    (by norm_num [i1452, i1328, i779, RationalInterval.mul]) (by norm_num [i1452, i1328, i779, RationalInterval.mul])

def n1453 (b : ℝ) : ℝ := (n1451 b) + (n1452 b)
def i1453 : RationalInterval := ⟨(872263675989201468112054264879 / 500000000000000000000000000000 : ℚ), (87226431854749786823234630279 / 50000000000000000000000000000 : ℚ)⟩
theorem b1453 (b : ℝ) (hb : rootInterval.Contains b) : i1453.Contains (n1453 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1451 b hb) (b1452 b hb))
    (by norm_num [i1453, i1451, i1452, RationalInterval.add]) (by norm_num [i1453, i1451, i1452, RationalInterval.add])

def n1454 (b : ℝ) : ℝ := (n1047 b) * (n16 b)
def i1454 : RationalInterval := ⟨(-2452916096311304192811382477987 / 1000000000000000000000000000000 : ℚ), (-2452915574559471639290991026117 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1454 (b : ℝ) (hb : rootInterval.Contains b) : i1454.Contains (n1454 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1047 b hb) (b16 b hb))
    (by norm_num [i1454, i1047, i16, RationalInterval.mul]) (by norm_num [i1454, i1047, i16, RationalInterval.mul])

def n1455 (b : ℝ) : ℝ := (n1171 b) * (n839 b)
def i1455 : RationalInterval := ⟨(-587473029025389575285023932093 / 500000000000000000000000000000 : ℚ), (-587473024152917990481554333359 / 500000000000000000000000000000 : ℚ)⟩
theorem b1455 (b : ℝ) (hb : rootInterval.Contains b) : i1455.Contains (n1455 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1171 b hb) (b839 b hb))
    (by norm_num [i1455, i1171, i839, RationalInterval.mul]) (by norm_num [i1455, i1171, i839, RationalInterval.mul])

def n1456 (b : ℝ) : ℝ := (n1454 b) + (n1455 b)
def i1456 : RationalInterval := ⟨(-3627862154362083343381430342173 / 1000000000000000000000000000000 : ℚ), (-725572324573061524050819938567 / 200000000000000000000000000000 : ℚ)⟩
theorem b1456 (b : ℝ) (hb : rootInterval.Contains b) : i1456.Contains (n1456 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1454 b hb) (b1455 b hb))
    (by norm_num [i1456, i1454, i1455, RationalInterval.add]) (by norm_num [i1456, i1454, i1455, RationalInterval.add])

def n1457 (b : ℝ) : ℝ := (n1251 b) * (n840 b)
def i1457 : RationalInterval := ⟨(2308249540394251123192464473353 / 1000000000000000000000000000000 : ℚ), (2308249855248021412990919422681 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1457 (b : ℝ) (hb : rootInterval.Contains b) : i1457.Contains (n1457 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1251 b hb) (b840 b hb))
    (by norm_num [i1457, i1251, i840, RationalInterval.mul]) (by norm_num [i1457, i1251, i840, RationalInterval.mul])

def n1458 (b : ℝ) : ℝ := (n1456 b) + (n1457 b)
def i1458 : RationalInterval := ⟨(-65980630698391611009448293441 / 50000000000000000000000000000 : ℚ), (-659805883808643103631590135077 / 500000000000000000000000000000 : ℚ)⟩
theorem b1458 (b : ℝ) (hb : rootInterval.Contains b) : i1458.Contains (n1458 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1456 b hb) (b1457 b hb))
    (by norm_num [i1458, i1456, i1457, RationalInterval.add]) (by norm_num [i1458, i1456, i1457, RationalInterval.add])

def n1459 (b : ℝ) : ℝ := (n1328 b) * (n836 b)
def i1459 : RationalInterval := ⟨(-15146188918438144064745719771 / 2500000000000000000000000000 : ℚ), (-3029237507879356285632979040837 / 500000000000000000000000000000 : ℚ)⟩
theorem b1459 (b : ℝ) (hb : rootInterval.Contains b) : i1459.Contains (n1459 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1328 b hb) (b836 b hb))
    (by norm_num [i1459, i1328, i836, RationalInterval.mul]) (by norm_num [i1459, i1328, i836, RationalInterval.mul])

def n1460 (b : ℝ) : ℝ := (n1458 b) + (n1459 b)
def i1460 : RationalInterval := ⟨(-368904409067154492304362688861 / 50000000000000000000000000000 : ℚ), (-1844521695843999694632284587957 / 250000000000000000000000000000 : ℚ)⟩
theorem b1460 (b : ℝ) (hb : rootInterval.Contains b) : i1460.Contains (n1460 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1458 b hb) (b1459 b hb))
    (by norm_num [i1460, i1458, i1459, RationalInterval.add]) (by norm_num [i1460, i1458, i1459, RationalInterval.add])

def n1461 (b : ℝ) : ℝ := (n1158 b) * (n16 b)
def i1461 : RationalInterval := ⟨(1569118609228725784919936408603 / 1000000000000000000000000000000 : ℚ), (1569118963277250234555153565099 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1461 (b : ℝ) (hb : rootInterval.Contains b) : i1461.Contains (n1461 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1158 b hb) (b16 b hb))
    (by norm_num [i1461, i1158, i16, RationalInterval.mul]) (by norm_num [i1461, i1158, i16, RationalInterval.mul])

def n1462 (b : ℝ) : ℝ := (n1171 b) * (n896 b)
def i1462 : RationalInterval := ⟨(596441669938303286615186276301 / 1000000000000000000000000000000 : ℚ), (596441675569834737071455656483 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1462 (b : ℝ) (hb : rootInterval.Contains b) : i1462.Contains (n1462 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1171 b hb) (b896 b hb))
    (by norm_num [i1462, i1171, i896, RationalInterval.mul]) (by norm_num [i1462, i1171, i896, RationalInterval.mul])

def n1463 (b : ℝ) : ℝ := (n1461 b) + (n1462 b)
def i1463 : RationalInterval := ⟨(270695034895878633941890335613 / 125000000000000000000000000000 : ℚ), (1082780319423542485813304610791 / 500000000000000000000000000000 : ℚ)⟩
theorem b1463 (b : ℝ) (hb : rootInterval.Contains b) : i1463.Contains (n1463 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1461 b hb) (b1462 b hb))
    (by norm_num [i1463, i1461, i1462, RationalInterval.add]) (by norm_num [i1463, i1461, i1462, RationalInterval.add])

def n1464 (b : ℝ) : ℝ := (n1251 b) * (n900 b)
def i1464 : RationalInterval := ⟨(-161662439531108157788832691481 / 125000000000000000000000000000 : ℚ), (-1293299339469921503274253161921 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1464 (b : ℝ) (hb : rootInterval.Contains b) : i1464.Contains (n1464 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1251 b hb) (b900 b hb))
    (by norm_num [i1464, i1251, i900, RationalInterval.mul]) (by norm_num [i1464, i1251, i900, RationalInterval.mul])

def n1465 (b : ℝ) : ℝ := (n1463 b) + (n1464 b)
def i1465 : RationalInterval := ⟨(27258148841192619038264411033 / 31250000000000000000000000000 : ℚ), (872261299377163468352356059661 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1465 (b : ℝ) (hb : rootInterval.Contains b) : i1465.Contains (n1465 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1463 b hb) (b1464 b hb))
    (by norm_num [i1465, i1463, i1464, RationalInterval.add]) (by norm_num [i1465, i1463, i1464, RationalInterval.add])

def n1466 (b : ℝ) : ℝ := (n1328 b) * (n902 b)
def i1466 : RationalInterval := ⟨(154363651161793242495489849613 / 62500000000000000000000000000 : ℚ), (1234909323763298637425602684761 / 500000000000000000000000000000 : ℚ)⟩
theorem b1466 (b : ℝ) (hb : rootInterval.Contains b) : i1466.Contains (n1466 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1328 b hb) (b902 b hb))
    (by norm_num [i1466, i1328, i902, RationalInterval.mul]) (by norm_num [i1466, i1328, i902, RationalInterval.mul])

def n1467 (b : ℝ) : ℝ := (n1465 b) + (n1466 b)
def i1467 : RationalInterval := ⟨(208879948844178480572018671679 / 62500000000000000000000000000 : ℚ), (3342079946903760743203561429183 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1467 (b : ℝ) (hb : rootInterval.Contains b) : i1467.Contains (n1467 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1465 b hb) (b1466 b hb))
    (by norm_num [i1467, i1465, i1466, RationalInterval.add]) (by norm_num [i1467, i1465, i1466, RationalInterval.add])

def n1468 (b : ℝ) : ℝ := (n1171 b) * (n57 b)
def i1468 : RationalInterval := ⟨(42517814455728581261905015239 / 62500000000000000000000000000 : ℚ), (6802850324207822387332479167 / 10000000000000000000000000000 : ℚ)⟩
theorem b1468 (b : ℝ) (hb : rootInterval.Contains b) : i1468.Contains (n1468 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1171 b hb) (b57 b hb))
    (by norm_num [i1468, i1171, i57, RationalInterval.mul]) (by norm_num [i1468, i1171, i57, RationalInterval.mul])

def n1469 (b : ℝ) : ℝ := (n1251 b) * (n57 b)
def i1469 : RationalInterval := ⟨(-47732189536902523313537250421 / 25000000000000000000000000000 : ℚ), (-477321832476378415177452946877 / 250000000000000000000000000000 : ℚ)⟩
theorem b1469 (b : ℝ) (hb : rootInterval.Contains b) : i1469.Contains (n1469 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1251 b hb) (b57 b hb))
    (by norm_num [i1469, i1251, i57, RationalInterval.mul]) (by norm_num [i1469, i1251, i57, RationalInterval.mul])

def n1470 (b : ℝ) : ℝ := (n1468 b) + (n1469 b)
def i1470 : RationalInterval := ⟨(-153625318773055454043876221627 / 125000000000000000000000000000 : ℚ), (-153625287185591427747070483851 / 125000000000000000000000000000 : ℚ)⟩
theorem b1470 (b : ℝ) (hb : rootInterval.Contains b) : i1470.Contains (n1470 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1468 b hb) (b1469 b hb))
    (by norm_num [i1470, i1468, i1469, RationalInterval.add]) (by norm_num [i1470, i1468, i1469, RationalInterval.add])

def n1471 (b : ℝ) : ℝ := (n1328 b) * (n57 b)
def i1471 : RationalInterval := ⟨(987493609252820030056453063659 / 125000000000000000000000000000 : ℚ), (1974987391252914260234818881977 / 250000000000000000000000000000 : ℚ)⟩
theorem b1471 (b : ℝ) (hb : rootInterval.Contains b) : i1471.Contains (n1471 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1328 b hb) (b57 b hb))
    (by norm_num [i1471, i1328, i57, RationalInterval.mul]) (by norm_num [i1471, i1328, i57, RationalInterval.mul])

def n1472 (b : ℝ) : ℝ := (n1470 b) + (n1471 b)
def i1472 : RationalInterval := ⟨(52116768154985286000786052627 / 7812500000000000000000000000 : ℚ), (66709472675269256189627116571 / 10000000000000000000000000000 : ℚ)⟩
theorem b1472 (b : ℝ) (hb : rootInterval.Contains b) : i1472.Contains (n1472 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1470 b hb) (b1471 b hb))
    (by norm_num [i1472, i1470, i1471, RationalInterval.add]) (by norm_num [i1472, i1470, i1471, RationalInterval.add])

def n1473 (b : ℝ) : ℝ := (n90 b) * (n210 b)
def i1473 : RationalInterval := ⟨(-27216863802369226776513811213 / 100000000000000000000000000000 : ℚ), (-272168633940719944738194660079 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1473 (b : ℝ) (hb : rootInterval.Contains b) : i1473.Contains (n1473 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b90 b hb) (b210 b hb))
    (by norm_num [i1473, i90, i210, RationalInterval.mul]) (by norm_num [i1473, i90, i210, RationalInterval.mul])

def n1474 (b : ℝ) : ℝ := (n91 b) * (n212 b)
def i1474 : RationalInterval := ⟨(-565120457390472950167960001603 / 1000000000000000000000000000000 : ℚ), (-565120450065367629640760001063 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1474 (b : ℝ) (hb : rootInterval.Contains b) : i1474.Contains (n1474 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b91 b hb) (b212 b hb))
    (by norm_num [i1474, i91, i212, RationalInterval.mul]) (by norm_num [i1474, i91, i212, RationalInterval.mul])

def n1475 (b : ℝ) : ℝ := (n1473 b) + (n1474 b)
def i1475 : RationalInterval := ⟨(-837289095414165217933098113733 / 1000000000000000000000000000000 : ℚ), (-418644542003043787189477330571 / 500000000000000000000000000000 : ℚ)⟩
theorem b1475 (b : ℝ) (hb : rootInterval.Contains b) : i1475.Contains (n1475 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1473 b hb) (b1474 b hb))
    (by norm_num [i1475, i1473, i1474, RationalInterval.add]) (by norm_num [i1475, i1473, i1474, RationalInterval.add])

def n1476 (b : ℝ) : ℝ := (n92 b) * (n210 b)
def i1476 : RationalInterval := ⟨(-159928828073880960055562788139 / 1000000000000000000000000000000 : ℚ), (-19991103206937199708342431869 / 125000000000000000000000000000 : ℚ)⟩
theorem b1476 (b : ℝ) (hb : rootInterval.Contains b) : i1476.Contains (n1476 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b92 b hb) (b210 b hb))
    (by norm_num [i1476, i92, i210, RationalInterval.mul]) (by norm_num [i1476, i92, i210, RationalInterval.mul])

def n1477 (b : ℝ) : ℝ := (n93 b) * (n212 b)
def i1477 : RationalInterval := ⟨(-86220710017732020211425845663 / 200000000000000000000000000000 : ℚ), (-215551772308154158350648561949 / 500000000000000000000000000000 : ℚ)⟩
theorem b1477 (b : ℝ) (hb : rootInterval.Contains b) : i1477.Contains (n1477 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b93 b hb) (b212 b hb))
    (by norm_num [i1477, i93, i212, RationalInterval.mul]) (by norm_num [i1477, i93, i212, RationalInterval.mul])

def n1478 (b : ℝ) : ℝ := (n1476 b) + (n1477 b)
def i1478 : RationalInterval := ⟨(-295516189081270530556346008227 / 500000000000000000000000000000 : ℚ), (-11820647405436118287360731577 / 20000000000000000000000000000 : ℚ)⟩
theorem b1478 (b : ℝ) (hb : rootInterval.Contains b) : i1478.Contains (n1478 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1476 b hb) (b1477 b hb))
    (by norm_num [i1478, i1476, i1477, RationalInterval.add]) (by norm_num [i1478, i1476, i1477, RationalInterval.add])

def n1479 (b : ℝ) : ℝ := -(n1475 b)
def i1479 : RationalInterval := ⟨(418644542003043787189477330571 / 500000000000000000000000000000 : ℚ), (837289095414165217933098113733 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1479 (b : ℝ) (hb : rootInterval.Contains b) : i1479.Contains (n1479 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b1475 b hb))
    (by norm_num [i1479, i1475, RationalInterval.neg]) (by norm_num [i1479, i1475, RationalInterval.neg])

def n1480 (b : ℝ) : ℝ := -(n1478 b)
def i1480 : RationalInterval := ⟨(11820647405436118287360731577 / 20000000000000000000000000000 : ℚ), (295516189081270530556346008227 / 500000000000000000000000000000 : ℚ)⟩
theorem b1480 (b : ℝ) (hb : rootInterval.Contains b) : i1480.Contains (n1480 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b1478 b hb))
    (by norm_num [i1480, i1478, RationalInterval.neg]) (by norm_num [i1480, i1478, RationalInterval.neg])

def n1481 (b : ℝ) : ℝ := (n1479 b) + (n15 b)
def i1481 : RationalInterval := ⟨(918644542003043787189477330571 / 500000000000000000000000000000 : ℚ), (1837289095414165217933098113733 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1481 (b : ℝ) (hb : rootInterval.Contains b) : i1481.Contains (n1481 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1479 b hb) (b15 b hb))
    (by norm_num [i1481, i1479, i15, RationalInterval.add]) (by norm_num [i1481, i1479, i15, RationalInterval.add])

def n1482 (b : ℝ) : ℝ := (n224 b) * (n1481 b)
def i1482 : RationalInterval := ⟨(345793320111149897025798401089 / 1000000000000000000000000000000 : ℚ), (86448331067760748398786621409 / 250000000000000000000000000000 : ℚ)⟩
theorem b1482 (b : ℝ) (hb : rootInterval.Contains b) : i1482.Contains (n1482 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b224 b hb) (b1481 b hb))
    (by norm_num [i1482, i224, i1481, RationalInterval.mul]) (by norm_num [i1482, i224, i1481, RationalInterval.mul])

def n1483 (b : ℝ) : ℝ := (n225 b) * (n1480 b)
def i1483 : RationalInterval := ⟨(217523605488642230079085131 / 7812500000000000000000000000 : ℚ), (27843022151408912523603928637 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1483 (b : ℝ) (hb : rootInterval.Contains b) : i1483.Contains (n1483 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b225 b hb) (b1480 b hb))
    (by norm_num [i1483, i225, i1480, RationalInterval.mul]) (by norm_num [i1483, i225, i1480, RationalInterval.mul])

def n1484 (b : ℝ) : ℝ := (n1482 b) + (n1483 b)
def i1484 : RationalInterval := ⟨(373636341613696102475921297857 / 1000000000000000000000000000000 : ℚ), (373636346422451906118750414273 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1484 (b : ℝ) (hb : rootInterval.Contains b) : i1484.Contains (n1484 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1482 b hb) (b1483 b hb))
    (by norm_num [i1484, i1482, i1483, RationalInterval.add]) (by norm_num [i1484, i1482, i1483, RationalInterval.add])

def n1485 (b : ℝ) : ℝ := (n226 b) * (n1481 b)
def i1485 : RationalInterval := ⟨(86553092597702009906096946083 / 1000000000000000000000000000000 : ℚ), (43276546998318773546007608669 / 500000000000000000000000000000 : ℚ)⟩
theorem b1485 (b : ℝ) (hb : rootInterval.Contains b) : i1485.Contains (n1485 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b226 b hb) (b1481 b hb))
    (by norm_num [i1485, i226, i1481, RationalInterval.mul]) (by norm_num [i1485, i226, i1481, RationalInterval.mul])

def n1486 (b : ℝ) : ℝ := (n227 b) * (n1480 b)
def i1486 : RationalInterval := ⟨(6969190780015834403492893471 / 1000000000000000000000000000000 : ℚ), (6969190971229989979548406629 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1486 (b : ℝ) (hb : rootInterval.Contains b) : i1486.Contains (n1486 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b227 b hb) (b1480 b hb))
    (by norm_num [i1486, i227, i1480, RationalInterval.mul]) (by norm_num [i1486, i227, i1480, RationalInterval.mul])

def n1487 (b : ℝ) : ℝ := (n1485 b) + (n1486 b)
def i1487 : RationalInterval := ⟨(46761141688858922154794919777 / 500000000000000000000000000000 : ℚ), (93522284967867537071563623967 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1487 (b : ℝ) (hb : rootInterval.Contains b) : i1487.Contains (n1487 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1485 b hb) (b1486 b hb))
    (by norm_num [i1487, i1485, i1486, RationalInterval.add]) (by norm_num [i1487, i1485, i1486, RationalInterval.add])

def n1488 (b : ℝ) : ℝ := -(n210 b)
def i1488 : RationalInterval := ⟨(304015598171090167181267651997 / 1000000000000000000000000000000 : ℚ), (304015602318281222815061084761 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1488 (b : ℝ) (hb : rootInterval.Contains b) : i1488.Contains (n1488 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b210 b hb))
    (by norm_num [i1488, i210, RationalInterval.neg]) (by norm_num [i1488, i210, RationalInterval.neg])

def n1489 (b : ℝ) : ℝ := -(n212 b)
def i1489 : RationalInterval := ⟨(1074261822854187343377343754867 / 1000000000000000000000000000000 : ℚ), (134282729226210685066719959941 / 125000000000000000000000000000 : ℚ)⟩
theorem b1489 (b : ℝ) (hb : rootInterval.Contains b) : i1489.Contains (n1489 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b212 b hb))
    (by norm_num [i1489, i212, RationalInterval.neg]) (by norm_num [i1489, i212, RationalInterval.neg])

def n1490 (b : ℝ) : ℝ := (n1484 b) + (n1488 b)
def i1490 : RationalInterval := ⟨(338825969892393134828594474927 / 500000000000000000000000000000 : ℚ), (338825974370366564466905749517 / 500000000000000000000000000000 : ℚ)⟩
theorem b1490 (b : ℝ) (hb : rootInterval.Contains b) : i1490.Contains (n1490 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1484 b hb) (b1488 b hb))
    (by norm_num [i1490, i1484, i1488, RationalInterval.add]) (by norm_num [i1490, i1484, i1488, RationalInterval.add])

def n1491 (b : ℝ) : ℝ := (n1487 b) + (n1489 b)
def i1491 : RationalInterval := ⟨(1167784106231905187686933594421 / 1000000000000000000000000000000 : ℚ), (233556823755510603521064660699 / 200000000000000000000000000000 : ℚ)⟩
theorem b1491 (b : ℝ) (hb : rootInterval.Contains b) : i1491.Contains (n1491 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1487 b hb) (b1489 b hb))
    (by norm_num [i1491, i1487, i1489, RationalInterval.add]) (by norm_num [i1491, i1487, i1489, RationalInterval.add])

def n1492 (b : ℝ) : ℝ := (n1479 b) * (n325 b)
def i1492 : RationalInterval := ⟨(-49510492654963636863884563959 / 1000000000000000000000000000000 : ℚ), (-49510491396636409371391364949 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1492 (b : ℝ) (hb : rootInterval.Contains b) : i1492.Contains (n1492 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1479 b hb) (b325 b hb))
    (by norm_num [i1492, i1479, i325, RationalInterval.mul]) (by norm_num [i1492, i1479, i325, RationalInterval.mul])

def n1493 (b : ℝ) : ℝ := (n1480 b) * (n326 b)
def i1493 : RationalInterval := ⟨(142227588042165625919320670417 / 250000000000000000000000000000 : ℚ), (142227590079464062576755184337 / 250000000000000000000000000000 : ℚ)⟩
theorem b1493 (b : ℝ) (hb : rootInterval.Contains b) : i1493.Contains (n1493 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1480 b hb) (b326 b hb))
    (by norm_num [i1493, i1480, i326, RationalInterval.mul]) (by norm_num [i1493, i1480, i326, RationalInterval.mul])

def n1494 (b : ℝ) : ℝ := (n1492 b) + (n1493 b)
def i1494 : RationalInterval := ⟨(519399859513698866813398117709 / 1000000000000000000000000000000 : ℚ), (519399868921219840935629372399 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1494 (b : ℝ) (hb : rootInterval.Contains b) : i1494.Contains (n1494 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1492 b hb) (b1493 b hb))
    (by norm_num [i1494, i1492, i1493, RationalInterval.add]) (by norm_num [i1494, i1492, i1493, RationalInterval.add])

def n1495 (b : ℝ) : ℝ := (n310 b) * (n1490 b)
def i1495 : RationalInterval := ⟨(302149996282501918436319117309 / 500000000000000000000000000000 : ℚ), (604300001920996377627545596617 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1495 (b : ℝ) (hb : rootInterval.Contains b) : i1495.Contains (n1495 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b310 b hb) (b1490 b hb))
    (by norm_num [i1495, i310, i1490, RationalInterval.mul]) (by norm_num [i1495, i310, i1490, RationalInterval.mul])

def n1496 (b : ℝ) : ℝ := (n311 b) * (n1491 b)
def i1496 : RationalInterval := ⟨(75396268943897357572160738721 / 125000000000000000000000000000 : ℚ), (120634031913849991140575839 / 200000000000000000000000000 : ℚ)⟩
theorem b1496 (b : ℝ) (hb : rootInterval.Contains b) : i1496.Contains (n1496 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b311 b hb) (b1491 b hb))
    (by norm_num [i1496, i311, i1491, RationalInterval.mul]) (by norm_num [i1496, i311, i1491, RationalInterval.mul])

def n1497 (b : ℝ) : ℝ := (n1495 b) + (n1496 b)
def i1497 : RationalInterval := ⟨(603735072058091348724962072193 / 500000000000000000000000000000 : ℚ), (1207470161490246333330424791617 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1497 (b : ℝ) (hb : rootInterval.Contains b) : i1497.Contains (n1497 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1495 b hb) (b1496 b hb))
    (by norm_num [i1497, i1495, i1496, RationalInterval.add]) (by norm_num [i1497, i1495, i1496, RationalInterval.add])

def n1498 (b : ℝ) : ℝ := (n1494 b) + (n1497 b)
def i1498 : RationalInterval := ⟨(345374000725976312852664452419 / 200000000000000000000000000000 : ℚ), (107929376900716635891628385251 / 62500000000000000000000000000 : ℚ)⟩
theorem b1498 (b : ℝ) (hb : rootInterval.Contains b) : i1498.Contains (n1498 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1494 b hb) (b1497 b hb))
    (by norm_num [i1498, i1494, i1497, RationalInterval.add]) (by norm_num [i1498, i1494, i1497, RationalInterval.add])

def n1499 (b : ℝ) : ℝ := (n90 b) * (n325 b)
def i1499 : RationalInterval := ⟨(-26468786111444795580124683479 / 500000000000000000000000000000 : ℚ), (-13234392881682194794632004151 / 250000000000000000000000000000 : ℚ)⟩
theorem b1499 (b : ℝ) (hb : rootInterval.Contains b) : i1499.Contains (n1499 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b90 b hb) (b325 b hb))
    (by norm_num [i1499, i90, i325, RationalInterval.mul]) (by norm_num [i1499, i90, i325, RationalInterval.mul])

def n1500 (b : ℝ) : ℝ := (n91 b) * (n326 b)
def i1500 : RationalInterval := ⟨(50636473286071306602887585979 / 100000000000000000000000000000 : ℚ), (506364734753154368524764675003 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1500 (b : ℝ) (hb : rootInterval.Contains b) : i1500.Contains (n1500 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b91 b hb) (b326 b hb))
    (by norm_num [i1500, i91, i326, RationalInterval.mul]) (by norm_num [i1500, i91, i326, RationalInterval.mul])

def n1501 (b : ℝ) : ℝ := (n1499 b) + (n1500 b)
def i1501 : RationalInterval := ⟨(14169598769931983589644577901 / 31250000000000000000000000000 : ℚ), (453427163226425589346236658399 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1501 (b : ℝ) (hb : rootInterval.Contains b) : i1501.Contains (n1501 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1499 b hb) (b1500 b hb))
    (by norm_num [i1501, i1499, i1500, RationalInterval.add]) (by norm_num [i1501, i1499, i1500, RationalInterval.add])

def n1502 (b : ℝ) : ℝ := (n92 b) * (n325 b)
def i1502 : RationalInterval := ⟨(-7776652692388991926098928991 / 250000000000000000000000000000 : ℚ), (-15553305178376363329846639289 / 500000000000000000000000000000 : ℚ)⟩
theorem b1502 (b : ℝ) (hb : rootInterval.Contains b) : i1502.Contains (n1502 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b92 b hb) (b325 b hb))
    (by norm_num [i1502, i92, i325, RationalInterval.mul]) (by norm_num [i1502, i92, i325, RationalInterval.mul])

def n1503 (b : ℝ) : ℝ := (n93 b) * (n326 b)
def i1503 : RationalInterval := ⟨(9657039980578173412561189603 / 25000000000000000000000000000 : ℚ), (38628160056317878854721671497 / 100000000000000000000000000000 : ℚ)⟩
theorem b1503 (b : ℝ) (hb : rootInterval.Contains b) : i1503.Contains (n1503 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b93 b hb) (b326 b hb))
    (by norm_num [i1503, i93, i326, RationalInterval.mul]) (by norm_num [i1503, i93, i326, RationalInterval.mul])

def n1504 (b : ℝ) : ℝ := (n1502 b) + (n1503 b)
def i1504 : RationalInterval := ⟨(88793747113392742199512967039 / 250000000000000000000000000000 : ℚ), (44396873775803257735940429549 / 125000000000000000000000000000 : ℚ)⟩
theorem b1504 (b : ℝ) (hb : rootInterval.Contains b) : i1504.Contains (n1504 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1502 b hb) (b1503 b hb))
    (by norm_num [i1504, i1502, i1503, RationalInterval.add]) (by norm_num [i1504, i1502, i1503, RationalInterval.add])

def n1505 (b : ℝ) : ℝ := (n325 b) * (n1501 b)
def i1505 : RationalInterval := ⟨(-13406004185076804875696689467 / 500000000000000000000000000000 : ℚ), (-26812007900961735488930628759 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1505 (b : ℝ) (hb : rootInterval.Contains b) : i1505.Contains (n1505 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b325 b hb) (b1501 b hb))
    (by norm_num [i1505, i325, i1501, RationalInterval.mul]) (by norm_num [i1505, i325, i1501, RationalInterval.mul])

def n1506 (b : ℝ) : ℝ := (n326 b) * (n1504 b)
def i1506 : RationalInterval := ⟨(341880983049534875914136329209 / 1000000000000000000000000000000 : ℚ), (68376197013916966046214782599 / 200000000000000000000000000000 : ℚ)⟩
theorem b1506 (b : ℝ) (hb : rootInterval.Contains b) : i1506.Contains (n1506 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b326 b hb) (b1504 b hb))
    (by norm_num [i1506, i326, i1504, RationalInterval.mul]) (by norm_num [i1506, i326, i1504, RationalInterval.mul])

def n1507 (b : ℝ) : ℝ := (n1505 b) + (n1506 b)
def i1507 : RationalInterval := ⟨(12602758987175250646509718011 / 40000000000000000000000000000 : ℚ), (78767244292155773685535821059 / 250000000000000000000000000000 : ℚ)⟩
theorem b1507 (b : ℝ) (hb : rootInterval.Contains b) : i1507.Contains (n1507 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1505 b hb) (b1506 b hb))
    (by norm_num [i1507, i1505, i1506, RationalInterval.add]) (by norm_num [i1507, i1505, i1506, RationalInterval.add])

def n1508 (b : ℝ) : ℝ := (n1501 b) * (n310 b)
def i1508 : RationalInterval := ⟨(202173131747566747894298377819 / 500000000000000000000000000000 : ℚ), (80869253343974227429716642533 / 200000000000000000000000000000 : ℚ)⟩
theorem b1508 (b : ℝ) (hb : rootInterval.Contains b) : i1508.Contains (n1508 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1501 b hb) (b310 b hb))
    (by norm_num [i1508, i1501, i310, RationalInterval.mul]) (by norm_num [i1508, i1501, i310, RationalInterval.mul])

def n1509 (b : ℝ) : ℝ := (n1501 b) * (n311 b)
def i1509 : RationalInterval := ⟨(117099439759383389095438894303 / 500000000000000000000000000000 : ℚ), (234198881453030192105394091397 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1509 (b : ℝ) (hb : rootInterval.Contains b) : i1509.Contains (n1509 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1501 b hb) (b311 b hb))
    (by norm_num [i1509, i1501, i311, RationalInterval.mul]) (by norm_num [i1509, i1501, i311, RationalInterval.mul])

def n1510 (b : ℝ) : ℝ := (n1504 b) * (n310 b)
def i1510 : RationalInterval := ⟨(316729327078931936715451347281 / 1000000000000000000000000000000 : ℚ), (158364664679914143511958535919 / 500000000000000000000000000000 : ℚ)⟩
theorem b1510 (b : ℝ) (hb : rootInterval.Contains b) : i1510.Contains (n1510 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1504 b hb) (b310 b hb))
    (by norm_num [i1510, i1504, i310, RationalInterval.mul]) (by norm_num [i1510, i1504, i310, RationalInterval.mul])

def n1511 (b : ℝ) : ℝ := (n1504 b) * (n311 b)
def i1511 : RationalInterval := ⟨(183450819778656420922752319713 / 1000000000000000000000000000000 : ℚ), (11465676321989830874472167357 / 62500000000000000000000000000 : ℚ)⟩
theorem b1511 (b : ℝ) (hb : rootInterval.Contains b) : i1511.Contains (n1511 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1504 b hb) (b311 b hb))
    (by norm_num [i1511, i1504, i311, RationalInterval.mul]) (by norm_num [i1511, i1504, i311, RationalInterval.mul])

def n1512 (b : ℝ) : ℝ := (n310 b) * (n1501 b)
def i1512 : RationalInterval := ⟨(202173131747566747894298377819 / 500000000000000000000000000000 : ℚ), (80869253343974227429716642533 / 200000000000000000000000000000 : ℚ)⟩
theorem b1512 (b : ℝ) (hb : rootInterval.Contains b) : i1512.Contains (n1512 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b310 b hb) (b1501 b hb))
    (by norm_num [i1512, i310, i1501, RationalInterval.mul]) (by norm_num [i1512, i310, i1501, RationalInterval.mul])

def n1513 (b : ℝ) : ℝ := (n310 b) * (n1504 b)
def i1513 : RationalInterval := ⟨(316729327078931936715451347281 / 1000000000000000000000000000000 : ℚ), (158364664679914143511958535919 / 500000000000000000000000000000 : ℚ)⟩
theorem b1513 (b : ℝ) (hb : rootInterval.Contains b) : i1513.Contains (n1513 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b310 b hb) (b1504 b hb))
    (by norm_num [i1513, i310, i1504, RationalInterval.mul]) (by norm_num [i1513, i310, i1504, RationalInterval.mul])

def n1514 (b : ℝ) : ℝ := (n311 b) * (n1501 b)
def i1514 : RationalInterval := ⟨(117099439759383389095438894303 / 500000000000000000000000000000 : ℚ), (234198881453030192105394091397 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1514 (b : ℝ) (hb : rootInterval.Contains b) : i1514.Contains (n1514 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b311 b hb) (b1501 b hb))
    (by norm_num [i1514, i311, i1501, RationalInterval.mul]) (by norm_num [i1514, i311, i1501, RationalInterval.mul])

def n1515 (b : ℝ) : ℝ := (n311 b) * (n1504 b)
def i1515 : RationalInterval := ⟨(183450819778656420922752319713 / 1000000000000000000000000000000 : ℚ), (11465676321989830874472167357 / 62500000000000000000000000000 : ℚ)⟩
theorem b1515 (b : ℝ) (hb : rootInterval.Contains b) : i1515.Contains (n1515 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b311 b hb) (b1504 b hb))
    (by norm_num [i1515, i311, i1504, RationalInterval.mul]) (by norm_num [i1515, i311, i1504, RationalInterval.mul])

def n1516 (b : ℝ) : ℝ := (n1508 b) + (n1512 b)
def i1516 : RationalInterval := ⟨(202173131747566747894298377819 / 250000000000000000000000000000 : ℚ), (80869253343974227429716642533 / 100000000000000000000000000000 : ℚ)⟩
theorem b1516 (b : ℝ) (hb : rootInterval.Contains b) : i1516.Contains (n1516 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1508 b hb) (b1512 b hb))
    (by norm_num [i1516, i1508, i1512, RationalInterval.add]) (by norm_num [i1516, i1508, i1512, RationalInterval.add])

def n1517 (b : ℝ) : ℝ := (n1509 b) + (n1513 b)
def i1517 : RationalInterval := ⟨(550928206597698714906329135887 / 1000000000000000000000000000000 : ℚ), (110185642162571695825862232647 / 200000000000000000000000000000 : ℚ)⟩
theorem b1517 (b : ℝ) (hb : rootInterval.Contains b) : i1517.Contains (n1517 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1509 b hb) (b1513 b hb))
    (by norm_num [i1517, i1509, i1513, RationalInterval.add]) (by norm_num [i1517, i1509, i1513, RationalInterval.add])

def n1518 (b : ℝ) : ℝ := (n1510 b) + (n1514 b)
def i1518 : RationalInterval := ⟨(550928206597698714906329135887 / 1000000000000000000000000000000 : ℚ), (110185642162571695825862232647 / 200000000000000000000000000000 : ℚ)⟩
theorem b1518 (b : ℝ) (hb : rootInterval.Contains b) : i1518.Contains (n1518 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1510 b hb) (b1514 b hb))
    (by norm_num [i1518, i1510, i1514, RationalInterval.add]) (by norm_num [i1518, i1510, i1514, RationalInterval.add])

def n1519 (b : ℝ) : ℝ := (n1511 b) + (n1515 b)
def i1519 : RationalInterval := ⟨(183450819778656420922752319713 / 500000000000000000000000000000 : ℚ), (11465676321989830874472167357 / 31250000000000000000000000000 : ℚ)⟩
theorem b1519 (b : ℝ) (hb : rootInterval.Contains b) : i1519.Contains (n1519 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1511 b hb) (b1515 b hb))
    (by norm_num [i1519, i1511, i1515, RationalInterval.add]) (by norm_num [i1519, i1511, i1515, RationalInterval.add])

def n1520 (b : ℝ) : ℝ := (n310 b) * (n310 b)
def i1520 : RationalInterval := ⟨(99403532720640718924569358579 / 125000000000000000000000000000 : ℚ), (397614132684723708055411476539 / 500000000000000000000000000000 : ℚ)⟩
theorem b1520 (b : ℝ) (hb : rootInterval.Contains b) : i1520.Contains (n1520 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b310 b hb) (b310 b hb))
    (by norm_num [i1520, i310, i310, RationalInterval.mul]) (by norm_num [i1520, i310, i310, RationalInterval.mul])

def n1521 (b : ℝ) : ℝ := (n310 b) * (n311 b)
def i1521 : RationalInterval := ⟨(460599205881595894921689815437 / 1000000000000000000000000000000 : ℚ), (115149802024996302652132633149 / 250000000000000000000000000000 : ℚ)⟩
theorem b1521 (b : ℝ) (hb : rootInterval.Contains b) : i1521.Contains (n1521 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b310 b hb) (b311 b hb))
    (by norm_num [i1521, i310, i311, RationalInterval.mul]) (by norm_num [i1521, i310, i311, RationalInterval.mul])

def n1522 (b : ℝ) : ℝ := (n311 b) * (n310 b)
def i1522 : RationalInterval := ⟨(460599205881595894921689815437 / 1000000000000000000000000000000 : ℚ), (115149802024996302652132633149 / 250000000000000000000000000000 : ℚ)⟩
theorem b1522 (b : ℝ) (hb : rootInterval.Contains b) : i1522.Contains (n1522 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b311 b hb) (b310 b hb))
    (by norm_num [i1522, i311, i310, RationalInterval.mul]) (by norm_num [i1522, i311, i310, RationalInterval.mul])

def n1523 (b : ℝ) : ℝ := (n311 b) * (n311 b)
def i1523 : RationalInterval := ⟨(266780795727575262384151129901 / 1000000000000000000000000000000 : ℚ), (266780797088207126910633492369 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1523 (b : ℝ) (hb : rootInterval.Contains b) : i1523.Contains (n1523 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b311 b hb) (b311 b hb))
    (by norm_num [i1523, i311, i311, RationalInterval.mul]) (by norm_num [i1523, i311, i311, RationalInterval.mul])

def n1524 (b : ℝ) : ℝ := (n90 b) * (n1490 b)
def i1524 : RationalInterval := ⟨(75833116724947564865182569711 / 125000000000000000000000000000 : ℚ), (606664942642569385176557761917 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1524 (b : ℝ) (hb : rootInterval.Contains b) : i1524.Contains (n1524 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b90 b hb) (b1490 b hb))
    (by norm_num [i1524, i90, i1490, RationalInterval.mul]) (by norm_num [i1524, i90, i1490, RationalInterval.mul])

def n1525 (b : ℝ) : ℝ := (n91 b) * (n1491 b)
def i1525 : RationalInterval := ⟨(614318284102825018660662292373 / 1000000000000000000000000000000 : ℚ), (614318292400411986791962688419 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1525 (b : ℝ) (hb : rootInterval.Contains b) : i1525.Contains (n1525 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b91 b hb) (b1491 b hb))
    (by norm_num [i1525, i91, i1491, RationalInterval.mul]) (by norm_num [i1525, i91, i1491, RationalInterval.mul])

def n1526 (b : ℝ) : ℝ := (n1524 b) + (n1525 b)
def i1526 : RationalInterval := ⟨(1220983217902405537582122850061 / 1000000000000000000000000000000 : ℚ), (38155726095093167874016264073 / 31250000000000000000000000000 : ℚ)⟩
theorem b1526 (b : ℝ) (hb : rootInterval.Contains b) : i1526.Contains (n1526 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1524 b hb) (b1525 b hb))
    (by norm_num [i1526, i1524, i1525, RationalInterval.add]) (by norm_num [i1526, i1524, i1525, RationalInterval.add])

def n1527 (b : ℝ) : ℝ := (n92 b) * (n1490 b)
def i1527 : RationalInterval := ⟨(356481968638860036234097395647 / 1000000000000000000000000000000 : ℚ), (178240986938929507917613580753 / 500000000000000000000000000000 : ℚ)⟩
theorem b1527 (b : ℝ) (hb : rootInterval.Contains b) : i1527.Contains (n1527 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b92 b hb) (b1490 b hb))
    (by norm_num [i1527, i92, i1490, RationalInterval.mul]) (by norm_num [i1527, i92, i1490, RationalInterval.mul])

def n1528 (b : ℝ) : ℝ := (n93 b) * (n1491 b)
def i1528 : RationalInterval := ⟨(234317117500085764406726788221 / 500000000000000000000000000000 : ℚ), (93726848240863507137650331713 / 200000000000000000000000000000 : ℚ)⟩
theorem b1528 (b : ℝ) (hb : rootInterval.Contains b) : i1528.Contains (n1528 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b93 b hb) (b1491 b hb))
    (by norm_num [i1528, i93, i1491, RationalInterval.mul]) (by norm_num [i1528, i93, i1491, RationalInterval.mul])

def n1529 (b : ℝ) : ℝ := (n1527 b) + (n1528 b)
def i1529 : RationalInterval := ⟨(825116203639031565047550972089 / 1000000000000000000000000000000 : ℚ), (825116215082176551523478820071 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1529 (b : ℝ) (hb : rootInterval.Contains b) : i1529.Contains (n1529 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1527 b hb) (b1528 b hb))
    (by norm_num [i1529, i1527, i1528, RationalInterval.add]) (by norm_num [i1529, i1527, i1528, RationalInterval.add])

