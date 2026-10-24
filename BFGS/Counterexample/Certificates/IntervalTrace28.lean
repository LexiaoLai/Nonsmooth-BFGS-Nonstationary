import BFGS.Counterexample.Certificates.IntervalTrace27

/-! Generated arithmetic proofs. Each bound is checked by the Lean kernel. -/
namespace BFGS.Counterexample.Trace
noncomputable section
open BFGS RationalInterval
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false

def n2520 (b : ℝ) : ℝ := (n231 b) * (n331 b)
def i2520 : RationalInterval := ⟨(242102267054965247380035233953 / 200000000000000000000000000000 : ℚ), (605255668351839013297557327473 / 500000000000000000000000000000 : ℚ)⟩
theorem b2520 (b : ℝ) (hb : rootInterval.Contains b) : i2520.Contains (n2520 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b231 b hb) (b331 b hb))
    (by norm_num [i2520, i231, i331, RationalInterval.mul]) (by norm_num [i2520, i231, i331, RationalInterval.mul])

def n2521 (b : ℝ) : ℝ := (n232 b) * (n330 b)
def i2521 : RationalInterval := ⟨(975838083043844191728422388623 / 1000000000000000000000000000000 : ℚ), (487919042168311511528815846989 / 500000000000000000000000000000 : ℚ)⟩
theorem b2521 (b : ℝ) (hb : rootInterval.Contains b) : i2521.Contains (n2521 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b232 b hb) (b330 b hb))
    (by norm_num [i2521, i232, i330, RationalInterval.mul]) (by norm_num [i2521, i232, i330, RationalInterval.mul])

def n2522 (b : ℝ) : ℝ := (n2520 b) + (n2521 b)
def i2522 : RationalInterval := ⟨(546587354579667607157149639597 / 250000000000000000000000000000 : ℚ), (546587355260075262413186587231 / 250000000000000000000000000000 : ℚ)⟩
theorem b2522 (b : ℝ) (hb : rootInterval.Contains b) : i2522.Contains (n2522 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2520 b hb) (b2521 b hb))
    (by norm_num [i2522, i2520, i2521, RationalInterval.add]) (by norm_num [i2522, i2520, i2521, RationalInterval.add])

def n2523 (b : ℝ) : ℝ := (n331 b) * (n332 b)
def i2523 : RationalInterval := ⟨(-548822874341172493229990624683 / 250000000000000000000000000000 : ℚ), (-548822874059838188173799177839 / 250000000000000000000000000000 : ℚ)⟩
theorem b2523 (b : ℝ) (hb : rootInterval.Contains b) : i2523.Contains (n2523 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b331 b hb) (b332 b hb))
    (by norm_num [i2523, i331, i332, RationalInterval.mul]) (by norm_num [i2523, i331, i332, RationalInterval.mul])

def n2524 (b : ℝ) : ℝ := (n330 b) * (n331 b)
def i2524 : RationalInterval := ⟨(-287852918941978528807080390421 / 250000000000000000000000000000 : ℚ), (-1151411675017940119540258522547 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2524 (b : ℝ) (hb : rootInterval.Contains b) : i2524.Contains (n2524 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b330 b hb) (b331 b hb))
    (by norm_num [i2524, i330, i331, RationalInterval.mul]) (by norm_num [i2524, i330, i331, RationalInterval.mul])

def n2525 (b : ℝ) : ℝ := (n2523 b) + (n2524 b)
def i2525 : RationalInterval := ⟨(-13073059270049234719329234611 / 3906250000000000000000000000 : ℚ), (-3346703171257292872235455233903 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2525 (b : ℝ) (hb : rootInterval.Contains b) : i2525.Contains (n2525 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2523 b hb) (b2524 b hb))
    (by norm_num [i2525, i2523, i2524, RationalInterval.add]) (by norm_num [i2525, i2523, i2524, RationalInterval.add])

def n2526 (b : ℝ) : ℝ := (n318 b) * (n2519 b)
def i2526 : RationalInterval := ⟨(-3580031471573393315426071882263 / 1000000000000000000000000000000 : ℚ), (-1790015721653540740809556426459 / 500000000000000000000000000000 : ℚ)⟩
theorem b2526 (b : ℝ) (hb : rootInterval.Contains b) : i2526.Contains (n2526 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b318 b hb) (b2519 b hb))
    (by norm_num [i2526, i318, i2519, RationalInterval.mul]) (by norm_num [i2526, i318, i2519, RationalInterval.mul])

def n2527 (b : ℝ) : ℝ := (n319 b) * (n2522 b)
def i2527 : RationalInterval := ⟨(1177281579951621792925541549617 / 1000000000000000000000000000000 : ℚ), (117728159342014590339673304627 / 100000000000000000000000000000 : ℚ)⟩
theorem b2527 (b : ℝ) (hb : rootInterval.Contains b) : i2527.Contains (n2527 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b319 b hb) (b2522 b hb))
    (by norm_num [i2527, i319, i2522, RationalInterval.mul]) (by norm_num [i2527, i319, i2522, RationalInterval.mul])

def n2528 (b : ℝ) : ℝ := (n2526 b) + (n2527 b)
def i2528 : RationalInterval := ⟨(-1201374945810885761250265166323 / 500000000000000000000000000000 : ℚ), (-300343731235866947277797475831 / 125000000000000000000000000000 : ℚ)⟩
theorem b2528 (b : ℝ) (hb : rootInterval.Contains b) : i2528.Contains (n2528 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2526 b hb) (b2527 b hb))
    (by norm_num [i2528, i2526, i2527, RationalInterval.add]) (by norm_num [i2528, i2526, i2527, RationalInterval.add])

def n2529 (b : ℝ) : ℝ := (n2525 b) + (n2528 b)
def i2529 : RationalInterval := ⟨(-2874726532377187805324407196531 / 500000000000000000000000000000 : ℚ), (-5749453021144228450457835040551 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2529 (b : ℝ) (hb : rootInterval.Contains b) : i2529.Contains (n2529 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2525 b hb) (b2528 b hb))
    (by norm_num [i2529, i2525, i2528, RationalInterval.add]) (by norm_num [i2529, i2525, i2528, RationalInterval.add])

def n2530 (b : ℝ) : ℝ := (n118 b) * (n2519 b)
def i2530 : RationalInterval := ⟨(-6113731069507881705388054966291 / 1000000000000000000000000000000 : ℚ), (-6113731054101043746122297414669 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2530 (b : ℝ) (hb : rootInterval.Contains b) : i2530.Contains (n2530 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b118 b hb) (b2519 b hb))
    (by norm_num [i2530, i118, i2519, RationalInterval.mul]) (by norm_num [i2530, i118, i2519, RationalInterval.mul])

def n2531 (b : ℝ) : ℝ := (n119 b) * (n2522 b)
def i2531 : RationalInterval := ⟨(2312036198881855244400958467557 / 1000000000000000000000000000000 : ℚ), (231203621011642460747248146119 / 100000000000000000000000000000 : ℚ)⟩
theorem b2531 (b : ℝ) (hb : rootInterval.Contains b) : i2531.Contains (n2531 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b119 b hb) (b2522 b hb))
    (by norm_num [i2531, i119, i2522, RationalInterval.mul]) (by norm_num [i2531, i119, i2522, RationalInterval.mul])

def n2532 (b : ℝ) : ℝ := (n2530 b) + (n2531 b)
def i2532 : RationalInterval := ⟨(-1900847435313013230493548249367 / 500000000000000000000000000000 : ℚ), (-3801694843984619138649815953479 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2532 (b : ℝ) (hb : rootInterval.Contains b) : i2532.Contains (n2532 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2530 b hb) (b2531 b hb))
    (by norm_num [i2532, i2530, i2531, RationalInterval.add]) (by norm_num [i2532, i2530, i2531, RationalInterval.add])

def n2533 (b : ℝ) : ℝ := (n120 b) * (n2519 b)
def i2533 : RationalInterval := ⟨(-47351678524601900446591194933 / 15625000000000000000000000000 : ℚ), (-3030507416732059835442785516501 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2533 (b : ℝ) (hb : rootInterval.Contains b) : i2533.Contains (n2533 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b120 b hb) (b2519 b hb))
    (by norm_num [i2533, i120, i2519, RationalInterval.mul]) (by norm_num [i2533, i120, i2519, RationalInterval.mul])

def n2534 (b : ℝ) : ℝ := (n121 b) * (n2522 b)
def i2534 : RationalInterval := ⟨(1315210245238892630566549726229 / 1000000000000000000000000000000 : ℚ), (263042050516647955694496389219 / 200000000000000000000000000000 : ℚ)⟩
theorem b2534 (b : ℝ) (hb : rootInterval.Contains b) : i2534.Contains (n2534 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b121 b hb) (b2522 b hb))
    (by norm_num [i2534, i121, i2522, RationalInterval.mul]) (by norm_num [i2534, i121, i2522, RationalInterval.mul])

def n2535 (b : ℝ) : ℝ := (n2533 b) + (n2534 b)
def i2535 : RationalInterval := ⟨(-1715297180335628998015286749483 / 1000000000000000000000000000000 : ℚ), (-857648582074410028485151785203 / 500000000000000000000000000000 : ℚ)⟩
theorem b2535 (b : ℝ) (hb : rootInterval.Contains b) : i2535.Contains (n2535 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2533 b hb) (b2534 b hb))
    (by norm_num [i2535, i2533, i2534, RationalInterval.add]) (by norm_num [i2535, i2533, i2534, RationalInterval.add])

def n2536 (b : ℝ) : ℝ := (n331 b) + (n2532 b)
def i2536 : RationalInterval := ⟨(-2422787346111401159339368717891 / 500000000000000000000000000000 : ℚ), (-302848416575376985737797133893 / 62500000000000000000000000000 : ℚ)⟩
theorem b2536 (b : ℝ) (hb : rootInterval.Contains b) : i2536.Contains (n2536 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b331 b hb) (b2532 b hb))
    (by norm_num [i2536, i331, i2532, RationalInterval.add]) (by norm_num [i2536, i331, i2532, RationalInterval.add])

def n2537 (b : ℝ) : ℝ := (n332 b) + (n2535 b)
def i2537 : RationalInterval := ⟨(193857268845106965757123085693 / 500000000000000000000000000000 : ℚ), (387714554198845321425264508201 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2537 (b : ℝ) (hb : rootInterval.Contains b) : i2537.Contains (n2537 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b332 b hb) (b2535 b hb))
    (by norm_num [i2537, i332, i2535, RationalInterval.add]) (by norm_num [i2537, i332, i2535, RationalInterval.add])

def n2538 (b : ℝ) : ℝ := (n2519 b) * (n2210 b)
def i2538 : RationalInterval := ⟨(-9693762541081275020814126848553 / 1000000000000000000000000000000 : ℚ), (-2423440624352031306935352566897 / 250000000000000000000000000000 : ℚ)⟩
theorem b2538 (b : ℝ) (hb : rootInterval.Contains b) : i2538.Contains (n2538 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2519 b hb) (b2210 b hb))
    (by norm_num [i2538, i2519, i2210, RationalInterval.mul]) (by norm_num [i2538, i2519, i2210, RationalInterval.mul])

def n2539 (b : ℝ) : ℝ := (n2522 b) * (n2213 b)
def i2539 : RationalInterval := ⟨(3489317780832365990977711064831 / 1000000000000000000000000000000 : ℚ), (697863560307536310923244300521 / 200000000000000000000000000000 : ℚ)⟩
theorem b2539 (b : ℝ) (hb : rootInterval.Contains b) : i2539.Contains (n2539 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2522 b hb) (b2213 b hb))
    (by norm_num [i2539, i2522, i2213, RationalInterval.mul]) (by norm_num [i2539, i2522, i2213, RationalInterval.mul])

def n2540 (b : ℝ) : ℝ := (n2538 b) + (n2539 b)
def i2540 : RationalInterval := ⟨(-3102222380124454514918207891861 / 500000000000000000000000000000 : ℚ), (-6204444695870443673125188764983 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2540 (b : ℝ) (hb : rootInterval.Contains b) : i2540.Contains (n2540 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2538 b hb) (b2539 b hb))
    (by norm_num [i2540, i2538, i2539, RationalInterval.add]) (by norm_num [i2540, i2538, i2539, RationalInterval.add])

def n2541 (b : ℝ) : ℝ := (n2540 b) * (n13 b)
def i2541 : RationalInterval := ⟨(-3102222380124454514918207891861 / 250000000000000000000000000000 : ℚ), (-6204444695870443673125188764983 / 500000000000000000000000000000 : ℚ)⟩
theorem b2541 (b : ℝ) (hb : rootInterval.Contains b) : i2541.Contains (n2541 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2540 b hb) (b13 b hb))
    (by norm_num [i2541, i2540, i13, RationalInterval.mul]) (by norm_num [i2541, i2540, i13, RationalInterval.mul])

def n2542 (b : ℝ) : ℝ := (n332 b) * (n331 b)
def i2542 : RationalInterval := ⟨(-548822874341172493229990624683 / 250000000000000000000000000000 : ℚ), (-548822874059838188173799177839 / 250000000000000000000000000000 : ℚ)⟩
theorem b2542 (b : ℝ) (hb : rootInterval.Contains b) : i2542.Contains (n2542 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b332 b hb) (b331 b hb))
    (by norm_num [i2542, i332, i331, RationalInterval.mul]) (by norm_num [i2542, i332, i331, RationalInterval.mul])

def n2543 (b : ℝ) : ℝ := (n2542 b) + (n2523 b)
def i2543 : RationalInterval := ⟨(-548822874341172493229990624683 / 125000000000000000000000000000 : ℚ), (-548822874059838188173799177839 / 125000000000000000000000000000 : ℚ)⟩
theorem b2543 (b : ℝ) (hb : rootInterval.Contains b) : i2543.Contains (n2543 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2542 b hb) (b2523 b hb))
    (by norm_num [i2543, i2542, i2523, RationalInterval.add]) (by norm_num [i2543, i2542, i2523, RationalInterval.add])

def n2544 (b : ℝ) : ℝ := (n2541 b) + (n2543 b)
def i2544 : RationalInterval := ⟨(-4199868128806799501378189141227 / 250000000000000000000000000000 : ℚ), (-8399736192109796425820385476339 / 500000000000000000000000000000 : ℚ)⟩
theorem b2544 (b : ℝ) (hb : rootInterval.Contains b) : i2544.Contains (n2544 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2541 b hb) (b2543 b hb))
    (by norm_num [i2544, i2541, i2543, RationalInterval.add]) (by norm_num [i2544, i2541, i2543, RationalInterval.add])

def n2545 (b : ℝ) : ℝ := (n331 b) * (n318 b)
def i2545 : RationalInterval := ⟨(-652029219554476681335534792851 / 500000000000000000000000000000 : ℚ), (-652029214845169632253261460701 / 500000000000000000000000000000 : ℚ)⟩
theorem b2545 (b : ℝ) (hb : rootInterval.Contains b) : i2545.Contains (n2545 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b331 b hb) (b318 b hb))
    (by norm_num [i2545, i331, i318, RationalInterval.mul]) (by norm_num [i2545, i331, i318, RationalInterval.mul])

def n2546 (b : ℝ) : ℝ := (n331 b) * (n319 b)
def i2546 : RationalInterval := ⟨(-56209702249873663541733194649 / 100000000000000000000000000000 : ℚ), (-562097016565737921421692751953 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2546 (b : ℝ) (hb : rootInterval.Contains b) : i2546.Contains (n2546 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b331 b hb) (b319 b hb))
    (by norm_num [i2546, i331, i319, RationalInterval.mul]) (by norm_num [i2546, i331, i319, RationalInterval.mul])

def n2547 (b : ℝ) : ℝ := (n318 b) * (n331 b)
def i2547 : RationalInterval := ⟨(-652029219554476681335534792851 / 500000000000000000000000000000 : ℚ), (-652029214845169632253261460701 / 500000000000000000000000000000 : ℚ)⟩
theorem b2547 (b : ℝ) (hb : rootInterval.Contains b) : i2547.Contains (n2547 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b318 b hb) (b331 b hb))
    (by norm_num [i2547, i318, i331, RationalInterval.mul]) (by norm_num [i2547, i318, i331, RationalInterval.mul])

def n2548 (b : ℝ) : ℝ := (n2545 b) + (n2547 b)
def i2548 : RationalInterval := ⟨(-652029219554476681335534792851 / 250000000000000000000000000000 : ℚ), (-652029214845169632253261460701 / 250000000000000000000000000000 : ℚ)⟩
theorem b2548 (b : ℝ) (hb : rootInterval.Contains b) : i2548.Contains (n2548 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2545 b hb) (b2547 b hb))
    (by norm_num [i2548, i2545, i2547, RationalInterval.add]) (by norm_num [i2548, i2545, i2547, RationalInterval.add])

def n2549 (b : ℝ) : ℝ := (n2546 b) + (n2460 b)
def i2549 : RationalInterval := ⟨(407915725675819471007435677461 / 500000000000000000000000000000 : ℚ), (81583146714333317836462880573 / 100000000000000000000000000000 : ℚ)⟩
theorem b2549 (b : ℝ) (hb : rootInterval.Contains b) : i2549.Contains (n2549 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2546 b hb) (b2460 b hb))
    (by norm_num [i2549, i2546, i2460, RationalInterval.add]) (by norm_num [i2549, i2546, i2460, RationalInterval.add])

def n2550 (b : ℝ) : ℝ := (n2458 b) + (n334 b)
def i2550 : RationalInterval := ⟨(407915725675819471007435677461 / 500000000000000000000000000000 : ℚ), (81583146714333317836462880573 / 100000000000000000000000000000 : ℚ)⟩
theorem b2550 (b : ℝ) (hb : rootInterval.Contains b) : i2550.Contains (n2550 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2458 b hb) (b334 b hb))
    (by norm_num [i2550, i2458, i334, RationalInterval.add]) (by norm_num [i2550, i2458, i334, RationalInterval.add])

def n2551 (b : ℝ) : ℝ := (n2459 b) + (n2461 b)
def i2551 : RationalInterval := ⟨(593937715180596411571783638183 / 500000000000000000000000000000 : ℚ), (593937721409397883143622968433 / 500000000000000000000000000000 : ℚ)⟩
theorem b2551 (b : ℝ) (hb : rootInterval.Contains b) : i2551.Contains (n2551 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2459 b hb) (b2461 b hb))
    (by norm_num [i2551, i2459, i2461, RationalInterval.add]) (by norm_num [i2551, i2459, i2461, RationalInterval.add])

def n2552 (b : ℝ) : ℝ := (n2536 b) * (n318 b)
def i2552 : RationalInterval := ⟨(-151332376557968121121900922211 / 25000000000000000000000000000 : ℚ), (-6053294987024749874739488743291 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2552 (b : ℝ) (hb : rootInterval.Contains b) : i2552.Contains (n2552 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2536 b hb) (b318 b hb))
    (by norm_num [i2552, i2536, i318, RationalInterval.mul]) (by norm_num [i2552, i2536, i318, RationalInterval.mul])

def n2553 (b : ℝ) : ℝ := (n2536 b) * (n319 b)
def i2553 : RationalInterval := ⟨(-1304596108883192234274781827009 / 500000000000000000000000000000 : ℚ), (-2609192176616590343198114752263 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2553 (b : ℝ) (hb : rootInterval.Contains b) : i2553.Contains (n2553 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2536 b hb) (b319 b hb))
    (by norm_num [i2553, i2536, i319, RationalInterval.mul]) (by norm_num [i2553, i2536, i319, RationalInterval.mul])

def n2554 (b : ℝ) : ℝ := (n2537 b) * (n318 b)
def i2554 : RationalInterval := ⟨(121087313144157231872650754621 / 250000000000000000000000000000 : ℚ), (19373971060958825641552245369 / 40000000000000000000000000000 : ℚ)⟩
theorem b2554 (b : ℝ) (hb : rootInterval.Contains b) : i2554.Contains (n2554 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2537 b hb) (b318 b hb))
    (by norm_num [i2554, i2537, i318, RationalInterval.mul]) (by norm_num [i2554, i2537, i318, RationalInterval.mul])

def n2555 (b : ℝ) : ℝ := (n2537 b) * (n319 b)
def i2555 : RationalInterval := ⟨(104386146989524370077809123087 / 500000000000000000000000000000 : ℚ), (52193076249245202120446680387 / 250000000000000000000000000000 : ℚ)⟩
theorem b2555 (b : ℝ) (hb : rootInterval.Contains b) : i2555.Contains (n2555 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2537 b hb) (b319 b hb))
    (by norm_num [i2555, i2537, i319, RationalInterval.mul]) (by norm_num [i2555, i2537, i319, RationalInterval.mul])

def n2556 (b : ℝ) : ℝ := (n2210 b) * (n331 b)
def i2556 : RationalInterval := ⟨(-882759896720934049432427971751 / 250000000000000000000000000000 : ℚ), (-1765519786675910539655667115547 / 500000000000000000000000000000 : ℚ)⟩
theorem b2556 (b : ℝ) (hb : rootInterval.Contains b) : i2556.Contains (n2556 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2210 b hb) (b331 b hb))
    (by norm_num [i2556, i2210, i331, RationalInterval.mul]) (by norm_num [i2556, i2210, i331, RationalInterval.mul])

def n2557 (b : ℝ) : ℝ := (n2213 b) * (n331 b)
def i2557 : RationalInterval := ⟨(-83299320984805844727281805391 / 50000000000000000000000000000 : ℚ), (-416496602821274869484642569503 / 250000000000000000000000000000 : ℚ)⟩
theorem b2557 (b : ℝ) (hb : rootInterval.Contains b) : i2557.Contains (n2557 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2213 b hb) (b331 b hb))
    (by norm_num [i2557, i2213, i331, RationalInterval.mul]) (by norm_num [i2557, i2213, i331, RationalInterval.mul])

def n2558 (b : ℝ) : ℝ := (n2552 b) + (n2556 b)
def i2558 : RationalInterval := ⟨(-2396083662300615260651437193861 / 250000000000000000000000000000 : ℚ), (-1916866912075314190810164594877 / 200000000000000000000000000000 : ℚ)⟩
theorem b2558 (b : ℝ) (hb : rootInterval.Contains b) : i2558.Contains (n2558 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2552 b hb) (b2556 b hb))
    (by norm_num [i2558, i2552, i2556, RationalInterval.add]) (by norm_num [i2558, i2552, i2556, RationalInterval.add])

def n2559 (b : ℝ) : ℝ := (n2553 b) + (n2467 b)
def i2559 : RationalInterval := ⟨(560933785957991701920804992277 / 500000000000000000000000000000 : ℚ), (1121867627111193306862353423917 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2559 (b : ℝ) (hb : rootInterval.Contains b) : i2559.Contains (n2559 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2553 b hb) (b2467 b hb))
    (by norm_num [i2559, i2553, i2467, RationalInterval.add]) (by norm_num [i2559, i2553, i2467, RationalInterval.add])

def n2560 (b : ℝ) : ℝ := (n2554 b) + (n2557 b)
def i2560 : RationalInterval := ⟨(-147704645889935995881879136167 / 125000000000000000000000000000 : ℚ), (-1181637134761128836899764143787 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2560 (b : ℝ) (hb : rootInterval.Contains b) : i2560.Contains (n2560 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2554 b hb) (b2557 b hb))
    (by norm_num [i2560, i2554, i2557, RationalInterval.add]) (by norm_num [i2560, i2554, i2557, RationalInterval.add])

def n2561 (b : ℝ) : ℝ := (n2555 b) + (n2468 b)
def i2561 : RationalInterval := ⟨(1969130619106133039185593700661 / 1000000000000000000000000000000 : ℚ), (123070664930759490544040028217 / 62500000000000000000000000000 : ℚ)⟩
theorem b2561 (b : ℝ) (hb : rootInterval.Contains b) : i2561.Contains (n2561 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2555 b hb) (b2468 b hb))
    (by norm_num [i2561, i2555, i2468, RationalInterval.add]) (by norm_num [i2561, i2555, i2468, RationalInterval.add])

def n2562 (b : ℝ) : ℝ := (n331 b) * (n2210 b)
def i2562 : RationalInterval := ⟨(-882759896720934049432427971751 / 250000000000000000000000000000 : ℚ), (-1765519786675910539655667115547 / 500000000000000000000000000000 : ℚ)⟩
theorem b2562 (b : ℝ) (hb : rootInterval.Contains b) : i2562.Contains (n2562 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b331 b hb) (b2210 b hb))
    (by norm_num [i2562, i331, i2210, RationalInterval.mul]) (by norm_num [i2562, i331, i2210, RationalInterval.mul])

def n2563 (b : ℝ) : ℝ := (n318 b) * (n2536 b)
def i2563 : RationalInterval := ⟨(-151332376557968121121900922211 / 25000000000000000000000000000 : ℚ), (-6053294987024749874739488743291 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2563 (b : ℝ) (hb : rootInterval.Contains b) : i2563.Contains (n2563 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b318 b hb) (b2536 b hb))
    (by norm_num [i2563, i318, i2536, RationalInterval.mul]) (by norm_num [i2563, i318, i2536, RationalInterval.mul])

def n2564 (b : ℝ) : ℝ := (n318 b) * (n2537 b)
def i2564 : RationalInterval := ⟨(121087313144157231872650754621 / 250000000000000000000000000000 : ℚ), (19373971060958825641552245369 / 40000000000000000000000000000 : ℚ)⟩
theorem b2564 (b : ℝ) (hb : rootInterval.Contains b) : i2564.Contains (n2564 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b318 b hb) (b2537 b hb))
    (by norm_num [i2564, i318, i2537, RationalInterval.mul]) (by norm_num [i2564, i318, i2537, RationalInterval.mul])

def n2565 (b : ℝ) : ℝ := (n319 b) * (n2536 b)
def i2565 : RationalInterval := ⟨(-1304596108883192234274781827009 / 500000000000000000000000000000 : ℚ), (-2609192176616590343198114752263 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2565 (b : ℝ) (hb : rootInterval.Contains b) : i2565.Contains (n2565 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b319 b hb) (b2536 b hb))
    (by norm_num [i2565, i319, i2536, RationalInterval.mul]) (by norm_num [i2565, i319, i2536, RationalInterval.mul])

def n2566 (b : ℝ) : ℝ := (n319 b) * (n2537 b)
def i2566 : RationalInterval := ⟨(104386146989524370077809123087 / 500000000000000000000000000000 : ℚ), (52193076249245202120446680387 / 250000000000000000000000000000 : ℚ)⟩
theorem b2566 (b : ℝ) (hb : rootInterval.Contains b) : i2566.Contains (n2566 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b319 b hb) (b2537 b hb))
    (by norm_num [i2566, i319, i2537, RationalInterval.mul]) (by norm_num [i2566, i319, i2537, RationalInterval.mul])

def n2567 (b : ℝ) : ℝ := (n2562 b) + (n2563 b)
def i2567 : RationalInterval := ⟨(-2396083662300615260651437193861 / 250000000000000000000000000000 : ℚ), (-1916866912075314190810164594877 / 200000000000000000000000000000 : ℚ)⟩
theorem b2567 (b : ℝ) (hb : rootInterval.Contains b) : i2567.Contains (n2567 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2562 b hb) (b2563 b hb))
    (by norm_num [i2567, i2562, i2563, RationalInterval.add]) (by norm_num [i2567, i2562, i2563, RationalInterval.add])

def n2568 (b : ℝ) : ℝ := (n2215 b) + (n2564 b)
def i2568 : RationalInterval := ⟨(-147704645889935995881879136167 / 125000000000000000000000000000 : ℚ), (-1181637134761128836899764143787 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2568 (b : ℝ) (hb : rootInterval.Contains b) : i2568.Contains (n2568 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2215 b hb) (b2564 b hb))
    (by norm_num [i2568, i2215, i2564, RationalInterval.add]) (by norm_num [i2568, i2215, i2564, RationalInterval.add])

def n2569 (b : ℝ) : ℝ := (n2471 b) + (n2565 b)
def i2569 : RationalInterval := ⟨(560933785957991701920804992277 / 500000000000000000000000000000 : ℚ), (1121867627111193306862353423917 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2569 (b : ℝ) (hb : rootInterval.Contains b) : i2569.Contains (n2569 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2471 b hb) (b2565 b hb))
    (by norm_num [i2569, i2471, i2565, RationalInterval.add]) (by norm_num [i2569, i2471, i2565, RationalInterval.add])

def n2570 (b : ℝ) : ℝ := (n2472 b) + (n2566 b)
def i2570 : RationalInterval := ⟨(1969130619106133039185593700661 / 1000000000000000000000000000000 : ℚ), (123070664930759490544040028217 / 62500000000000000000000000000 : ℚ)⟩
theorem b2570 (b : ℝ) (hb : rootInterval.Contains b) : i2570.Contains (n2570 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2472 b hb) (b2566 b hb))
    (by norm_num [i2570, i2472, i2566, RationalInterval.add]) (by norm_num [i2570, i2472, i2566, RationalInterval.add])

def n2571 (b : ℝ) : ℝ := (n2558 b) + (n2567 b)
def i2571 : RationalInterval := ⟨(-2396083662300615260651437193861 / 125000000000000000000000000000 : ℚ), (-1916866912075314190810164594877 / 100000000000000000000000000000 : ℚ)⟩
theorem b2571 (b : ℝ) (hb : rootInterval.Contains b) : i2571.Contains (n2571 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2558 b hb) (b2567 b hb))
    (by norm_num [i2571, i2558, i2567, RationalInterval.add]) (by norm_num [i2571, i2558, i2567, RationalInterval.add])

def n2572 (b : ℝ) : ℝ := (n2559 b) + (n2568 b)
def i2572 : RationalInterval := ⟨(-29884797601752281606711552391 / 500000000000000000000000000000 : ℚ), (-5976950764993553003741071987 / 100000000000000000000000000000 : ℚ)⟩
theorem b2572 (b : ℝ) (hb : rootInterval.Contains b) : i2572.Contains (n2572 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2559 b hb) (b2568 b hb))
    (by norm_num [i2572, i2559, i2568, RationalInterval.add]) (by norm_num [i2572, i2559, i2568, RationalInterval.add])

def n2573 (b : ℝ) : ℝ := (n2560 b) + (n2569 b)
def i2573 : RationalInterval := ⟨(-29884797601752281606711552391 / 500000000000000000000000000000 : ℚ), (-5976950764993553003741071987 / 100000000000000000000000000000 : ℚ)⟩
theorem b2573 (b : ℝ) (hb : rootInterval.Contains b) : i2573.Contains (n2573 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2560 b hb) (b2569 b hb))
    (by norm_num [i2573, i2560, i2569, RationalInterval.add]) (by norm_num [i2573, i2560, i2569, RationalInterval.add])

def n2574 (b : ℝ) : ℝ := (n2561 b) + (n2570 b)
def i2574 : RationalInterval := ⟨(1969130619106133039185593700661 / 500000000000000000000000000000 : ℚ), (123070664930759490544040028217 / 31250000000000000000000000000 : ℚ)⟩
theorem b2574 (b : ℝ) (hb : rootInterval.Contains b) : i2574.Contains (n2574 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2561 b hb) (b2570 b hb))
    (by norm_num [i2574, i2561, i2570, RationalInterval.add]) (by norm_num [i2574, i2561, i2570, RationalInterval.add])

def n2575 (b : ℝ) : ℝ := (n2284 b) * (n2571 b)
def i2575 : RationalInterval := ⟨(1856463715240700993931538183649 / 200000000000000000000000000000 : ℚ), (9282318771749678310851322047023 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2575 (b : ℝ) (hb : rootInterval.Contains b) : i2575.Contains (n2575 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2284 b hb) (b2571 b hb))
    (by norm_num [i2575, i2284, i2571, RationalInterval.mul]) (by norm_num [i2575, i2284, i2571, RationalInterval.mul])

def n2576 (b : ℝ) : ℝ := (n2284 b) * (n2572 b)
def i2576 : RationalInterval := ⟨(14471521409613017750662681811 / 500000000000000000000000000000 : ℚ), (2894308555803278518827575061 / 100000000000000000000000000000 : ℚ)⟩
theorem b2576 (b : ℝ) (hb : rootInterval.Contains b) : i2576.Contains (n2576 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2284 b hb) (b2572 b hb))
    (by norm_num [i2576, i2284, i2572, RationalInterval.mul]) (by norm_num [i2576, i2284, i2572, RationalInterval.mul])

def n2577 (b : ℝ) : ℝ := (n2284 b) * (n2573 b)
def i2577 : RationalInterval := ⟨(14471521409613017750662681811 / 500000000000000000000000000000 : ℚ), (2894308555803278518827575061 / 100000000000000000000000000000 : ℚ)⟩
theorem b2577 (b : ℝ) (hb : rootInterval.Contains b) : i2577.Contains (n2577 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2284 b hb) (b2573 b hb))
    (by norm_num [i2577, i2284, i2573, RationalInterval.mul]) (by norm_num [i2577, i2284, i2573, RationalInterval.mul])

def n2578 (b : ℝ) : ℝ := (n2284 b) * (n2574 b)
def i2578 : RationalInterval := ⟨(-953540280176727203635091535521 / 500000000000000000000000000000 : ℚ), (-1907080518689845898042004749447 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2578 (b : ℝ) (hb : rootInterval.Contains b) : i2578.Contains (n2578 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2284 b hb) (b2574 b hb))
    (by norm_num [i2578, i2284, i2574, RationalInterval.mul]) (by norm_num [i2578, i2284, i2574, RationalInterval.mul])

def n2579 (b : ℝ) : ℝ := (n2576 b) + (n15 b)
def i2579 : RationalInterval := ⟨(514471521409613017750662681811 / 500000000000000000000000000000 : ℚ), (102894308555803278518827575061 / 100000000000000000000000000000 : ℚ)⟩
theorem b2579 (b : ℝ) (hb : rootInterval.Contains b) : i2579.Contains (n2579 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2576 b hb) (b15 b hb))
    (by norm_num [i2579, i2576, i15, RationalInterval.add]) (by norm_num [i2579, i2576, i15, RationalInterval.add])

def n2580 (b : ℝ) : ℝ := (n2577 b) + (n15 b)
def i2580 : RationalInterval := ⟨(514471521409613017750662681811 / 500000000000000000000000000000 : ℚ), (102894308555803278518827575061 / 100000000000000000000000000000 : ℚ)⟩
theorem b2580 (b : ℝ) (hb : rootInterval.Contains b) : i2580.Contains (n2580 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2577 b hb) (b15 b hb))
    (by norm_num [i2580, i2577, i15, RationalInterval.add]) (by norm_num [i2580, i2577, i15, RationalInterval.add])

def n2581 (b : ℝ) : ℝ := (n2529 b) * (n2290 b)
def i2581 : RationalInterval := ⟨(-168525480383910166745800166677 / 125000000000000000000000000000 : ℚ), (-674101900515458441925074336563 / 500000000000000000000000000000 : ℚ)⟩
theorem b2581 (b : ℝ) (hb : rootInterval.Contains b) : i2581.Contains (n2581 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2529 b hb) (b2290 b hb))
    (by norm_num [i2581, i2529, i2290, RationalInterval.mul]) (by norm_num [i2581, i2529, i2290, RationalInterval.mul])

def n2582 (b : ℝ) : ℝ := (n2581 b) * (n2225 b)
def i2582 : RationalInterval := ⟨(-2278841853969848736617577706341 / 200000000000000000000000000000 : ℚ), (-11394208796782824312912831681203 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2582 (b : ℝ) (hb : rootInterval.Contains b) : i2582.Contains (n2582 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2581 b hb) (b2225 b hb))
    (by norm_num [i2582, i2581, i2225, RationalInterval.mul]) (by norm_num [i2582, i2581, i2225, RationalInterval.mul])

def n2583 (b : ℝ) : ℝ := (n2581 b) * (n2226 b)
def i2583 : RationalInterval := ⟨(-2571811358144618455250778306977 / 500000000000000000000000000000 : ℚ), (-2571811245641134456709889277213 / 500000000000000000000000000000 : ℚ)⟩
theorem b2583 (b : ℝ) (hb : rootInterval.Contains b) : i2583.Contains (n2583 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2581 b hb) (b2226 b hb))
    (by norm_num [i2583, i2581, i2226, RationalInterval.mul]) (by norm_num [i2583, i2581, i2226, RationalInterval.mul])

def n2584 (b : ℝ) : ℝ := (n2581 b) * (n2227 b)
def i2584 : RationalInterval := ⟨(-2571811358144618455250778306977 / 500000000000000000000000000000 : ℚ), (-2571811245641134456709889277213 / 500000000000000000000000000000 : ℚ)⟩
theorem b2584 (b : ℝ) (hb : rootInterval.Contains b) : i2584.Contains (n2584 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2581 b hb) (b2227 b hb))
    (by norm_num [i2584, i2581, i2227, RationalInterval.mul]) (by norm_num [i2584, i2581, i2227, RationalInterval.mul])

def n2585 (b : ℝ) : ℝ := (n2581 b) * (n2228 b)
def i2585 : RationalInterval := ⟨(-579305032753297081709930180919 / 250000000000000000000000000000 : ℚ), (-2317220024265542702337086413371 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2585 (b : ℝ) (hb : rootInterval.Contains b) : i2585.Contains (n2585 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2581 b hb) (b2228 b hb))
    (by norm_num [i2585, i2581, i2228, RationalInterval.mul]) (by norm_num [i2585, i2581, i2228, RationalInterval.mul])

def n2586 (b : ℝ) : ℝ := (n2575 b) + (n2582 b)
def i2586 : RationalInterval := ⟨(-105594534682286935671509880673 / 50000000000000000000000000000 : ℚ), (-105594501251657300103075481709 / 50000000000000000000000000000 : ℚ)⟩
theorem b2586 (b : ℝ) (hb : rootInterval.Contains b) : i2586.Contains (n2586 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2575 b hb) (b2582 b hb))
    (by norm_num [i2586, i2575, i2582, RationalInterval.add]) (by norm_num [i2586, i2575, i2582, RationalInterval.add])

def n2587 (b : ℝ) : ℝ := (n2579 b) + (n2583 b)
def i2587 : RationalInterval := ⟨(-1028669918367502718750057812583 / 250000000000000000000000000000 : ℚ), (-514334925715529516028937850477 / 125000000000000000000000000000 : ℚ)⟩
theorem b2587 (b : ℝ) (hb : rootInterval.Contains b) : i2587.Contains (n2587 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2579 b hb) (b2583 b hb))
    (by norm_num [i2587, i2579, i2583, RationalInterval.add]) (by norm_num [i2587, i2579, i2583, RationalInterval.add])

def n2588 (b : ℝ) : ℝ := (n2580 b) + (n2584 b)
def i2588 : RationalInterval := ⟨(-1028669918367502718750057812583 / 250000000000000000000000000000 : ℚ), (-514334925715529516028937850477 / 125000000000000000000000000000 : ℚ)⟩
theorem b2588 (b : ℝ) (hb : rootInterval.Contains b) : i2588.Contains (n2588 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2580 b hb) (b2584 b hb))
    (by norm_num [i2588, i2580, i2584, RationalInterval.add]) (by norm_num [i2588, i2580, i2584, RationalInterval.add])

def n2589 (b : ℝ) : ℝ := (n2578 b) + (n2585 b)
def i2589 : RationalInterval := ⟨(-2112150345683321367054951897359 / 500000000000000000000000000000 : ℚ), (-2112150271477694300189545581409 / 500000000000000000000000000000 : ℚ)⟩
theorem b2589 (b : ℝ) (hb : rootInterval.Contains b) : i2589.Contains (n2589 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2578 b hb) (b2585 b hb))
    (by norm_num [i2589, i2578, i2585, RationalInterval.add]) (by norm_num [i2589, i2578, i2585, RationalInterval.add])

def n2590 (b : ℝ) : ℝ := (n2529 b) + (n2544 b)
def i2590 : RationalInterval := ⟨(-2254892557998157361616157095797 / 100000000000000000000000000000 : ℚ), (-22548925405363821302098605993229 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2590 (b : ℝ) (hb : rootInterval.Contains b) : i2590.Contains (n2590 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2529 b hb) (b2544 b hb))
    (by norm_num [i2590, i2529, i2544, RationalInterval.add]) (by norm_num [i2590, i2529, i2544, RationalInterval.add])

def n2591 (b : ℝ) : ℝ := (n2590 b) * (n2290 b)
def i2591 : RationalInterval := ⟨(-1057510959100532507126498575151 / 200000000000000000000000000000 : ℚ), (-660944328722942189862633249397 / 125000000000000000000000000000 : ℚ)⟩
theorem b2591 (b : ℝ) (hb : rootInterval.Contains b) : i2591.Contains (n2591 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2590 b hb) (b2290 b hb))
    (by norm_num [i2591, i2590, i2290, RationalInterval.mul]) (by norm_num [i2591, i2590, i2290, RationalInterval.mul])

def n2592 (b : ℝ) : ℝ := (n2303 b) * (n2529 b)
def i2592 : RationalInterval := ⟨(-86388498972919137810735576058483 / 1000000000000000000000000000000 : ℚ), (-86388497644181872592792036633599 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2592 (b : ℝ) (hb : rootInterval.Contains b) : i2592.Contains (n2592 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2303 b hb) (b2529 b hb))
    (by norm_num [i2592, i2303, i2529, RationalInterval.mul]) (by norm_num [i2592, i2303, i2529, RationalInterval.mul])

def n2593 (b : ℝ) : ℝ := (n2592 b) * (n2306 b)
def i2593 : RationalInterval := ⟨(-9809558686425937974832233221463 / 1000000000000000000000000000000 : ℚ), (-9809558188325427177479202644533 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2593 (b : ℝ) (hb : rootInterval.Contains b) : i2593.Contains (n2593 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2592 b hb) (b2306 b hb))
    (by norm_num [i2593, i2592, i2306, RationalInterval.mul]) (by norm_num [i2593, i2592, i2306, RationalInterval.mul])

def n2594 (b : ℝ) : ℝ := -(n2593 b)
def i2594 : RationalInterval := ⟨(9809558188325427177479202644533 / 1000000000000000000000000000000 : ℚ), (9809558686425937974832233221463 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2594 (b : ℝ) (hb : rootInterval.Contains b) : i2594.Contains (n2594 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b2593 b hb))
    (by norm_num [i2594, i2593, RationalInterval.neg]) (by norm_num [i2594, i2593, RationalInterval.neg])

def n2595 (b : ℝ) : ℝ := (n2591 b) + (n2594 b)
def i2595 : RationalInterval := ⟨(2261001696411382320923354884389 / 500000000000000000000000000000 : ℚ), (4522004056642400455931167226287 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2595 (b : ℝ) (hb : rootInterval.Contains b) : i2595.Contains (n2595 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2591 b hb) (b2594 b hb))
    (by norm_num [i2595, i2591, i2594, RationalInterval.add]) (by norm_num [i2595, i2591, i2594, RationalInterval.add])

def n2596 (b : ℝ) : ℝ := (n2595 b) * (n2229 b)
def i2596 : RationalInterval := ⟨(3528531386487628972500099960629 / 500000000000000000000000000000 : ℚ), (44106649411252324109408476311 / 6250000000000000000000000000 : ℚ)⟩
theorem b2596 (b : ℝ) (hb : rootInterval.Contains b) : i2596.Contains (n2596 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2595 b hb) (b2229 b hb))
    (by norm_num [i2596, i2595, i2229, RationalInterval.mul]) (by norm_num [i2596, i2595, i2229, RationalInterval.mul])

def n2597 (b : ℝ) : ℝ := (n2595 b) * (n2230 b)
def i2597 : RationalInterval := ⟨(608370582190625977841967490811 / 200000000000000000000000000000 : ℚ), (190115838086219467452293481729 / 62500000000000000000000000000 : ℚ)⟩
theorem b2597 (b : ℝ) (hb : rootInterval.Contains b) : i2597.Contains (n2597 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2595 b hb) (b2230 b hb))
    (by norm_num [i2597, i2595, i2230, RationalInterval.mul]) (by norm_num [i2597, i2595, i2230, RationalInterval.mul])

def n2598 (b : ℝ) : ℝ := (n2595 b) * (n2231 b)
def i2598 : RationalInterval := ⟨(608370582190625977841967490811 / 200000000000000000000000000000 : ℚ), (190115838086219467452293481729 / 62500000000000000000000000000 : ℚ)⟩
theorem b2598 (b : ℝ) (hb : rootInterval.Contains b) : i2598.Contains (n2598 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2595 b hb) (b2231 b hb))
    (by norm_num [i2598, i2595, i2231, RationalInterval.mul]) (by norm_num [i2598, i2595, i2231, RationalInterval.mul])

def n2599 (b : ℝ) : ℝ := (n2595 b) * (n2232 b)
def i2599 : RationalInterval := ⟨(655575090482936143850052398043 / 500000000000000000000000000000 : ℚ), (52446016007017297790097186811 / 40000000000000000000000000000 : ℚ)⟩
theorem b2599 (b : ℝ) (hb : rootInterval.Contains b) : i2599.Contains (n2599 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2595 b hb) (b2232 b hb))
    (by norm_num [i2599, i2595, i2232, RationalInterval.mul]) (by norm_num [i2599, i2595, i2232, RationalInterval.mul])

def n2600 (b : ℝ) : ℝ := (n2586 b) + (n2596 b)
def i2600 : RationalInterval := ⟨(2472586039664759615785001153899 / 500000000000000000000000000000 : ℚ), (247258694038361292772192328779 / 50000000000000000000000000000 : ℚ)⟩
theorem b2600 (b : ℝ) (hb : rootInterval.Contains b) : i2600.Contains (n2600 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2586 b hb) (b2596 b hb))
    (by norm_num [i2600, i2586, i2596, RationalInterval.add]) (by norm_num [i2600, i2586, i2596, RationalInterval.add])

def n2601 (b : ℝ) : ℝ := (n2587 b) + (n2597 b)
def i2601 : RationalInterval := ⟨(-1072826762516880985790393796277 / 1000000000000000000000000000000 : ℚ), (-134103249543090581124350887019 / 125000000000000000000000000000 : ℚ)⟩
theorem b2601 (b : ℝ) (hb : rootInterval.Contains b) : i2601.Contains (n2601 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2587 b hb) (b2597 b hb))
    (by norm_num [i2601, i2587, i2597, RationalInterval.add]) (by norm_num [i2601, i2587, i2597, RationalInterval.add])

def n2602 (b : ℝ) : ℝ := (n2588 b) + (n2598 b)
def i2602 : RationalInterval := ⟨(-1072826762516880985790393796277 / 1000000000000000000000000000000 : ℚ), (-134103249543090581124350887019 / 125000000000000000000000000000 : ℚ)⟩
theorem b2602 (b : ℝ) (hb : rootInterval.Contains b) : i2602.Contains (n2602 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2588 b hb) (b2598 b hb))
    (by norm_num [i2602, i2588, i2598, RationalInterval.add]) (by norm_num [i2602, i2588, i2598, RationalInterval.add])

def n2603 (b : ℝ) : ℝ := (n2589 b) + (n2599 b)
def i2603 : RationalInterval := ⟨(-364143813800096305801224874829 / 125000000000000000000000000000 : ℚ), (-2913150142779956155626661492543 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2603 (b : ℝ) (hb : rootInterval.Contains b) : i2603.Contains (n2603 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2589 b hb) (b2599 b hb))
    (by norm_num [i2603, i2589, i2599, RationalInterval.add]) (by norm_num [i2603, i2589, i2599, RationalInterval.add])

def n2604 (b : ℝ) : ℝ := (n2318 b) * (n2548 b)
def i2604 : RationalInterval := ⟨(-574335273520711838371971497941 / 125000000000000000000000000000 : ℚ), (-2297341005369184385548771425017 / 500000000000000000000000000000 : ℚ)⟩
theorem b2604 (b : ℝ) (hb : rootInterval.Contains b) : i2604.Contains (n2604 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2318 b hb) (b2548 b hb))
    (by norm_num [i2604, i2318, i2548, RationalInterval.mul]) (by norm_num [i2604, i2318, i2548, RationalInterval.mul])

def n2605 (b : ℝ) : ℝ := (n2318 b) * (n2549 b)
def i2605 : RationalInterval := ⟨(179654818755421046874621880147 / 125000000000000000000000000000 : ℚ), (1437238622982974765136982595487 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2605 (b : ℝ) (hb : rootInterval.Contains b) : i2605.Contains (n2605 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2318 b hb) (b2549 b hb))
    (by norm_num [i2605, i2318, i2549, RationalInterval.mul]) (by norm_num [i2605, i2318, i2549, RationalInterval.mul])

def n2606 (b : ℝ) : ℝ := (n2318 b) * (n2550 b)
def i2606 : RationalInterval := ⟨(179654818755421046874621880147 / 125000000000000000000000000000 : ℚ), (1437238622982974765136982595487 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2606 (b : ℝ) (hb : rootInterval.Contains b) : i2606.Contains (n2606 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2318 b hb) (b2550 b hb))
    (by norm_num [i2606, i2318, i2550, RationalInterval.mul]) (by norm_num [i2606, i2318, i2550, RationalInterval.mul])

def n2607 (b : ℝ) : ℝ := (n2318 b) * (n2551 b)
def i2607 : RationalInterval := ⟨(523165771047419800809085238933 / 250000000000000000000000000000 : ℚ), (523165792957894495993277539073 / 250000000000000000000000000000 : ℚ)⟩
theorem b2607 (b : ℝ) (hb : rootInterval.Contains b) : i2607.Contains (n2607 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2318 b hb) (b2551 b hb))
    (by norm_num [i2607, i2318, i2551, RationalInterval.mul]) (by norm_num [i2607, i2318, i2551, RationalInterval.mul])

def n2608 (b : ℝ) : ℝ := (n2600 b) + (n2604 b)
def i2608 : RationalInterval := ⟨(35048989116382452459423032427 / 100000000000000000000000000000 : ℚ), (175245935014428542173151862773 / 500000000000000000000000000000 : ℚ)⟩
theorem b2608 (b : ℝ) (hb : rootInterval.Contains b) : i2608.Contains (n2608 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2600 b hb) (b2604 b hb))
    (by norm_num [i2608, i2600, i2604, RationalInterval.add]) (by norm_num [i2608, i2600, i2604, RationalInterval.add])

def n2609 (b : ℝ) : ℝ := (n2601 b) + (n2605 b)
def i2609 : RationalInterval := ⟨(364411787526487389206581244899 / 1000000000000000000000000000000 : ℚ), (72882525327650023228435099867 / 200000000000000000000000000000 : ℚ)⟩
theorem b2609 (b : ℝ) (hb : rootInterval.Contains b) : i2609.Contains (n2609 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2601 b hb) (b2605 b hb))
    (by norm_num [i2609, i2601, i2605, RationalInterval.add]) (by norm_num [i2609, i2601, i2605, RationalInterval.add])

