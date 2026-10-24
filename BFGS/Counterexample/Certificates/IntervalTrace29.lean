import BFGS.Counterexample.Certificates.IntervalTrace28

/-! Generated arithmetic proofs. Each bound is checked by the Lean kernel. -/
namespace BFGS.Counterexample.Trace
noncomputable section
open BFGS RationalInterval
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false

def n2610 (b : ℝ) : ℝ := (n2602 b) + (n2606 b)
def i2610 : RationalInterval := ⟨(364411787526487389206581244899 / 1000000000000000000000000000000 : ℚ), (72882525327650023228435099867 / 200000000000000000000000000000 : ℚ)⟩
theorem b2610 (b : ℝ) (hb : rootInterval.Contains b) : i2610.Contains (n2610 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2602 b hb) (b2606 b hb))
    (by norm_num [i2610, i2602, i2606, RationalInterval.add]) (by norm_num [i2610, i2602, i2606, RationalInterval.add])

def n2611 (b : ℝ) : ℝ := (n2603 b) + (n2607 b)
def i2611 : RationalInterval := ⟨(-8204874262110912431734580429 / 10000000000000000000000000000 : ℚ), (-820486970948378171653551336251 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2611 (b : ℝ) (hb : rootInterval.Contains b) : i2611.Contains (n2611 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2603 b hb) (b2607 b hb))
    (by norm_num [i2611, i2603, i2607, RationalInterval.add]) (by norm_num [i2611, i2603, i2607, RationalInterval.add])

def n2612 (b : ℝ) : ℝ := (n230 b) * (n331 b)
def i2612 : RationalInterval := ⟨(242102267054965247380035233953 / 200000000000000000000000000000 : ℚ), (605255668351839013297557327473 / 500000000000000000000000000000 : ℚ)⟩
theorem b2612 (b : ℝ) (hb : rootInterval.Contains b) : i2612.Contains (n2612 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b230 b hb) (b331 b hb))
    (by norm_num [i2612, i230, i331, RationalInterval.mul]) (by norm_num [i2612, i230, i331, RationalInterval.mul])

def n2613 (b : ℝ) : ℝ := (n232 b) * (n331 b)
def i2613 : RationalInterval := ⟨(-461761950684723490931705321969 / 500000000000000000000000000000 : ℚ), (-923523900083342112276876838351 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2613 (b : ℝ) (hb : rootInterval.Contains b) : i2613.Contains (n2613 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b232 b hb) (b331 b hb))
    (by norm_num [i2613, i232, i331, RationalInterval.mul]) (by norm_num [i2613, i232, i331, RationalInterval.mul])

def n2614 (b : ℝ) : ℝ := (n331 b) * (n331 b)
def i2614 : RationalInterval := ⟨(27242127028831210019471365943 / 25000000000000000000000000000 : ℚ), (136210635242114574045585581681 / 125000000000000000000000000000 : ℚ)⟩
theorem b2614 (b : ℝ) (hb : rootInterval.Contains b) : i2614.Contains (n2614 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b331 b hb) (b331 b hb))
    (by norm_num [i2614, i331, i331, RationalInterval.mul]) (by norm_num [i2614, i331, i331, RationalInterval.mul])

def n2615 (b : ℝ) : ℝ := (n318 b) * (n2612 b)
def i2615 : RationalInterval := ⟨(1512221501852386842883330222951 / 1000000000000000000000000000000 : ℚ), (189027689251959608787078635037 / 125000000000000000000000000000 : ℚ)⟩
theorem b2615 (b : ℝ) (hb : rootInterval.Contains b) : i2615.Contains (n2615 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b318 b hb) (b2612 b hb))
    (by norm_num [i2615, i318, i2612, RationalInterval.mul]) (by norm_num [i2615, i318, i2612, RationalInterval.mul])

def n2616 (b : ℝ) : ℝ := (n319 b) * (n2613 b)
def i2616 : RationalInterval := ⟨(-497289079093533849326192799273 / 1000000000000000000000000000000 : ℚ), (-248644536665440130712616350911 / 500000000000000000000000000000 : ℚ)⟩
theorem b2616 (b : ℝ) (hb : rootInterval.Contains b) : i2616.Contains (n2616 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b319 b hb) (b2613 b hb))
    (by norm_num [i2616, i319, i2613, RationalInterval.mul]) (by norm_num [i2616, i319, i2613, RationalInterval.mul])

def n2617 (b : ℝ) : ℝ := (n2615 b) + (n2616 b)
def i2617 : RationalInterval := ⟨(507466211379426496778568711839 / 500000000000000000000000000000 : ℚ), (507466220342398304435698189237 / 500000000000000000000000000000 : ℚ)⟩
theorem b2617 (b : ℝ) (hb : rootInterval.Contains b) : i2617.Contains (n2617 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2615 b hb) (b2616 b hb))
    (by norm_num [i2617, i2615, i2616, RationalInterval.add]) (by norm_num [i2617, i2615, i2616, RationalInterval.add])

def n2618 (b : ℝ) : ℝ := (n2614 b) + (n2617 b)
def i2618 : RationalInterval := ⟨(1052308751956050697167996030699 / 500000000000000000000000000000 : ℚ), (1052308761310856600618040515961 / 500000000000000000000000000000 : ℚ)⟩
theorem b2618 (b : ℝ) (hb : rootInterval.Contains b) : i2618.Contains (n2618 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2614 b hb) (b2617 b hb))
    (by norm_num [i2618, i2614, i2617, RationalInterval.add]) (by norm_num [i2618, i2614, i2617, RationalInterval.add])

def n2619 (b : ℝ) : ℝ := (n118 b) * (n2612 b)
def i2619 : RationalInterval := ⟨(2582467696991461447408592103711 / 1000000000000000000000000000000 : ℚ), (1291233851940504709288194642367 / 500000000000000000000000000000 : ℚ)⟩
theorem b2619 (b : ℝ) (hb : rootInterval.Contains b) : i2619.Contains (n2619 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b118 b hb) (b2612 b hb))
    (by norm_num [i2619, i118, i2612, RationalInterval.mul]) (by norm_num [i2619, i118, i2612, RationalInterval.mul])

def n2620 (b : ℝ) : ℝ := (n119 b) * (n2613 b)
def i2620 : RationalInterval := ⟨(-244153642634371059797877629373 / 250000000000000000000000000000 : ℚ), (-976614565647629885288618872697 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2620 (b : ℝ) (hb : rootInterval.Contains b) : i2620.Contains (n2620 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b119 b hb) (b2613 b hb))
    (by norm_num [i2620, i119, i2613, RationalInterval.mul]) (by norm_num [i2620, i119, i2613, RationalInterval.mul])

def n2621 (b : ℝ) : ℝ := (n2619 b) + (n2620 b)
def i2621 : RationalInterval := ⟨(1605853126453977208217081586219 / 1000000000000000000000000000000 : ℚ), (1605853138233379533287770412037 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2621 (b : ℝ) (hb : rootInterval.Contains b) : i2621.Contains (n2621 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2619 b hb) (b2620 b hb))
    (by norm_num [i2621, i2619, i2620, RationalInterval.add]) (by norm_num [i2621, i2619, i2620, RationalInterval.add])

def n2622 (b : ℝ) : ℝ := (n120 b) * (n2612 b)
def i2622 : RationalInterval := ⟨(160012507909426260324277210109 / 125000000000000000000000000000 : ℚ), (1280100067199675593922932335229 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2622 (b : ℝ) (hb : rootInterval.Contains b) : i2622.Contains (n2622 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b120 b hb) (b2612 b hb))
    (by norm_num [i2622, i120, i2612, RationalInterval.mul]) (by norm_num [i2622, i120, i2612, RationalInterval.mul])

def n2623 (b : ℝ) : ℝ := (n121 b) * (n2613 b)
def i2623 : RationalInterval := ⟨(-17360961551619647686533017409 / 31250000000000000000000000000 : ℚ), (-555550766467445485382771699187 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2623 (b : ℝ) (hb : rootInterval.Contains b) : i2623.Contains (n2623 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b121 b hb) (b2613 b hb))
    (by norm_num [i2623, i121, i2613, RationalInterval.mul]) (by norm_num [i2623, i121, i2613, RationalInterval.mul])

def n2624 (b : ℝ) : ℝ := (n2622 b) + (n2623 b)
def i2624 : RationalInterval := ⟨(90568661702947669578145140473 / 125000000000000000000000000000 : ℚ), (362274650366115054270080318021 / 500000000000000000000000000000 : ℚ)⟩
theorem b2624 (b : ℝ) (hb : rootInterval.Contains b) : i2624.Contains (n2624 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2622 b hb) (b2623 b hb))
    (by norm_num [i2624, i2622, i2623, RationalInterval.add]) (by norm_num [i2624, i2622, i2623, RationalInterval.add])

def n2625 (b : ℝ) : ℝ := (n331 b) + (n2624 b)
def i2625 : RationalInterval := ⟨(-19958157998324656316654988329 / 62500000000000000000000000000 : ℚ), (-319330520489182524614777552767 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2625 (b : ℝ) (hb : rootInterval.Contains b) : i2625.Contains (n2625 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b331 b hb) (b2624 b hb))
    (by norm_num [i2625, i331, i2624, RationalInterval.add]) (by norm_num [i2625, i331, i2624, RationalInterval.add])

def n2626 (b : ℝ) : ℝ := (n2612 b) * (n2210 b)
def i2626 : RationalInterval := ⟨(4094689198843848290291922326663 / 1000000000000000000000000000000 : ℚ), (4094689217896686288873018365029 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2626 (b : ℝ) (hb : rootInterval.Contains b) : i2626.Contains (n2626 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2612 b hb) (b2210 b hb))
    (by norm_num [i2626, i2612, i2210, RationalInterval.mul]) (by norm_num [i2626, i2612, i2210, RationalInterval.mul])

def n2627 (b : ℝ) : ℝ := (n2613 b) * (n2213 b)
def i2627 : RationalInterval := ⟨(-1473903648786678336821152266483 / 1000000000000000000000000000000 : ℚ), (-1473903639822849897186623984711 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2627 (b : ℝ) (hb : rootInterval.Contains b) : i2627.Contains (n2627 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2613 b hb) (b2213 b hb))
    (by norm_num [i2627, i2613, i2213, RationalInterval.mul]) (by norm_num [i2627, i2613, i2213, RationalInterval.mul])

def n2628 (b : ℝ) : ℝ := (n2626 b) + (n2627 b)
def i2628 : RationalInterval := ⟨(131039277502858497673538503009 / 50000000000000000000000000000 : ℚ), (1310392789036918195843197190159 / 500000000000000000000000000000 : ℚ)⟩
theorem b2628 (b : ℝ) (hb : rootInterval.Contains b) : i2628.Contains (n2628 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2626 b hb) (b2627 b hb))
    (by norm_num [i2628, i2626, i2627, RationalInterval.add]) (by norm_num [i2628, i2626, i2627, RationalInterval.add])

def n2629 (b : ℝ) : ℝ := (n2628 b) * (n13 b)
def i2629 : RationalInterval := ⟨(131039277502858497673538503009 / 25000000000000000000000000000 : ℚ), (1310392789036918195843197190159 / 250000000000000000000000000000 : ℚ)⟩
theorem b2629 (b : ℝ) (hb : rootInterval.Contains b) : i2629.Contains (n2629 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2628 b hb) (b13 b hb))
    (by norm_num [i2629, i2628, i13, RationalInterval.mul]) (by norm_num [i2629, i2628, i13, RationalInterval.mul])

def n2630 (b : ℝ) : ℝ := (n2629 b) + (n2614 b)
def i2630 : RationalInterval := ⟨(19785175566461213461626233619 / 3125000000000000000000000000 : ℚ), (1582814059521147343934368353521 / 250000000000000000000000000000 : ℚ)⟩
theorem b2630 (b : ℝ) (hb : rootInterval.Contains b) : i2630.Contains (n2630 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2629 b hb) (b2614 b hb))
    (by norm_num [i2630, i2629, i2614, RationalInterval.add]) (by norm_num [i2630, i2629, i2614, RationalInterval.add])

def n2631 (b : ℝ) : ℝ := (n2546 b) + (n334 b)
def i2631 : RationalInterval := ⟨(-56209702249873663541733194649 / 50000000000000000000000000000 : ℚ), (-562097016565737921421692751953 / 500000000000000000000000000000 : ℚ)⟩
theorem b2631 (b : ℝ) (hb : rootInterval.Contains b) : i2631.Contains (n2631 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2546 b hb) (b334 b hb))
    (by norm_num [i2631, i2546, i334, RationalInterval.add]) (by norm_num [i2631, i2546, i334, RationalInterval.add])

def n2632 (b : ℝ) : ℝ := (n2621 b) * (n318 b)
def i2632 : RationalInterval := ⟨(7836324371891284169686992167 / 3906250000000000000000000000 : ℚ), (2006099067687259891487785827739 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2632 (b : ℝ) (hb : rootInterval.Contains b) : i2632.Contains (n2632 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2621 b hb) (b318 b hb))
    (by norm_num [i2632, i2621, i318, RationalInterval.mul]) (by norm_num [i2632, i2621, i318, RationalInterval.mul])

def n2633 (b : ℝ) : ℝ := (n2621 b) * (n319 b)
def i2633 : RationalInterval := ⟨(864702270388161141930662857243 / 1000000000000000000000000000000 : ℚ), (864702285547103529735143778417 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2633 (b : ℝ) (hb : rootInterval.Contains b) : i2633.Contains (n2633 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2621 b hb) (b319 b hb))
    (by norm_num [i2633, i2621, i319, RationalInterval.mul]) (by norm_num [i2633, i2621, i319, RationalInterval.mul])

def n2634 (b : ℝ) : ℝ := (n2625 b) * (n318 b)
def i2634 : RationalInterval := ⟨(-319136867101482570184451899 / 800000000000000000000000000 : ℚ), (-199460535894867109547485387027 / 500000000000000000000000000000 : ℚ)⟩
theorem b2634 (b : ℝ) (hb : rootInterval.Contains b) : i2634.Contains (n2634 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2625 b hb) (b318 b hb))
    (by norm_num [i2634, i2625, i318, RationalInterval.mul]) (by norm_num [i2634, i2625, i318, RationalInterval.mul])

def n2635 (b : ℝ) : ℝ := (n2625 b) * (n319 b)
def i2635 : RationalInterval := ⟨(-171949620304104696211865251031 / 1000000000000000000000000000000 : ℚ), (-85974807260539010530543593037 / 500000000000000000000000000000 : ℚ)⟩
theorem b2635 (b : ℝ) (hb : rootInterval.Contains b) : i2635.Contains (n2635 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2625 b hb) (b319 b hb))
    (by norm_num [i2635, i2625, i319, RationalInterval.mul]) (by norm_num [i2635, i2625, i319, RationalInterval.mul])

def n2636 (b : ℝ) : ℝ := (n2633 b) + (n2556 b)
def i2636 : RationalInterval := ⟨(-2666337316495575055799049029761 / 1000000000000000000000000000000 : ℚ), (-2666337287804717549576190452677 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2636 (b : ℝ) (hb : rootInterval.Contains b) : i2636.Contains (n2636 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2633 b hb) (b2556 b hb))
    (by norm_num [i2636, i2633, i2556, RationalInterval.add]) (by norm_num [i2636, i2633, i2556, RationalInterval.add])

def n2637 (b : ℝ) : ℝ := (n2635 b) + (n2557 b)
def i2637 : RationalInterval := ⟨(-1837936040000221590757501358851 / 1000000000000000000000000000000 : ℚ), (-918968012903088749499828732043 / 500000000000000000000000000000 : ℚ)⟩
theorem b2637 (b : ℝ) (hb : rootInterval.Contains b) : i2637.Contains (n2637 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2635 b hb) (b2557 b hb))
    (by norm_num [i2637, i2635, i2557, RationalInterval.add]) (by norm_num [i2637, i2635, i2557, RationalInterval.add])

def n2638 (b : ℝ) : ℝ := (n318 b) * (n2621 b)
def i2638 : RationalInterval := ⟨(7836324371891284169686992167 / 3906250000000000000000000000 : ℚ), (2006099067687259891487785827739 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2638 (b : ℝ) (hb : rootInterval.Contains b) : i2638.Contains (n2638 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b318 b hb) (b2621 b hb))
    (by norm_num [i2638, i318, i2621, RationalInterval.mul]) (by norm_num [i2638, i318, i2621, RationalInterval.mul])

def n2639 (b : ℝ) : ℝ := (n318 b) * (n2625 b)
def i2639 : RationalInterval := ⟨(-319136867101482570184451899 / 800000000000000000000000000 : ℚ), (-199460535894867109547485387027 / 500000000000000000000000000000 : ℚ)⟩
theorem b2639 (b : ℝ) (hb : rootInterval.Contains b) : i2639.Contains (n2639 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b318 b hb) (b2625 b hb))
    (by norm_num [i2639, i318, i2625, RationalInterval.mul]) (by norm_num [i2639, i318, i2625, RationalInterval.mul])

def n2640 (b : ℝ) : ℝ := (n319 b) * (n2621 b)
def i2640 : RationalInterval := ⟨(864702270388161141930662857243 / 1000000000000000000000000000000 : ℚ), (864702285547103529735143778417 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2640 (b : ℝ) (hb : rootInterval.Contains b) : i2640.Contains (n2640 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b319 b hb) (b2621 b hb))
    (by norm_num [i2640, i319, i2621, RationalInterval.mul]) (by norm_num [i2640, i319, i2621, RationalInterval.mul])

def n2641 (b : ℝ) : ℝ := (n319 b) * (n2625 b)
def i2641 : RationalInterval := ⟨(-171949620304104696211865251031 / 1000000000000000000000000000000 : ℚ), (-85974807260539010530543593037 / 500000000000000000000000000000 : ℚ)⟩
theorem b2641 (b : ℝ) (hb : rootInterval.Contains b) : i2641.Contains (n2641 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b319 b hb) (b2625 b hb))
    (by norm_num [i2641, i319, i2625, RationalInterval.mul]) (by norm_num [i2641, i319, i2625, RationalInterval.mul])

def n2642 (b : ℝ) : ℝ := (n2562 b) + (n2640 b)
def i2642 : RationalInterval := ⟨(-2666337316495575055799049029761 / 1000000000000000000000000000000 : ℚ), (-2666337287804717549576190452677 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2642 (b : ℝ) (hb : rootInterval.Contains b) : i2642.Contains (n2642 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2562 b hb) (b2640 b hb))
    (by norm_num [i2642, i2562, i2640, RationalInterval.add]) (by norm_num [i2642, i2562, i2640, RationalInterval.add])

def n2643 (b : ℝ) : ℝ := (n2215 b) + (n2641 b)
def i2643 : RationalInterval := ⟨(-1837936040000221590757501358851 / 1000000000000000000000000000000 : ℚ), (-918968012903088749499828732043 / 500000000000000000000000000000 : ℚ)⟩
theorem b2643 (b : ℝ) (hb : rootInterval.Contains b) : i2643.Contains (n2643 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2215 b hb) (b2641 b hb))
    (by norm_num [i2643, i2215, i2641, RationalInterval.add]) (by norm_num [i2643, i2215, i2641, RationalInterval.add])

def n2644 (b : ℝ) : ℝ := (n2632 b) + (n2638 b)
def i2644 : RationalInterval := ⟨(7836324371891284169686992167 / 1953125000000000000000000000 : ℚ), (2006099067687259891487785827739 / 500000000000000000000000000000 : ℚ)⟩
theorem b2644 (b : ℝ) (hb : rootInterval.Contains b) : i2644.Contains (n2644 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2632 b hb) (b2638 b hb))
    (by norm_num [i2644, i2632, i2638, RationalInterval.add]) (by norm_num [i2644, i2632, i2638, RationalInterval.add])

def n2645 (b : ℝ) : ℝ := (n2636 b) + (n2639 b)
def i2645 : RationalInterval := ⟨(-3065258400372428268529613903511 / 1000000000000000000000000000000 : ℚ), (-3065258359594451768671161226731 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2645 (b : ℝ) (hb : rootInterval.Contains b) : i2645.Contains (n2645 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2636 b hb) (b2639 b hb))
    (by norm_num [i2645, i2636, i2639, RationalInterval.add]) (by norm_num [i2645, i2636, i2639, RationalInterval.add])

def n2646 (b : ℝ) : ℝ := (n2634 b) + (n2642 b)
def i2646 : RationalInterval := ⟨(-3065258400372428268529613903511 / 1000000000000000000000000000000 : ℚ), (-3065258359594451768671161226731 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2646 (b : ℝ) (hb : rootInterval.Contains b) : i2646.Contains (n2646 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2634 b hb) (b2642 b hb))
    (by norm_num [i2646, i2634, i2642, RationalInterval.add]) (by norm_num [i2646, i2634, i2642, RationalInterval.add])

def n2647 (b : ℝ) : ℝ := (n2637 b) + (n2643 b)
def i2647 : RationalInterval := ⟨(-1837936040000221590757501358851 / 500000000000000000000000000000 : ℚ), (-918968012903088749499828732043 / 250000000000000000000000000000 : ℚ)⟩
theorem b2647 (b : ℝ) (hb : rootInterval.Contains b) : i2647.Contains (n2647 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2637 b hb) (b2643 b hb))
    (by norm_num [i2647, i2637, i2643, RationalInterval.add]) (by norm_num [i2647, i2637, i2643, RationalInterval.add])

def n2648 (b : ℝ) : ℝ := (n2284 b) * (n2644 b)
def i2648 : RationalInterval := ⟨(-15543072495309839155379056769 / 8000000000000000000000000000 : ℚ), (-971442005702335648606499493133 / 500000000000000000000000000000 : ℚ)⟩
theorem b2648 (b : ℝ) (hb : rootInterval.Contains b) : i2648.Contains (n2648 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2284 b hb) (b2644 b hb))
    (by norm_num [i2648, i2284, i2644, RationalInterval.mul]) (by norm_num [i2648, i2284, i2644, RationalInterval.mul])

def n2649 (b : ℝ) : ℝ := (n2284 b) * (n2645 b)
def i2649 : RationalInterval := ⟨(371083464805103130098547572427 / 250000000000000000000000000000 : ℚ), (742166948240064068093263698789 / 500000000000000000000000000000 : ℚ)⟩
theorem b2649 (b : ℝ) (hb : rootInterval.Contains b) : i2649.Contains (n2649 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2284 b hb) (b2645 b hb))
    (by norm_num [i2649, i2284, i2645, RationalInterval.mul]) (by norm_num [i2649, i2284, i2645, RationalInterval.mul])

def n2650 (b : ℝ) : ℝ := (n2284 b) * (n2646 b)
def i2650 : RationalInterval := ⟨(371083464805103130098547572427 / 250000000000000000000000000000 : ℚ), (742166948240064068093263698789 / 500000000000000000000000000000 : ℚ)⟩
theorem b2650 (b : ℝ) (hb : rootInterval.Contains b) : i2650.Contains (n2650 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2284 b hb) (b2646 b hb))
    (by norm_num [i2650, i2284, i2646, RationalInterval.mul]) (by norm_num [i2650, i2284, i2646, RationalInterval.mul])

def n2651 (b : ℝ) : ℝ := (n2284 b) * (n2647 b)
def i2651 : RationalInterval := ⟨(1780020053217343243495097008887 / 1000000000000000000000000000000 : ℚ), (890010043983019722034915976929 / 500000000000000000000000000000 : ℚ)⟩
theorem b2651 (b : ℝ) (hb : rootInterval.Contains b) : i2651.Contains (n2651 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2284 b hb) (b2647 b hb))
    (by norm_num [i2651, i2284, i2647, RationalInterval.mul]) (by norm_num [i2651, i2284, i2647, RationalInterval.mul])

def n2652 (b : ℝ) : ℝ := (n2651 b) + (n15 b)
def i2652 : RationalInterval := ⟨(2780020053217343243495097008887 / 1000000000000000000000000000000 : ℚ), (1390010043983019722034915976929 / 500000000000000000000000000000 : ℚ)⟩
theorem b2652 (b : ℝ) (hb : rootInterval.Contains b) : i2652.Contains (n2652 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2651 b hb) (b15 b hb))
    (by norm_num [i2652, i2651, i15, RationalInterval.add]) (by norm_num [i2652, i2651, i15, RationalInterval.add])

def n2653 (b : ℝ) : ℝ := (n2618 b) * (n2290 b)
def i2653 : RationalInterval := ⟨(246758544513317841721160446539 / 500000000000000000000000000000 : ℚ), (493517105059622389528366384097 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2653 (b : ℝ) (hb : rootInterval.Contains b) : i2653.Contains (n2653 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2618 b hb) (b2290 b hb))
    (by norm_num [i2653, i2618, i2290, RationalInterval.mul]) (by norm_num [i2653, i2618, i2290, RationalInterval.mul])

def n2654 (b : ℝ) : ℝ := (n2653 b) * (n2225 b)
def i2654 : RationalInterval := ⟨(4170910030701651328251490481339 / 1000000000000000000000000000000 : ℚ), (4170910209311875154473887875527 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2654 (b : ℝ) (hb : rootInterval.Contains b) : i2654.Contains (n2654 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2653 b hb) (b2225 b hb))
    (by norm_num [i2654, i2653, i2225, RationalInterval.mul]) (by norm_num [i2654, i2653, i2225, RationalInterval.mul])

def n2655 (b : ℝ) : ℝ := (n2653 b) * (n2226 b)
def i2655 : RationalInterval := ⟨(941425026768391849192789683803 / 500000000000000000000000000000 : ℚ), (470712534589579038602847811719 / 250000000000000000000000000000 : ℚ)⟩
theorem b2655 (b : ℝ) (hb : rootInterval.Contains b) : i2655.Contains (n2655 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2653 b hb) (b2226 b hb))
    (by norm_num [i2655, i2653, i2226, RationalInterval.mul]) (by norm_num [i2655, i2653, i2226, RationalInterval.mul])

def n2656 (b : ℝ) : ℝ := (n2653 b) * (n2227 b)
def i2656 : RationalInterval := ⟨(941425026768391849192789683803 / 500000000000000000000000000000 : ℚ), (470712534589579038602847811719 / 250000000000000000000000000000 : ℚ)⟩
theorem b2656 (b : ℝ) (hb : rootInterval.Contains b) : i2656.Contains (n2656 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2653 b hb) (b2227 b hb))
    (by norm_num [i2656, i2653, i2227, RationalInterval.mul]) (by norm_num [i2656, i2653, i2227, RationalInterval.mul])

def n2657 (b : ℝ) : ℝ := (n2653 b) * (n2228 b)
def i2657 : RationalInterval := ⟨(169646114353824773177539100653 / 200000000000000000000000000000 : ℚ), (169646122390268933779466240153 / 200000000000000000000000000000 : ℚ)⟩
theorem b2657 (b : ℝ) (hb : rootInterval.Contains b) : i2657.Contains (n2657 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2653 b hb) (b2228 b hb))
    (by norm_num [i2657, i2653, i2228, RationalInterval.mul]) (by norm_num [i2657, i2653, i2228, RationalInterval.mul])

def n2658 (b : ℝ) : ℝ := (n2648 b) + (n2654 b)
def i2658 : RationalInterval := ⟨(1114012984393960716914554192607 / 500000000000000000000000000000 : ℚ), (2228026197907203857260888889261 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2658 (b : ℝ) (hb : rootInterval.Contains b) : i2658.Contains (n2658 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2648 b hb) (b2654 b hb))
    (by norm_num [i2658, i2648, i2654, RationalInterval.add]) (by norm_num [i2658, i2648, i2654, RationalInterval.add])

def n2659 (b : ℝ) : ℝ := (n2649 b) + (n2655 b)
def i2659 : RationalInterval := ⟨(1683591956378598109389884828657 / 500000000000000000000000000000 : ℚ), (1683592017419222145298959322227 / 500000000000000000000000000000 : ℚ)⟩
theorem b2659 (b : ℝ) (hb : rootInterval.Contains b) : i2659.Contains (n2659 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2649 b hb) (b2655 b hb))
    (by norm_num [i2659, i2649, i2655, RationalInterval.add]) (by norm_num [i2659, i2649, i2655, RationalInterval.add])

def n2660 (b : ℝ) : ℝ := (n2650 b) + (n2656 b)
def i2660 : RationalInterval := ⟨(1683591956378598109389884828657 / 500000000000000000000000000000 : ℚ), (1683592017419222145298959322227 / 500000000000000000000000000000 : ℚ)⟩
theorem b2660 (b : ℝ) (hb : rootInterval.Contains b) : i2660.Contains (n2660 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2650 b hb) (b2656 b hb))
    (by norm_num [i2660, i2650, i2656, RationalInterval.add]) (by norm_num [i2660, i2650, i2656, RationalInterval.add])

def n2661 (b : ℝ) : ℝ := (n2652 b) + (n2657 b)
def i2661 : RationalInterval := ⟨(453531328123308388672849064019 / 125000000000000000000000000000 : ℚ), (3628250699917384112967163154623 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2661 (b : ℝ) (hb : rootInterval.Contains b) : i2661.Contains (n2661 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2652 b hb) (b2657 b hb))
    (by norm_num [i2661, i2652, i2657, RationalInterval.add]) (by norm_num [i2661, i2652, i2657, RationalInterval.add])

def n2662 (b : ℝ) : ℝ := (n2618 b) + (n2630 b)
def i2662 : RationalInterval := ⟨(4217936842589844851028193409739 / 500000000000000000000000000000 : ℚ), (4217936880353151288486777223003 / 500000000000000000000000000000 : ℚ)⟩
theorem b2662 (b : ℝ) (hb : rootInterval.Contains b) : i2662.Contains (n2662 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2618 b hb) (b2630 b hb))
    (by norm_num [i2662, i2618, i2630, RationalInterval.add]) (by norm_num [i2662, i2618, i2630, RationalInterval.add])

def n2663 (b : ℝ) : ℝ := (n2662 b) * (n2290 b)
def i2663 : RationalInterval := ⟨(494537346663652325301819926699 / 250000000000000000000000000000 : ℚ), (1978149451044227563303011111081 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2663 (b : ℝ) (hb : rootInterval.Contains b) : i2663.Contains (n2663 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2662 b hb) (b2290 b hb))
    (by norm_num [i2663, i2662, i2290, RationalInterval.mul]) (by norm_num [i2663, i2662, i2290, RationalInterval.mul])

def n2664 (b : ℝ) : ℝ := (n2303 b) * (n2618 b)
def i2664 : RationalInterval := ⟨(15811481858358641702362515014521 / 500000000000000000000000000000 : ℚ), (15811482122183465676664087407803 / 500000000000000000000000000000 : ℚ)⟩
theorem b2664 (b : ℝ) (hb : rootInterval.Contains b) : i2664.Contains (n2664 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2303 b hb) (b2618 b hb))
    (by norm_num [i2664, i2303, i2618, RationalInterval.mul]) (by norm_num [i2664, i2303, i2618, RationalInterval.mul])

def n2665 (b : ℝ) : ℝ := (n2664 b) * (n2306 b)
def i2665 : RationalInterval := ⟨(3590840344789048178970394809109 / 1000000000000000000000000000000 : ℚ), (897710132951579402259656600661 / 250000000000000000000000000000 : ℚ)⟩
theorem b2665 (b : ℝ) (hb : rootInterval.Contains b) : i2665.Contains (n2665 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2664 b hb) (b2306 b hb))
    (by norm_num [i2665, i2664, i2306, RationalInterval.mul]) (by norm_num [i2665, i2664, i2306, RationalInterval.mul])

def n2666 (b : ℝ) : ℝ := -(n2665 b)
def i2666 : RationalInterval := ⟨(-897710132951579402259656600661 / 250000000000000000000000000000 : ℚ), (-3590840344789048178970394809109 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2666 (b : ℝ) (hb : rootInterval.Contains b) : i2666.Contains (n2666 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b2665 b hb))
    (by norm_num [i2666, i2665, RationalInterval.neg]) (by norm_num [i2666, i2665, RationalInterval.neg])

def n2667 (b : ℝ) : ℝ := (n2663 b) + (n2666 b)
def i2667 : RationalInterval := ⟨(-201586393143963538478918336981 / 125000000000000000000000000000 : ℚ), (-403172723436205153916845924507 / 250000000000000000000000000000 : ℚ)⟩
theorem b2667 (b : ℝ) (hb : rootInterval.Contains b) : i2667.Contains (n2667 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2663 b hb) (b2666 b hb))
    (by norm_num [i2667, i2663, i2666, RationalInterval.add]) (by norm_num [i2667, i2663, i2666, RationalInterval.add])

def n2668 (b : ℝ) : ℝ := (n2667 b) * (n2229 b)
def i2668 : RationalInterval := ⟨(-1258387247014580295333604288677 / 500000000000000000000000000000 : ℚ), (-503354813427440176835731872779 / 200000000000000000000000000000 : ℚ)⟩
theorem b2668 (b : ℝ) (hb : rootInterval.Contains b) : i2668.Contains (n2668 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2667 b hb) (b2229 b hb))
    (by norm_num [i2668, i2667, i2229, RationalInterval.mul]) (by norm_num [i2668, i2667, i2229, RationalInterval.mul])

def n2669 (b : ℝ) : ℝ := (n2667 b) * (n2230 b)
def i2669 : RationalInterval := ⟨(-1084822126806819102847334955011 / 1000000000000000000000000000000 : ℚ), (-1084821939185474663575649764949 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2669 (b : ℝ) (hb : rootInterval.Contains b) : i2669.Contains (n2669 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2667 b hb) (b2230 b hb))
    (by norm_num [i2669, i2667, i2230, RationalInterval.mul]) (by norm_num [i2669, i2667, i2230, RationalInterval.mul])

def n2670 (b : ℝ) : ℝ := (n2667 b) * (n2231 b)
def i2670 : RationalInterval := ⟨(-1084822126806819102847334955011 / 1000000000000000000000000000000 : ℚ), (-1084821939185474663575649764949 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2670 (b : ℝ) (hb : rootInterval.Contains b) : i2670.Contains (n2670 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2667 b hb) (b2231 b hb))
    (by norm_num [i2670, i2667, i2231, RationalInterval.mul]) (by norm_num [i2670, i2667, i2231, RationalInterval.mul])

def n2671 (b : ℝ) : ℝ := (n2667 b) * (n2232 b)
def i2671 : RationalInterval := ⟨(-233799064954294404869405356543 / 500000000000000000000000000000 : ℚ), (-116899511869650358232885043453 / 250000000000000000000000000000 : ℚ)⟩
theorem b2671 (b : ℝ) (hb : rootInterval.Contains b) : i2671.Contains (n2671 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2667 b hb) (b2232 b hb))
    (by norm_num [i2671, i2667, i2232, RationalInterval.mul]) (by norm_num [i2671, i2667, i2232, RationalInterval.mul])

def n2672 (b : ℝ) : ℝ := (n2658 b) + (n2668 b)
def i2672 : RationalInterval := ⟨(-14437426262061957841905009607 / 50000000000000000000000000000 : ℚ), (-144373934614998513458885237317 / 500000000000000000000000000000 : ℚ)⟩
theorem b2672 (b : ℝ) (hb : rootInterval.Contains b) : i2672.Contains (n2672 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2658 b hb) (b2668 b hb))
    (by norm_num [i2672, i2658, i2668, RationalInterval.add]) (by norm_num [i2672, i2658, i2668, RationalInterval.add])

def n2673 (b : ℝ) : ℝ := (n2659 b) + (n2669 b)
def i2673 : RationalInterval := ⟨(2282361785950377115932434702303 / 1000000000000000000000000000000 : ℚ), (456472419130593925404453775901 / 200000000000000000000000000000 : ℚ)⟩
theorem b2673 (b : ℝ) (hb : rootInterval.Contains b) : i2673.Contains (n2673 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2659 b hb) (b2669 b hb))
    (by norm_num [i2673, i2659, i2669, RationalInterval.add]) (by norm_num [i2673, i2659, i2669, RationalInterval.add])

def n2674 (b : ℝ) : ℝ := (n2660 b) + (n2670 b)
def i2674 : RationalInterval := ⟨(2282361785950377115932434702303 / 1000000000000000000000000000000 : ℚ), (456472419130593925404453775901 / 200000000000000000000000000000 : ℚ)⟩
theorem b2674 (b : ℝ) (hb : rootInterval.Contains b) : i2674.Contains (n2674 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2660 b hb) (b2670 b hb))
    (by norm_num [i2674, i2660, i2670, RationalInterval.add]) (by norm_num [i2674, i2660, i2670, RationalInterval.add])

def n2675 (b : ℝ) : ℝ := (n2661 b) + (n2671 b)
def i2675 : RationalInterval := ⟨(1580326247538939149821990899533 / 500000000000000000000000000000 : ℚ), (3160652652438782680035622980811 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2675 (b : ℝ) (hb : rootInterval.Contains b) : i2675.Contains (n2675 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2661 b hb) (b2671 b hb))
    (by norm_num [i2675, i2661, i2671, RationalInterval.add]) (by norm_num [i2675, i2661, i2671, RationalInterval.add])

def n2676 (b : ℝ) : ℝ := (n2318 b) * (n2547 b)
def i2676 : RationalInterval := ⟨(-574335273520711838371971497941 / 250000000000000000000000000000 : ℚ), (-2297341005369184385548771425017 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2676 (b : ℝ) (hb : rootInterval.Contains b) : i2676.Contains (n2676 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2318 b hb) (b2547 b hb))
    (by norm_num [i2676, i2318, i2547, RationalInterval.mul]) (by norm_num [i2676, i2318, i2547, RationalInterval.mul])

def n2677 (b : ℝ) : ℝ := (n2318 b) * (n2545 b)
def i2677 : RationalInterval := ⟨(-574335273520711838371971497941 / 250000000000000000000000000000 : ℚ), (-2297341005369184385548771425017 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2677 (b : ℝ) (hb : rootInterval.Contains b) : i2677.Contains (n2677 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2318 b hb) (b2545 b hb))
    (by norm_num [i2677, i2318, i2545, RationalInterval.mul]) (by norm_num [i2677, i2318, i2545, RationalInterval.mul])

def n2678 (b : ℝ) : ℝ := (n2318 b) * (n2631 b)
def i2678 : RationalInterval := ⟨(-1980476564424991533147539492927 / 1000000000000000000000000000000 : ℚ), (-495119120336804750599211605231 / 250000000000000000000000000000 : ℚ)⟩
theorem b2678 (b : ℝ) (hb : rootInterval.Contains b) : i2678.Contains (n2678 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2318 b hb) (b2631 b hb))
    (by norm_num [i2678, i2318, i2631, RationalInterval.mul]) (by norm_num [i2678, i2318, i2631, RationalInterval.mul])

def n2679 (b : ℝ) : ℝ := (n2673 b) + (n2676 b)
def i2679 : RationalInterval := ⟨(-14979308132470237555451289461 / 1000000000000000000000000000000 : ℚ), (-1872363714526844815812818189 / 125000000000000000000000000000 : ℚ)⟩
theorem b2679 (b : ℝ) (hb : rootInterval.Contains b) : i2679.Contains (n2679 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2673 b hb) (b2676 b hb))
    (by norm_num [i2679, i2673, i2676, RationalInterval.add]) (by norm_num [i2679, i2673, i2676, RationalInterval.add])

def n2680 (b : ℝ) : ℝ := (n2674 b) + (n2677 b)
def i2680 : RationalInterval := ⟨(-14979308132470237555451289461 / 1000000000000000000000000000000 : ℚ), (-1872363714526844815812818189 / 125000000000000000000000000000 : ℚ)⟩
theorem b2680 (b : ℝ) (hb : rootInterval.Contains b) : i2680.Contains (n2680 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2674 b hb) (b2677 b hb))
    (by norm_num [i2680, i2674, i2677, RationalInterval.add]) (by norm_num [i2680, i2674, i2677, RationalInterval.add])

def n2681 (b : ℝ) : ℝ := (n2675 b) + (n2678 b)
def i2681 : RationalInterval := ⟨(1180175930652886766496442306139 / 1000000000000000000000000000000 : ℚ), (1180176171091563677638776559887 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2681 (b : ℝ) (hb : rootInterval.Contains b) : i2681.Contains (n2681 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2675 b hb) (b2678 b hb))
    (by norm_num [i2681, i2675, i2678, RationalInterval.add]) (by norm_num [i2681, i2675, i2678, RationalInterval.add])

def n2682 (b : ℝ) : ℝ := (n2190 b) * (n1983 b)
def i2682 : RationalInterval := ⟨(-135675009433078924298551062417 / 250000000000000000000000000000 : ℚ), (-542699312798027856300006187657 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2682 (b : ℝ) (hb : rootInterval.Contains b) : i2682.Contains (n2682 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2190 b hb) (b1983 b hb))
    (by norm_num [i2682, i2190, i1983, RationalInterval.mul]) (by norm_num [i2682, i2190, i1983, RationalInterval.mul])

def n2683 (b : ℝ) : ℝ := (n2333 b) * (n2018 b)
def i2683 : RationalInterval := ⟨(456950866315758052382396881 / 3906250000000000000000000000 : ℚ), (116979524609279015650306996553 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2683 (b : ℝ) (hb : rootInterval.Contains b) : i2683.Contains (n2683 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2333 b hb) (b2018 b hb))
    (by norm_num [i2683, i2333, i2018, RationalInterval.mul]) (by norm_num [i2683, i2333, i2018, RationalInterval.mul])

def n2684 (b : ℝ) : ℝ := (n2682 b) + (n2683 b)
def i2684 : RationalInterval := ⟨(-106430153988870408946077662033 / 250000000000000000000000000000 : ℚ), (-6651871690449200635151549861 / 15625000000000000000000000000 : ℚ)⟩
theorem b2684 (b : ℝ) (hb : rootInterval.Contains b) : i2684.Contains (n2684 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2682 b hb) (b2683 b hb))
    (by norm_num [i2684, i2682, i2683, RationalInterval.add]) (by norm_num [i2684, i2682, i2683, RationalInterval.add])

def n2685 (b : ℝ) : ℝ := (n330 b) * (n2055 b)
def i2685 : RationalInterval := ⟨(2207141269096806984942127944389 / 200000000000000000000000000000 : ℚ), (5517863983391505719519773080371 / 500000000000000000000000000000 : ℚ)⟩
theorem b2685 (b : ℝ) (hb : rootInterval.Contains b) : i2685.Contains (n2685 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b330 b hb) (b2055 b hb))
    (by norm_num [i2685, i330, i2055, RationalInterval.mul]) (by norm_num [i2685, i330, i2055, RationalInterval.mul])

def n2686 (b : ℝ) : ℝ := (n2684 b) + (n2685 b)
def i2686 : RationalInterval := ⟨(10609985729528553288926329073813 / 1000000000000000000000000000000 : ℚ), (5305004089297131299194923484819 / 500000000000000000000000000000 : ℚ)⟩
theorem b2686 (b : ℝ) (hb : rootInterval.Contains b) : i2686.Contains (n2686 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2684 b hb) (b2685 b hb))
    (by norm_num [i2686, i2684, i2685, RationalInterval.add]) (by norm_num [i2686, i2684, i2685, RationalInterval.add])

def n2687 (b : ℝ) : ℝ := (n331 b) * (n2100 b)
def i2687 : RationalInterval := ⟨(-1279426141753363003464387504513 / 250000000000000000000000000000 : ℚ), (-204707978595652343374104944987 / 40000000000000000000000000000 : ℚ)⟩
theorem b2687 (b : ℝ) (hb : rootInterval.Contains b) : i2687.Contains (n2687 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b331 b hb) (b2100 b hb))
    (by norm_num [i2687, i331, i2100, RationalInterval.mul]) (by norm_num [i2687, i331, i2100, RationalInterval.mul])

def n2688 (b : ℝ) : ℝ := (n2686 b) + (n2687 b)
def i2688 : RationalInterval := ⟨(5492281162515101275068779055761 / 1000000000000000000000000000000 : ℚ), (5492308713702954014037223344963 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2688 (b : ℝ) (hb : rootInterval.Contains b) : i2688.Contains (n2688 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2686 b hb) (b2687 b hb))
    (by norm_num [i2688, i2686, i2687, RationalInterval.add]) (by norm_num [i2688, i2686, i2687, RationalInterval.add])

def n2689 (b : ℝ) : ℝ := (n2190 b) * (n1990 b)
def i2689 : RationalInterval := ⟨(-327113665447045761827666509503 / 250000000000000000000000000000 : ℚ), (-1308452675833615092460667922789 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2689 (b : ℝ) (hb : rootInterval.Contains b) : i2689.Contains (n2689 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2190 b hb) (b1990 b hb))
    (by norm_num [i2689, i2190, i1990, RationalInterval.mul]) (by norm_num [i2689, i2190, i1990, RationalInterval.mul])

def n2690 (b : ℝ) : ℝ := (n2333 b) * (n2025 b)
def i2690 : RationalInterval := ⟨(78392561323663449267149985479 / 1000000000000000000000000000000 : ℚ), (39196415228639513898522414591 / 500000000000000000000000000000 : ℚ)⟩
theorem b2690 (b : ℝ) (hb : rootInterval.Contains b) : i2690.Contains (n2690 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2333 b hb) (b2025 b hb))
    (by norm_num [i2690, i2333, i2025, RationalInterval.mul]) (by norm_num [i2690, i2333, i2025, RationalInterval.mul])

def n2691 (b : ℝ) : ℝ := (n2689 b) + (n2690 b)
def i2691 : RationalInterval := ⟨(-1230062100464519598043516052533 / 1000000000000000000000000000000 : ℚ), (-1230059845376336064663623093607 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2691 (b : ℝ) (hb : rootInterval.Contains b) : i2691.Contains (n2691 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2689 b hb) (b2690 b hb))
    (by norm_num [i2691, i2689, i2690, RationalInterval.add]) (by norm_num [i2691, i2689, i2690, RationalInterval.add])

def n2692 (b : ℝ) : ℝ := (n330 b) * (n2064 b)
def i2692 : RationalInterval := ⟨(4694139790082792424735231587603 / 200000000000000000000000000000 : ℚ), (4694151797865821667282544635011 / 200000000000000000000000000000 : ℚ)⟩
theorem b2692 (b : ℝ) (hb : rootInterval.Contains b) : i2692.Contains (n2692 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b330 b hb) (b2064 b hb))
    (by norm_num [i2692, i330, i2064, RationalInterval.mul]) (by norm_num [i2692, i330, i2064, RationalInterval.mul])

def n2693 (b : ℝ) : ℝ := (n2691 b) + (n2692 b)
def i2693 : RationalInterval := ⟨(11120318424974721262816320942741 / 500000000000000000000000000000 : ℚ), (2780087392994096533968637510181 / 125000000000000000000000000000 : ℚ)⟩
theorem b2693 (b : ℝ) (hb : rootInterval.Contains b) : i2693.Contains (n2693 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2691 b hb) (b2692 b hb))
    (by norm_num [i2693, i2691, i2692, RationalInterval.add]) (by norm_num [i2693, i2691, i2692, RationalInterval.add])

def n2694 (b : ℝ) : ℝ := (n331 b) * (n2109 b)
def i2694 : RationalInterval := ⟨(-11642699352025725327527252641449 / 1000000000000000000000000000000 : ℚ), (-11642686790217690028894316141467 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2694 (b : ℝ) (hb : rootInterval.Contains b) : i2694.Contains (n2694 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b331 b hb) (b2109 b hb))
    (by norm_num [i2694, i331, i2109, RationalInterval.mul]) (by norm_num [i2694, i331, i2109, RationalInterval.mul])

def n2695 (b : ℝ) : ℝ := (n2693 b) + (n2694 b)
def i2695 : RationalInterval := ⟨(10597937497923717198105389244033 / 1000000000000000000000000000000 : ℚ), (10598012353735082242854783939981 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2695 (b : ℝ) (hb : rootInterval.Contains b) : i2695.Contains (n2695 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2693 b hb) (b2694 b hb))
    (by norm_num [i2695, i2693, i2694, RationalInterval.add]) (by norm_num [i2695, i2693, i2694, RationalInterval.add])

def n2696 (b : ℝ) : ℝ := (n2190 b) * (n1997 b)
def i2696 : RationalInterval := ⟨(1544108235748572508506662349539 / 250000000000000000000000000000 : ℚ), (308821759588632809730777970507 / 50000000000000000000000000000 : ℚ)⟩
theorem b2696 (b : ℝ) (hb : rootInterval.Contains b) : i2696.Contains (n2696 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2190 b hb) (b1997 b hb))
    (by norm_num [i2696, i2190, i1997, RationalInterval.mul]) (by norm_num [i2696, i2190, i1997, RationalInterval.mul])

def n2697 (b : ℝ) : ℝ := (n2333 b) * (n2032 b)
def i2697 : RationalInterval := ⟨(-904953230773403039510508000301 / 1000000000000000000000000000000 : ℚ), (-452476463246537696694618542363 / 500000000000000000000000000000 : ℚ)⟩
theorem b2697 (b : ℝ) (hb : rootInterval.Contains b) : i2697.Contains (n2697 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2333 b hb) (b2032 b hb))
    (by norm_num [i2697, i2333, i2032, RationalInterval.mul]) (by norm_num [i2697, i2333, i2032, RationalInterval.mul])

def n2698 (b : ℝ) : ℝ := (n2696 b) + (n2697 b)
def i2698 : RationalInterval := ⟨(1054295942444177398903228279571 / 200000000000000000000000000000 : ℚ), (2635741132639790400613161162707 / 500000000000000000000000000000 : ℚ)⟩
theorem b2698 (b : ℝ) (hb : rootInterval.Contains b) : i2698.Contains (n2698 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2696 b hb) (b2697 b hb))
    (by norm_num [i2698, i2696, i2697, RationalInterval.add]) (by norm_num [i2698, i2696, i2697, RationalInterval.add])

def n2699 (b : ℝ) : ℝ := (n330 b) * (n2073 b)
def i2699 : RationalInterval := ⟨(-55193473378651360354247609050039 / 500000000000000000000000000000 : ℚ), (-110386835141183329557574006161771 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2699 (b : ℝ) (hb : rootInterval.Contains b) : i2699.Contains (n2699 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b330 b hb) (b2073 b hb))
    (by norm_num [i2699, i330, i2073, RationalInterval.mul]) (by norm_num [i2699, i330, i2073, RationalInterval.mul])

