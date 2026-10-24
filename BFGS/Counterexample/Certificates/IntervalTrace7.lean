import BFGS.Counterexample.Certificates.IntervalTrace6

/-! Generated arithmetic proofs. Each bound is checked by the Lean kernel. -/
namespace BFGS.Counterexample.Trace
noncomputable section
open BFGS RationalInterval
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false

def n630 (b : ℝ) : ℝ := (n600 b) * (n581 b)
def i630 : RationalInterval := ⟨(108120018321876917365531711281 / 1000000000000000000000000000000 : ℚ), (27030004621209227517914989683 / 250000000000000000000000000000 : ℚ)⟩
theorem b630 (b : ℝ) (hb : rootInterval.Contains b) : i630.Contains (n630 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b600 b hb) (b581 b hb))
    (by norm_num [i630, i600, i581, RationalInterval.mul]) (by norm_num [i630, i600, i581, RationalInterval.mul])

def n631 (b : ℝ) : ℝ := (n600 b) * (n582 b)
def i631 : RationalInterval := ⟨(40130461373654485882476006037 / 1000000000000000000000000000000 : ℚ), (20065230733330894399166994959 / 500000000000000000000000000000 : ℚ)⟩
theorem b631 (b : ℝ) (hb : rootInterval.Contains b) : i631.Contains (n631 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b600 b hb) (b582 b hb))
    (by norm_num [i631, i600, i582, RationalInterval.mul]) (by norm_num [i631, i600, i582, RationalInterval.mul])

def n632 (b : ℝ) : ℝ := (n626 b) + (n617 b)
def i632 : RationalInterval := ⟨(685476715322882803043823236539 / 1000000000000000000000000000000 : ℚ), (171369179948463326625647578967 / 250000000000000000000000000000 : ℚ)⟩
theorem b632 (b : ℝ) (hb : rootInterval.Contains b) : i632.Contains (n632 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b626 b hb) (b617 b hb))
    (by norm_num [i632, i626, i617, RationalInterval.add]) (by norm_num [i632, i626, i617, RationalInterval.add])

def n633 (b : ℝ) : ℝ := (n627 b) + (n619 b)
def i633 : RationalInterval := ⟨(294886085523633592433799269093 / 1000000000000000000000000000000 : ℚ), (73721521949885154142596121279 / 250000000000000000000000000000 : ℚ)⟩
theorem b633 (b : ℝ) (hb : rootInterval.Contains b) : i633.Contains (n633 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b627 b hb) (b619 b hb))
    (by norm_num [i633, i627, i619, RationalInterval.add]) (by norm_num [i633, i627, i619, RationalInterval.add])

def n634 (b : ℝ) : ℝ := (n628 b) + (n630 b)
def i634 : RationalInterval := ⟨(91399843919800605797492281789 / 500000000000000000000000000000 : ℚ), (182799690123323796469109137451 / 1000000000000000000000000000000 : ℚ)⟩
theorem b634 (b : ℝ) (hb : rootInterval.Contains b) : i634.Contains (n634 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b628 b hb) (b630 b hb))
    (by norm_num [i634, i628, i630, RationalInterval.add]) (by norm_num [i634, i628, i630, RationalInterval.add])

def n635 (b : ℝ) : ℝ := (n629 b) + (n631 b)
def i635 : RationalInterval := ⟨(15494059226503326599440486437 / 200000000000000000000000000000 : ℚ), (38735148642952615998529289639 / 500000000000000000000000000000 : ℚ)⟩
theorem b635 (b : ℝ) (hb : rootInterval.Contains b) : i635.Contains (n635 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b629 b hb) (b631 b hb))
    (by norm_num [i635, i629, i631, RationalInterval.add]) (by norm_num [i635, i629, i631, RationalInterval.add])

def n636 (b : ℝ) : ℝ := (n581 b) * (n600 b)
def i636 : RationalInterval := ⟨(108120018321876917365531711281 / 1000000000000000000000000000000 : ℚ), (27030004621209227517914989683 / 250000000000000000000000000000 : ℚ)⟩
theorem b636 (b : ℝ) (hb : rootInterval.Contains b) : i636.Contains (n636 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b581 b hb) (b600 b hb))
    (by norm_num [i636, i581, i600, RationalInterval.mul]) (by norm_num [i636, i581, i600, RationalInterval.mul])

def n637 (b : ℝ) : ℝ := (n582 b) * (n600 b)
def i637 : RationalInterval := ⟨(40130461373654485882476006037 / 1000000000000000000000000000000 : ℚ), (20065230733330894399166994959 / 500000000000000000000000000000 : ℚ)⟩
theorem b637 (b : ℝ) (hb : rootInterval.Contains b) : i637.Contains (n637 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b582 b hb) (b600 b hb))
    (by norm_num [i637, i582, i600, RationalInterval.mul]) (by norm_num [i637, i582, i600, RationalInterval.mul])

def n638 (b : ℝ) : ℝ := (n152 b) * (n609 b)
def i638 : RationalInterval := ⟨(157025633196463552238848729877 / 1000000000000000000000000000000 : ℚ), (15702563515522990835740634333 / 100000000000000000000000000000 : ℚ)⟩
theorem b638 (b : ℝ) (hb : rootInterval.Contains b) : i638.Contains (n638 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b152 b hb) (b609 b hb))
    (by norm_num [i638, i152, i609, RationalInterval.mul]) (by norm_num [i638, i152, i609, RationalInterval.mul])

def n639 (b : ℝ) : ℝ := (n152 b) * (n612 b)
def i639 : RationalInterval := ⟨(9334958689715536778681606537 / 250000000000000000000000000000 : ℚ), (466747947740543039984057367 / 12500000000000000000000000000 : ℚ)⟩
theorem b639 (b : ℝ) (hb : rootInterval.Contains b) : i639.Contains (n639 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b152 b hb) (b612 b hb))
    (by norm_num [i639, i152, i612, RationalInterval.mul]) (by norm_num [i639, i152, i612, RationalInterval.mul])

def n640 (b : ℝ) : ℝ := (n617 b) + (n626 b)
def i640 : RationalInterval := ⟨(685476715322882803043823236539 / 1000000000000000000000000000000 : ℚ), (171369179948463326625647578967 / 250000000000000000000000000000 : ℚ)⟩
theorem b640 (b : ℝ) (hb : rootInterval.Contains b) : i640.Contains (n640 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b617 b hb) (b626 b hb))
    (by norm_num [i640, i617, i626, RationalInterval.add]) (by norm_num [i640, i617, i626, RationalInterval.add])

def n641 (b : ℝ) : ℝ := (n636 b) + (n628 b)
def i641 : RationalInterval := ⟨(91399843919800605797492281789 / 500000000000000000000000000000 : ℚ), (182799690123323796469109137451 / 1000000000000000000000000000000 : ℚ)⟩
theorem b641 (b : ℝ) (hb : rootInterval.Contains b) : i641.Contains (n641 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b636 b hb) (b628 b hb))
    (by norm_num [i641, i636, i628, RationalInterval.add]) (by norm_num [i641, i636, i628, RationalInterval.add])

def n642 (b : ℝ) : ℝ := (n619 b) + (n638 b)
def i642 : RationalInterval := ⟨(294886085523633592433799269093 / 1000000000000000000000000000000 : ℚ), (73721521949885154142596121279 / 250000000000000000000000000000 : ℚ)⟩
theorem b642 (b : ℝ) (hb : rootInterval.Contains b) : i642.Contains (n642 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b619 b hb) (b638 b hb))
    (by norm_num [i642, i619, i638, RationalInterval.add]) (by norm_num [i642, i619, i638, RationalInterval.add])

def n643 (b : ℝ) : ℝ := (n637 b) + (n639 b)
def i643 : RationalInterval := ⟨(15494059226503326599440486437 / 200000000000000000000000000000 : ℚ), (38735148642952615998529289639 / 500000000000000000000000000000 : ℚ)⟩
theorem b643 (b : ℝ) (hb : rootInterval.Contains b) : i643.Contains (n643 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b637 b hb) (b639 b hb))
    (by norm_num [i643, i637, i639, RationalInterval.add]) (by norm_num [i643, i637, i639, RationalInterval.add])

def n644 (b : ℝ) : ℝ := (n632 b) + (n640 b)
def i644 : RationalInterval := ⟨(685476715322882803043823236539 / 500000000000000000000000000000 : ℚ), (171369179948463326625647578967 / 125000000000000000000000000000 : ℚ)⟩
theorem b644 (b : ℝ) (hb : rootInterval.Contains b) : i644.Contains (n644 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b632 b hb) (b640 b hb))
    (by norm_num [i644, i632, i640, RationalInterval.add]) (by norm_num [i644, i632, i640, RationalInterval.add])

def n645 (b : ℝ) : ℝ := (n633 b) + (n641 b)
def i645 : RationalInterval := ⟨(477685773363234804028783832671 / 1000000000000000000000000000000 : ℚ), (477685777922864413039493622567 / 1000000000000000000000000000000 : ℚ)⟩
theorem b645 (b : ℝ) (hb : rootInterval.Contains b) : i645.Contains (n645 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b633 b hb) (b641 b hb))
    (by norm_num [i645, i633, i641, RationalInterval.add]) (by norm_num [i645, i633, i641, RationalInterval.add])

def n646 (b : ℝ) : ℝ := (n634 b) + (n642 b)
def i646 : RationalInterval := ⟨(477685773363234804028783832671 / 1000000000000000000000000000000 : ℚ), (477685777922864413039493622567 / 1000000000000000000000000000000 : ℚ)⟩
theorem b646 (b : ℝ) (hb : rootInterval.Contains b) : i646.Contains (n646 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b634 b hb) (b642 b hb))
    (by norm_num [i646, i634, i642, RationalInterval.add]) (by norm_num [i646, i634, i642, RationalInterval.add])

def n647 (b : ℝ) : ℝ := (n635 b) + (n643 b)
def i647 : RationalInterval := ⟨(15494059226503326599440486437 / 100000000000000000000000000000 : ℚ), (38735148642952615998529289639 / 250000000000000000000000000000 : ℚ)⟩
theorem b647 (b : ℝ) (hb : rootInterval.Contains b) : i647.Contains (n647 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b635 b hb) (b643 b hb))
    (by norm_num [i647, i635, i643, RationalInterval.add]) (by norm_num [i647, i635, i643, RationalInterval.add])

def n648 (b : ℝ) : ℝ := (n413 b) * (n644 b)
def i648 : RationalInterval := ⟨(-171369179948463326625647578967 / 62500000000000000000000000000 : ℚ), (-685476715322882803043823236539 / 250000000000000000000000000000 : ℚ)⟩
theorem b648 (b : ℝ) (hb : rootInterval.Contains b) : i648.Contains (n648 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b413 b hb) (b644 b hb))
    (by norm_num [i648, i413, i644, RationalInterval.mul]) (by norm_num [i648, i413, i644, RationalInterval.mul])

def n649 (b : ℝ) : ℝ := (n413 b) * (n645 b)
def i649 : RationalInterval := ⟨(-477685777922864413039493622567 / 500000000000000000000000000000 : ℚ), (-477685773363234804028783832671 / 500000000000000000000000000000 : ℚ)⟩
theorem b649 (b : ℝ) (hb : rootInterval.Contains b) : i649.Contains (n649 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b413 b hb) (b645 b hb))
    (by norm_num [i649, i413, i645, RationalInterval.mul]) (by norm_num [i649, i413, i645, RationalInterval.mul])

def n650 (b : ℝ) : ℝ := (n413 b) * (n646 b)
def i650 : RationalInterval := ⟨(-477685777922864413039493622567 / 500000000000000000000000000000 : ℚ), (-477685773363234804028783832671 / 500000000000000000000000000000 : ℚ)⟩
theorem b650 (b : ℝ) (hb : rootInterval.Contains b) : i650.Contains (n650 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b413 b hb) (b646 b hb))
    (by norm_num [i650, i413, i646, RationalInterval.mul]) (by norm_num [i650, i413, i646, RationalInterval.mul])

def n651 (b : ℝ) : ℝ := (n413 b) * (n647 b)
def i651 : RationalInterval := ⟨(-38735148642952615998529289639 / 125000000000000000000000000000 : ℚ), (-15494059226503326599440486437 / 50000000000000000000000000000 : ℚ)⟩
theorem b651 (b : ℝ) (hb : rootInterval.Contains b) : i651.Contains (n651 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b413 b hb) (b647 b hb))
    (by norm_num [i651, i413, i647, RationalInterval.mul]) (by norm_num [i651, i413, i647, RationalInterval.mul])

def n652 (b : ℝ) : ℝ := (n599 b) * (n57 b)
def i652 : RationalInterval := ⟨(97647657370527135647999091219 / 31250000000000000000000000000 : ℚ), (781181264622906715900466866643 / 250000000000000000000000000000 : ℚ)⟩
theorem b652 (b : ℝ) (hb : rootInterval.Contains b) : i652.Contains (n652 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b599 b hb) (b57 b hb))
    (by norm_num [i652, i599, i57, RationalInterval.mul]) (by norm_num [i652, i599, i57, RationalInterval.mul])

def n653 (b : ℝ) : ℝ := (n652 b) * (n605 b)
def i653 : RationalInterval := ⟨(49439074806838182266865601791 / 40000000000000000000000000000 : ℚ), (308994219782971574978843364119 / 250000000000000000000000000000 : ℚ)⟩
theorem b653 (b : ℝ) (hb : rootInterval.Contains b) : i653.Contains (n653 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b652 b hb) (b605 b hb))
    (by norm_num [i653, i652, i605, RationalInterval.mul]) (by norm_num [i653, i652, i605, RationalInterval.mul])

def n654 (b : ℝ) : ℝ := (n652 b) * (n606 b)
def i654 : RationalInterval := ⟨(49439074806838182266865601791 / 40000000000000000000000000000 : ℚ), (308994219782971574978843364119 / 250000000000000000000000000000 : ℚ)⟩
theorem b654 (b : ℝ) (hb : rootInterval.Contains b) : i654.Contains (n654 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b652 b hb) (b606 b hb))
    (by norm_num [i654, i652, i606, RationalInterval.mul]) (by norm_num [i654, i652, i606, RationalInterval.mul])

def n655 (b : ℝ) : ℝ := (n652 b) * (n607 b)
def i655 : RationalInterval := ⟨(454795611206737471487647315023 / 1000000000000000000000000000000 : ℚ), (454795614508979584014906589833 / 1000000000000000000000000000000 : ℚ)⟩
theorem b655 (b : ℝ) (hb : rootInterval.Contains b) : i655.Contains (n655 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b652 b hb) (b607 b hb))
    (by norm_num [i655, i652, i607, RationalInterval.mul]) (by norm_num [i655, i652, i607, RationalInterval.mul])

def n656 (b : ℝ) : ℝ := (n648 b) + (n652 b)
def i656 : RationalInterval := ⟨(23926134792590944670350603471 / 62500000000000000000000000000 : ℚ), (11963068662502989107080453763 / 31250000000000000000000000000 : ℚ)⟩
theorem b656 (b : ℝ) (hb : rootInterval.Contains b) : i656.Contains (n656 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b648 b hb) (b652 b hb))
    (by norm_num [i656, i648, i652, RationalInterval.add]) (by norm_num [i656, i648, i652, RationalInterval.add])

def n657 (b : ℝ) : ℝ := (n649 b) + (n653 b)
def i657 : RationalInterval := ⟨(280605314325225730592652799641 / 1000000000000000000000000000000 : ℚ), (140302666202708345928902895567 / 500000000000000000000000000000 : ℚ)⟩
theorem b657 (b : ℝ) (hb : rootInterval.Contains b) : i657.Contains (n657 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b649 b hb) (b653 b hb))
    (by norm_num [i657, i649, i653, RationalInterval.add]) (by norm_num [i657, i649, i653, RationalInterval.add])

def n658 (b : ℝ) : ℝ := (n650 b) + (n654 b)
def i658 : RationalInterval := ⟨(280605314325225730592652799641 / 1000000000000000000000000000000 : ℚ), (140302666202708345928902895567 / 500000000000000000000000000000 : ℚ)⟩
theorem b658 (b : ℝ) (hb : rootInterval.Contains b) : i658.Contains (n658 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b650 b hb) (b654 b hb))
    (by norm_num [i658, i650, i654, RationalInterval.add]) (by norm_num [i658, i650, i654, RationalInterval.add])

def n659 (b : ℝ) : ℝ := (n651 b) + (n655 b)
def i659 : RationalInterval := ⟨(144914422063116543499412997911 / 1000000000000000000000000000000 : ℚ), (144914429978913052026096861093 / 1000000000000000000000000000000 : ℚ)⟩
theorem b659 (b : ℝ) (hb : rootInterval.Contains b) : i659.Contains (n659 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b651 b hb) (b655 b hb))
    (by norm_num [i659, i651, i655, RationalInterval.add]) (by norm_num [i659, i651, i655, RationalInterval.add])

def n660 (b : ℝ) : ℝ := (n599 b) + (n616 b)
def i660 : RationalInterval := ⟨(629962226355340459695301664119 / 500000000000000000000000000000 : ℚ), (251984892394158872563482461851 / 200000000000000000000000000000 : ℚ)⟩
theorem b660 (b : ℝ) (hb : rootInterval.Contains b) : i660.Contains (n660 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b599 b hb) (b616 b hb))
    (by norm_num [i660, i599, i616, RationalInterval.add]) (by norm_num [i660, i599, i616, RationalInterval.add])

def n661 (b : ℝ) : ℝ := (n660 b) * (n57 b)
def i661 : RationalInterval := ⟨(629962226355340459695301664119 / 125000000000000000000000000000 : ℚ), (251984892394158872563482461851 / 50000000000000000000000000000 : ℚ)⟩
theorem b661 (b : ℝ) (hb : rootInterval.Contains b) : i661.Contains (n661 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b660 b hb) (b57 b hb))
    (by norm_num [i661, i660, i57, RationalInterval.mul]) (by norm_num [i661, i660, i57, RationalInterval.mul])

def n662 (b : ℝ) : ℝ := (n64 b) + (n601 b)
def i662 : RationalInterval := ⟨(85445259791 / 100000000000 : ℚ), (68356207833 / 80000000000 : ℚ)⟩
theorem b662 (b : ℝ) (hb : rootInterval.Contains b) : i662.Contains (n662 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b64 b hb) (b601 b hb))
    (by norm_num [i662, i64, i601, RationalInterval.add]) (by norm_num [i662, i64, i601, RationalInterval.add])

def n663 (b : ℝ) : ℝ := (n662 b) * (n13 b)
def i663 : RationalInterval := ⟨(85445259791 / 50000000000 : ℚ), (68356207833 / 40000000000 : ℚ)⟩
theorem b663 (b : ℝ) (hb : rootInterval.Contains b) : i663.Contains (n663 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b662 b hb) (b13 b hb))
    (by norm_num [i663, i662, i13, RationalInterval.mul]) (by norm_num [i663, i662, i13, RationalInterval.mul])

def n664 (b : ℝ) : ℝ := (n663 b) * (n599 b)
def i664 : RationalInterval := ⟨(667482356160579764164670358283 / 500000000000000000000000000000 : ℚ), (26699294439904590922331899439 / 20000000000000000000000000000 : ℚ)⟩
theorem b664 (b : ℝ) (hb : rootInterval.Contains b) : i664.Contains (n664 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b663 b hb) (b599 b hb))
    (by norm_num [i664, i663, i599, RationalInterval.mul]) (by norm_num [i664, i663, i599, RationalInterval.mul])

def n665 (b : ℝ) : ℝ := ((8 : ℚ) : ℝ)
def i665 : RationalInterval := ⟨(8 : ℚ), (8 : ℚ)⟩
theorem b665 (b : ℝ) (hb : rootInterval.Contains b) : i665.Contains (n665 b) := by
  exact RationalInterval.contains_point (8 : ℚ)

def n666 (b : ℝ) : ℝ := (n664 b) * (n665 b)
def i666 : RationalInterval := ⟨(667482356160579764164670358283 / 62500000000000000000000000000 : ℚ), (26699294439904590922331899439 / 2500000000000000000000000000 : ℚ)⟩
theorem b666 (b : ℝ) (hb : rootInterval.Contains b) : i666.Contains (n666 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b664 b hb) (b665 b hb))
    (by norm_num [i666, i664, i665, RationalInterval.mul]) (by norm_num [i666, i664, i665, RationalInterval.mul])

def n667 (b : ℝ) : ℝ := -(n666 b)
def i667 : RationalInterval := ⟨(-26699294439904590922331899439 / 2500000000000000000000000000 : ℚ), (-667482356160579764164670358283 / 62500000000000000000000000000 : ℚ)⟩
theorem b667 (b : ℝ) (hb : rootInterval.Contains b) : i667.Contains (n667 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b666 b hb))
    (by norm_num [i667, i666, RationalInterval.neg]) (by norm_num [i667, i666, RationalInterval.neg])

def n668 (b : ℝ) : ℝ := (n661 b) + (n667 b)
def i668 : RationalInterval := ⟨(-705002495639889086421293307831 / 125000000000000000000000000000 : ℚ), (-1410004962671524693841269123877 / 250000000000000000000000000000 : ℚ)⟩
theorem b668 (b : ℝ) (hb : rootInterval.Contains b) : i668.Contains (n668 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b661 b hb) (b667 b hb))
    (by norm_num [i668, i661, i667, RationalInterval.add]) (by norm_num [i668, i661, i667, RationalInterval.add])

def n669 (b : ℝ) : ℝ := (n668 b) * (n64 b)
def i669 : RationalInterval := ⟨(-705002495639889086421293307831 / 250000000000000000000000000000 : ℚ), (-1410004962671524693841269123877 / 500000000000000000000000000000 : ℚ)⟩
theorem b669 (b : ℝ) (hb : rootInterval.Contains b) : i669.Contains (n669 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b668 b hb) (b64 b hb))
    (by norm_num [i669, i668, i64, RationalInterval.mul]) (by norm_num [i669, i668, i64, RationalInterval.mul])

def n670 (b : ℝ) : ℝ := (n668 b) * (n58 b)
def i670 : RationalInterval := ⟨(-705002495639889086421293307831 / 500000000000000000000000000000 : ℚ), (-1410004962671524693841269123877 / 1000000000000000000000000000000 : ℚ)⟩
theorem b670 (b : ℝ) (hb : rootInterval.Contains b) : i670.Contains (n670 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b668 b hb) (b58 b hb))
    (by norm_num [i670, i668, i58, RationalInterval.mul]) (by norm_num [i670, i668, i58, RationalInterval.mul])

def n671 (b : ℝ) : ℝ := (n656 b) + (n668 b)
def i671 : RationalInterval := ⟨(-657150226054707197080592100889 / 125000000000000000000000000000 : ℚ), (-1314300413371500780984625493773 / 250000000000000000000000000000 : ℚ)⟩
theorem b671 (b : ℝ) (hb : rootInterval.Contains b) : i671.Contains (n671 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b656 b hb) (b668 b hb))
    (by norm_num [i671, i656, i668, RationalInterval.add]) (by norm_num [i671, i656, i668, RationalInterval.add])

def n672 (b : ℝ) : ℝ := (n657 b) + (n669 b)
def i672 : RationalInterval := ⟨(-2539404668234330615092520431683 / 1000000000000000000000000000000 : ℚ), (-126970229646881634791236622831 / 50000000000000000000000000000 : ℚ)⟩
theorem b672 (b : ℝ) (hb : rootInterval.Contains b) : i672.Contains (n672 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b657 b hb) (b669 b hb))
    (by norm_num [i672, i657, i669, RationalInterval.add]) (by norm_num [i672, i657, i669, RationalInterval.add])

def n673 (b : ℝ) : ℝ := (n658 b) + (n669 b)
def i673 : RationalInterval := ⟨(-2539404668234330615092520431683 / 1000000000000000000000000000000 : ℚ), (-126970229646881634791236622831 / 50000000000000000000000000000 : ℚ)⟩
theorem b673 (b : ℝ) (hb : rootInterval.Contains b) : i673.Contains (n673 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b658 b hb) (b669 b hb))
    (by norm_num [i673, i658, i669, RationalInterval.add]) (by norm_num [i673, i658, i669, RationalInterval.add])

def n674 (b : ℝ) : ℝ := (n659 b) + (n670 b)
def i674 : RationalInterval := ⟨(-1265090569216661629343173617751 / 1000000000000000000000000000000 : ℚ), (-9883519786661028451681033303 / 7812500000000000000000000000 : ℚ)⟩
theorem b674 (b : ℝ) (hb : rootInterval.Contains b) : i674.Contains (n674 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b659 b hb) (b670 b hb))
    (by norm_num [i674, i659, i670, RationalInterval.add]) (by norm_num [i674, i659, i670, RationalInterval.add])

def n675 (b : ℝ) : ℝ := (n662 b) * (n57 b)
def i675 : RationalInterval := ⟨(85445259791 / 25000000000 : ℚ), (68356207833 / 20000000000 : ℚ)⟩
theorem b675 (b : ℝ) (hb : rootInterval.Contains b) : i675.Contains (n675 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b662 b hb) (b57 b hb))
    (by norm_num [i675, i662, i57, RationalInterval.mul]) (by norm_num [i675, i662, i57, RationalInterval.mul])

def n676 (b : ℝ) : ℝ := (n675 b) * (n622 b)
def i676 : RationalInterval := ⟨(101556940725788376403531210207 / 20000000000000000000000000000 : ℚ), (5077847043870457574010498137067 / 1000000000000000000000000000000 : ℚ)⟩
theorem b676 (b : ℝ) (hb : rootInterval.Contains b) : i676.Contains (n676 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b675 b hb) (b622 b hb))
    (by norm_num [i676, i675, i622, RationalInterval.mul]) (by norm_num [i676, i675, i622, RationalInterval.mul])

def n677 (b : ℝ) : ℝ := (n675 b) * (n623 b)
def i677 : RationalInterval := ⟨(2211823532192339874027297016367 / 1000000000000000000000000000000 : ℚ), (442364707251642022613199984609 / 200000000000000000000000000000 : ℚ)⟩
theorem b677 (b : ℝ) (hb : rootInterval.Contains b) : i677.Contains (n677 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b675 b hb) (b623 b hb))
    (by norm_num [i677, i675, i623, RationalInterval.mul]) (by norm_num [i677, i675, i623, RationalInterval.mul])

def n678 (b : ℝ) : ℝ := (n675 b) * (n624 b)
def i678 : RationalInterval := ⟨(2211823532192339874027297016367 / 1000000000000000000000000000000 : ℚ), (442364707251642022613199984609 / 200000000000000000000000000000 : ℚ)⟩
theorem b678 (b : ℝ) (hb : rootInterval.Contains b) : i678.Contains (n678 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b675 b hb) (b624 b hb))
    (by norm_num [i678, i675, i624, RationalInterval.mul]) (by norm_num [i678, i675, i624, RationalInterval.mul])

def n679 (b : ℝ) : ℝ := (n675 b) * (n625 b)
def i679 : RationalInterval := ⟨(117795221639998146122894611097 / 125000000000000000000000000000 : ℚ), (942361775290595719563375388781 / 1000000000000000000000000000000 : ℚ)⟩
theorem b679 (b : ℝ) (hb : rootInterval.Contains b) : i679.Contains (n679 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b675 b hb) (b625 b hb))
    (by norm_num [i679, i675, i625, RationalInterval.mul]) (by norm_num [i679, i675, i625, RationalInterval.mul])

def n680 (b : ℝ) : ℝ := (n671 b) + (n676 b)
def i680 : RationalInterval := ⟨(-89677386074119378234088148381 / 500000000000000000000000000000 : ℚ), (-7174184384621821997120153521 / 40000000000000000000000000000 : ℚ)⟩
theorem b680 (b : ℝ) (hb : rootInterval.Contains b) : i680.Contains (n680 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b671 b hb) (b676 b hb))
    (by norm_num [i680, i671, i676, RationalInterval.add]) (by norm_num [i680, i671, i676, RationalInterval.add])

def n681 (b : ℝ) : ℝ := (n672 b) + (n677 b)
def i681 : RationalInterval := ⟨(-81895284010497685266305853829 / 250000000000000000000000000000 : ℚ), (-13103242267176903310349301343 / 40000000000000000000000000000 : ℚ)⟩
theorem b681 (b : ℝ) (hb : rootInterval.Contains b) : i681.Contains (n681 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b672 b hb) (b677 b hb))
    (by norm_num [i681, i672, i677, RationalInterval.add]) (by norm_num [i681, i672, i677, RationalInterval.add])

def n682 (b : ℝ) : ℝ := (n673 b) + (n678 b)
def i682 : RationalInterval := ⟨(-81895284010497685266305853829 / 250000000000000000000000000000 : ℚ), (-13103242267176903310349301343 / 40000000000000000000000000000 : ℚ)⟩
theorem b682 (b : ℝ) (hb : rootInterval.Contains b) : i682.Contains (n682 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b673 b hb) (b678 b hb))
    (by norm_num [i682, i673, i678, RationalInterval.add]) (by norm_num [i682, i673, i678, RationalInterval.add])

def n683 (b : ℝ) : ℝ := (n674 b) + (n679 b)
def i683 : RationalInterval := ⟨(-12909151843867058414400669159 / 40000000000000000000000000000 : ℚ), (-322728757402015922251796874003 / 1000000000000000000000000000000 : ℚ)⟩
theorem b683 (b : ℝ) (hb : rootInterval.Contains b) : i683.Contains (n683 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b674 b hb) (b679 b hb))
    (by norm_num [i683, i674, i679, RationalInterval.add]) (by norm_num [i683, i674, i679, RationalInterval.add])

def n684 (b : ℝ) : ℝ := (n185 b) * (n64 b)
def i684 : RationalInterval := ⟨(349512406278889995784120842581 / 1000000000000000000000000000000 : ℚ), (34951240663994373113002814689 / 100000000000000000000000000000 : ℚ)⟩
theorem b684 (b : ℝ) (hb : rootInterval.Contains b) : i684.Contains (n684 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b185 b hb) (b64 b hb))
    (by norm_num [i684, i185, i64, RationalInterval.mul]) (by norm_num [i684, i185, i64, RationalInterval.mul])

def n685 (b : ℝ) : ℝ := (n183 b) + (n684 b)
def i685 : RationalInterval := ⟨(-283368085716383024336714597979 / 500000000000000000000000000000 : ℚ), (-283368085159834281947881930299 / 500000000000000000000000000000 : ℚ)⟩
theorem b685 (b : ℝ) (hb : rootInterval.Contains b) : i685.Contains (n685 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b183 b hb) (b684 b hb))
    (by norm_num [i685, i183, i684, RationalInterval.add]) (by norm_num [i685, i183, i684, RationalInterval.add])

def n686 (b : ℝ) : ℝ := (n183 b) * (n64 b)
def i686 : RationalInterval := ⟨(-45812428885582802222877501927 / 100000000000000000000000000000 : ℚ), (-14316384014993942109778000117 / 31250000000000000000000000000 : ℚ)⟩
theorem b686 (b : ℝ) (hb : rootInterval.Contains b) : i686.Contains (n686 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b183 b hb) (b64 b hb))
    (by norm_num [i686, i183, i64, RationalInterval.mul]) (by norm_num [i686, i183, i64, RationalInterval.mul])

def n687 (b : ℝ) : ℝ := (n61 b) * (n185 b)
def i687 : RationalInterval := ⟨(61942790203663977498395290089 / 250000000000000000000000000000 : ℚ), (247771161072356340983713752009 / 1000000000000000000000000000000 : ℚ)⟩
theorem b687 (b : ℝ) (hb : rootInterval.Contains b) : i687.Contains (n687 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b61 b hb) (b185 b hb))
    (by norm_num [i687, i61, i185, RationalInterval.mul]) (by norm_num [i687, i61, i185, RationalInterval.mul])

def n688 (b : ℝ) : ℝ := (n686 b) + (n687 b)
def i688 : RationalInterval := ⟨(-105176564020586056117596929457 / 500000000000000000000000000000 : ℚ), (-42070625481489961305836450347 / 200000000000000000000000000000 : ℚ)⟩
theorem b688 (b : ℝ) (hb : rootInterval.Contains b) : i688.Contains (n688 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b686 b hb) (b687 b hb))
    (by norm_num [i688, i686, i687, RationalInterval.add]) (by norm_num [i688, i686, i687, RationalInterval.add])

def n689 (b : ℝ) : ℝ := -(n685 b)
def i689 : RationalInterval := ⟨(283368085159834281947881930299 / 500000000000000000000000000000 : ℚ), (283368085716383024336714597979 / 500000000000000000000000000000 : ℚ)⟩
theorem b689 (b : ℝ) (hb : rootInterval.Contains b) : i689.Contains (n689 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b685 b hb))
    (by norm_num [i689, i685, RationalInterval.neg]) (by norm_num [i689, i685, RationalInterval.neg])

def n690 (b : ℝ) : ℝ := -(n688 b)
def i690 : RationalInterval := ⟨(42070625481489961305836450347 / 200000000000000000000000000000 : ℚ), (105176564020586056117596929457 / 500000000000000000000000000000 : ℚ)⟩
theorem b690 (b : ℝ) (hb : rootInterval.Contains b) : i690.Contains (n690 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b688 b hb))
    (by norm_num [i690, i688, RationalInterval.neg]) (by norm_num [i690, i688, RationalInterval.neg])

def n691 (b : ℝ) : ℝ := (n690 b) + (n15 b)
def i691 : RationalInterval := ⟨(242070625481489961305836450347 / 200000000000000000000000000000 : ℚ), (605176564020586056117596929457 / 500000000000000000000000000000 : ℚ)⟩
theorem b691 (b : ℝ) (hb : rootInterval.Contains b) : i691.Contains (n691 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b690 b hb) (b15 b hb))
    (by norm_num [i691, i690, i15, RationalInterval.add]) (by norm_num [i691, i690, i15, RationalInterval.add])

def n692 (b : ℝ) : ℝ := (n196 b) * (n689 b)
def i692 : RationalInterval := ⟨(169909542639267796405456203969 / 200000000000000000000000000000 : ℚ), (424773857766404258274483928737 / 500000000000000000000000000000 : ℚ)⟩
theorem b692 (b : ℝ) (hb : rootInterval.Contains b) : i692.Contains (n692 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b196 b hb) (b689 b hb))
    (by norm_num [i692, i196, i689, RationalInterval.mul]) (by norm_num [i692, i196, i689, RationalInterval.mul])

def n693 (b : ℝ) : ℝ := (n197 b) * (n691 b)
def i693 : RationalInterval := ⟨(-470909584792102277114883378337 / 1000000000000000000000000000000 : ℚ), (-470909583616678583464466182647 / 1000000000000000000000000000000 : ℚ)⟩
theorem b693 (b : ℝ) (hb : rootInterval.Contains b) : i693.Contains (n693 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b197 b hb) (b691 b hb))
    (by norm_num [i693, i197, i691, RationalInterval.mul]) (by norm_num [i693, i197, i691, RationalInterval.mul])

def n694 (b : ℝ) : ℝ := (n692 b) + (n693 b)
def i694 : RationalInterval := ⟨(94659532101059176228099410377 / 250000000000000000000000000000 : ℚ), (378638131916129933084501674827 / 1000000000000000000000000000000 : ℚ)⟩
theorem b694 (b : ℝ) (hb : rootInterval.Contains b) : i694.Contains (n694 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b692 b hb) (b693 b hb))
    (by norm_num [i694, i692, i693, RationalInterval.add]) (by norm_num [i694, i692, i693, RationalInterval.add])

def n695 (b : ℝ) : ℝ := (n198 b) * (n689 b)
def i695 : RationalInterval := ⟨(-220498868464932121615685837217 / 1000000000000000000000000000000 : ℚ), (-55124716899232652185088194861 / 250000000000000000000000000000 : ℚ)⟩
theorem b695 (b : ℝ) (hb : rootInterval.Contains b) : i695.Contains (n695 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b198 b hb) (b689 b hb))
    (by norm_num [i695, i198, i689, RationalInterval.mul]) (by norm_num [i695, i198, i689, RationalInterval.mul])

def n696 (b : ℝ) : ℝ := (n199 b) * (n691 b)
def i696 : RationalInterval := ⟨(15277986791546812653008307433 / 125000000000000000000000000000 : ℚ), (122223894782446242851392512351 / 1000000000000000000000000000000 : ℚ)⟩
theorem b696 (b : ℝ) (hb : rootInterval.Contains b) : i696.Contains (n696 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b199 b hb) (b691 b hb))
    (by norm_num [i696, i199, i691, RationalInterval.mul]) (by norm_num [i696, i199, i691, RationalInterval.mul])

def n697 (b : ℝ) : ℝ := (n695 b) + (n696 b)
def i697 : RationalInterval := ⟨(-98274974132557620391619377753 / 1000000000000000000000000000000 : ℚ), (-98274972814484365888960267093 / 1000000000000000000000000000000 : ℚ)⟩
theorem b697 (b : ℝ) (hb : rootInterval.Contains b) : i697.Contains (n697 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b695 b hb) (b696 b hb))
    (by norm_num [i697, i695, i696, RationalInterval.add]) (by norm_num [i697, i695, i696, RationalInterval.add])

def n698 (b : ℝ) : ℝ := -(n183 b)
def i698 : RationalInterval := ⟨(14316384014993942109778000117 / 15625000000000000000000000000 : ℚ), (916248577711656044457550038539 / 1000000000000000000000000000000 : ℚ)⟩
theorem b698 (b : ℝ) (hb : rootInterval.Contains b) : i698.Contains (n698 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b183 b hb))
    (by norm_num [i698, i183, RationalInterval.neg]) (by norm_num [i698, i183, RationalInterval.neg])

def n699 (b : ℝ) : ℝ := -(n185 b)
def i699 : RationalInterval := ⟨(-34951240663994373113002814689 / 50000000000000000000000000000 : ℚ), (-349512406278889995784120842581 / 500000000000000000000000000000 : ℚ)⟩
theorem b699 (b : ℝ) (hb : rootInterval.Contains b) : i699.Contains (n699 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b185 b hb))
    (by norm_num [i699, i185, RationalInterval.neg]) (by norm_num [i699, i185, RationalInterval.neg])

def n700 (b : ℝ) : ℝ := (n694 b) + (n698 b)
def i700 : RationalInterval := ⟨(323721676340962249984547412249 / 250000000000000000000000000000 : ℚ), (647443354813892988771025856683 / 500000000000000000000000000000 : ℚ)⟩
theorem b700 (b : ℝ) (hb : rootInterval.Contains b) : i700.Contains (n700 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b694 b hb) (b698 b hb))
    (by norm_num [i700, i694, i698, RationalInterval.add]) (by norm_num [i700, i694, i698, RationalInterval.add])

def n701 (b : ℝ) : ℝ := (n697 b) + (n699 b)
def i701 : RationalInterval := ⟨(-797299787412445082651675671533 / 1000000000000000000000000000000 : ℚ), (-159459957074452871491440390451 / 200000000000000000000000000000 : ℚ)⟩
theorem b701 (b : ℝ) (hb : rootInterval.Contains b) : i701.Contains (n701 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b697 b hb) (b699 b hb))
    (by norm_num [i701, i697, i699, RationalInterval.add]) (by norm_num [i701, i697, i699, RationalInterval.add])

def n702 (b : ℝ) : ℝ := (n689 b) * (n16 b)
def i702 : RationalInterval := ⟨(-283368085716383024336714597979 / 500000000000000000000000000000 : ℚ), (-283368085159834281947881930299 / 500000000000000000000000000000 : ℚ)⟩
theorem b702 (b : ℝ) (hb : rootInterval.Contains b) : i702.Contains (n702 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b689 b hb) (b16 b hb))
    (by norm_num [i702, i689, i16, RationalInterval.mul]) (by norm_num [i702, i689, i16, RationalInterval.mul])

def n703 (b : ℝ) : ℝ := (n702 b) + (n690 b)
def i703 : RationalInterval := ⟨(-356383044025316242144246944223 / 1000000000000000000000000000000 : ℚ), (-89095760569624112915142500421 / 250000000000000000000000000000 : ℚ)⟩
theorem b703 (b : ℝ) (hb : rootInterval.Contains b) : i703.Contains (n703 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b702 b hb) (b690 b hb))
    (by norm_num [i703, i702, i690, RationalInterval.add]) (by norm_num [i703, i702, i690, RationalInterval.add])

def n704 (b : ℝ) : ℝ := (n700 b) * (n16 b)
def i704 : RationalInterval := ⟨(-647443354813892988771025856683 / 500000000000000000000000000000 : ℚ), (-323721676340962249984547412249 / 250000000000000000000000000000 : ℚ)⟩
theorem b704 (b : ℝ) (hb : rootInterval.Contains b) : i704.Contains (n704 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b700 b hb) (b16 b hb))
    (by norm_num [i704, i700, i16, RationalInterval.mul]) (by norm_num [i704, i700, i16, RationalInterval.mul])

def n705 (b : ℝ) : ℝ := (n152 b) * (n701 b)
def i705 : RationalInterval := ⟨(398649892686132178728600976127 / 1000000000000000000000000000000 : ℚ), (398649893706222541325837835767 / 1000000000000000000000000000000 : ℚ)⟩
theorem b705 (b : ℝ) (hb : rootInterval.Contains b) : i705.Contains (n705 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b152 b hb) (b701 b hb))
    (by norm_num [i705, i152, i701, RationalInterval.mul]) (by norm_num [i705, i152, i701, RationalInterval.mul])

def n706 (b : ℝ) : ℝ := (n704 b) + (n705 b)
def i706 : RationalInterval := ⟨(-896236816941653798813450737239 / 1000000000000000000000000000000 : ℚ), (-896236811657626458612351813229 / 1000000000000000000000000000000 : ℚ)⟩
theorem b706 (b : ℝ) (hb : rootInterval.Contains b) : i706.Contains (n706 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b704 b hb) (b705 b hb))
    (by norm_num [i706, i704, i705, RationalInterval.add]) (by norm_num [i706, i704, i705, RationalInterval.add])

def n707 (b : ℝ) : ℝ := (n703 b) + (n706 b)
def i707 : RationalInterval := ⟨(-626309930483485020478848840731 / 500000000000000000000000000000 : ℚ), (-1252619853936122910272921814913 / 1000000000000000000000000000000 : ℚ)⟩
theorem b707 (b : ℝ) (hb : rootInterval.Contains b) : i707.Contains (n707 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b703 b hb) (b706 b hb))
    (by norm_num [i707, i703, i706, RationalInterval.add]) (by norm_num [i707, i703, i706, RationalInterval.add])

def n708 (b : ℝ) : ℝ := (n701 b) * (n64 b)
def i708 : RationalInterval := ⟨(-398649893706222541325837835767 / 1000000000000000000000000000000 : ℚ), (-398649892686132178728600976127 / 1000000000000000000000000000000 : ℚ)⟩
theorem b708 (b : ℝ) (hb : rootInterval.Contains b) : i708.Contains (n708 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b701 b hb) (b64 b hb))
    (by norm_num [i708, i701, i64, RationalInterval.mul]) (by norm_num [i708, i701, i64, RationalInterval.mul])

def n709 (b : ℝ) : ℝ := (n700 b) + (n708 b)
def i709 : RationalInterval := ⟨(896236811657626458612351813229 / 1000000000000000000000000000000 : ℚ), (896236816941653798813450737239 / 1000000000000000000000000000000 : ℚ)⟩
theorem b709 (b : ℝ) (hb : rootInterval.Contains b) : i709.Contains (n709 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b700 b hb) (b708 b hb))
    (by norm_num [i709, i700, i708, RationalInterval.add]) (by norm_num [i709, i700, i708, RationalInterval.add])

def n710 (b : ℝ) : ℝ := (n700 b) * (n64 b)
def i710 : RationalInterval := ⟨(323721676340962249984547412249 / 500000000000000000000000000000 : ℚ), (647443354813892988771025856683 / 1000000000000000000000000000000 : ℚ)⟩
theorem b710 (b : ℝ) (hb : rootInterval.Contains b) : i710.Contains (n710 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b700 b hb) (b64 b hb))
    (by norm_num [i710, i700, i64, RationalInterval.mul]) (by norm_num [i710, i700, i64, RationalInterval.mul])

def n711 (b : ℝ) : ℝ := (n61 b) * (n701 b)
def i711 : RationalInterval := ⟨(-282604980963425125679622226097 / 1000000000000000000000000000000 : ℚ), (-17662811264892782372500132101 / 62500000000000000000000000000 : ℚ)⟩
theorem b711 (b : ℝ) (hb : rootInterval.Contains b) : i711.Contains (n711 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b61 b hb) (b701 b hb))
    (by norm_num [i711, i61, i701, RationalInterval.mul]) (by norm_num [i711, i61, i701, RationalInterval.mul])

def n712 (b : ℝ) : ℝ := (n710 b) + (n711 b)
def i712 : RationalInterval := ⟨(364838371718499374289472598401 / 1000000000000000000000000000000 : ℚ), (364838374575608470811023743067 / 1000000000000000000000000000000 : ℚ)⟩
theorem b712 (b : ℝ) (hb : rootInterval.Contains b) : i712.Contains (n712 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b710 b hb) (b711 b hb))
    (by norm_num [i712, i710, i711, RationalInterval.add]) (by norm_num [i712, i710, i711, RationalInterval.add])

def n713 (b : ℝ) : ℝ := (n700 b) * (n152 b)
def i713 : RationalInterval := ⟨(-647443354813892988771025856683 / 1000000000000000000000000000000 : ℚ), (-323721676340962249984547412249 / 500000000000000000000000000000 : ℚ)⟩
theorem b713 (b : ℝ) (hb : rootInterval.Contains b) : i713.Contains (n713 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b700 b hb) (b152 b hb))
    (by norm_num [i713, i700, i152, RationalInterval.mul]) (by norm_num [i713, i700, i152, RationalInterval.mul])

def n714 (b : ℝ) : ℝ := (n701 b) * (n600 b)
def i714 : RationalInterval := ⟨(116044912445854411305168201617 / 1000000000000000000000000000000 : ℚ), (116044912744790665114746722377 / 1000000000000000000000000000000 : ℚ)⟩
theorem b714 (b : ℝ) (hb : rootInterval.Contains b) : i714.Contains (n714 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b701 b hb) (b600 b hb))
    (by norm_num [i714, i701, i600, RationalInterval.mul]) (by norm_num [i714, i701, i600, RationalInterval.mul])

def n715 (b : ℝ) : ℝ := (n713 b) + (n714 b)
def i715 : RationalInterval := ⟨(-265699221184019288732928827533 / 500000000000000000000000000000 : ℚ), (-531398439937133834854348102121 / 1000000000000000000000000000000 : ℚ)⟩
theorem b715 (b : ℝ) (hb : rootInterval.Contains b) : i715.Contains (n715 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b713 b hb) (b714 b hb))
    (by norm_num [i715, i713, i714, RationalInterval.add]) (by norm_num [i715, i713, i714, RationalInterval.add])

def n716 (b : ℝ) : ℝ := (n715 b) * (n13 b)
def i716 : RationalInterval := ⟨(-265699221184019288732928827533 / 250000000000000000000000000000 : ℚ), (-531398439937133834854348102121 / 500000000000000000000000000000 : ℚ)⟩
theorem b716 (b : ℝ) (hb : rootInterval.Contains b) : i716.Contains (n716 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b715 b hb) (b13 b hb))
    (by norm_num [i716, i715, i13, RationalInterval.mul]) (by norm_num [i716, i715, i13, RationalInterval.mul])

def n717 (b : ℝ) : ℝ := (n689 b) * (n152 b)
def i717 : RationalInterval := ⟨(-283368085716383024336714597979 / 1000000000000000000000000000000 : ℚ), (-283368085159834281947881930299 / 1000000000000000000000000000000 : ℚ)⟩
theorem b717 (b : ℝ) (hb : rootInterval.Contains b) : i717.Contains (n717 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b689 b hb) (b152 b hb))
    (by norm_num [i717, i689, i152, RationalInterval.mul]) (by norm_num [i717, i689, i152, RationalInterval.mul])

def n718 (b : ℝ) : ℝ := (n690 b) * (n16 b)
def i718 : RationalInterval := ⟨(-105176564020586056117596929457 / 500000000000000000000000000000 : ℚ), (-42070625481489961305836450347 / 200000000000000000000000000000 : ℚ)⟩
theorem b718 (b : ℝ) (hb : rootInterval.Contains b) : i718.Contains (n718 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b690 b hb) (b16 b hb))
    (by norm_num [i718, i690, i16, RationalInterval.mul]) (by norm_num [i718, i690, i16, RationalInterval.mul])

def n719 (b : ℝ) : ℝ := (n690 b) * (n152 b)
def i719 : RationalInterval := ⟨(-105176564020586056117596929457 / 1000000000000000000000000000000 : ℚ), (-105176563703724903264591125867 / 1000000000000000000000000000000 : ℚ)⟩
theorem b719 (b : ℝ) (hb : rootInterval.Contains b) : i719.Contains (n719 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b690 b hb) (b152 b hb))
    (by norm_num [i719, i690, i152, RationalInterval.mul]) (by norm_num [i719, i690, i152, RationalInterval.mul])

