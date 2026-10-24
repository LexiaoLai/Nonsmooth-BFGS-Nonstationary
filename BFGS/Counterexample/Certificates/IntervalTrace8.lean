import BFGS.Counterexample.Certificates.IntervalTrace7

/-! Generated arithmetic proofs. Each bound is checked by the Lean kernel. -/
namespace BFGS.Counterexample.Trace
noncomputable section
open BFGS RationalInterval
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false

def n720 (b : ℝ) : ℝ := (n152 b) * (n689 b)
def i720 : RationalInterval := ⟨(-283368085716383024336714597979 / 1000000000000000000000000000000 : ℚ), (-283368085159834281947881930299 / 1000000000000000000000000000000 : ℚ)⟩
theorem b720 (b : ℝ) (hb : rootInterval.Contains b) : i720.Contains (n720 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b152 b hb) (b689 b hb))
    (by norm_num [i720, i152, i689, RationalInterval.mul]) (by norm_num [i720, i152, i689, RationalInterval.mul])

def n721 (b : ℝ) : ℝ := (n152 b) * (n690 b)
def i721 : RationalInterval := ⟨(-105176564020586056117596929457 / 1000000000000000000000000000000 : ℚ), (-105176563703724903264591125867 / 1000000000000000000000000000000 : ℚ)⟩
theorem b721 (b : ℝ) (hb : rootInterval.Contains b) : i721.Contains (n721 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b152 b hb) (b690 b hb))
    (by norm_num [i721, i152, i690, RationalInterval.mul]) (by norm_num [i721, i152, i690, RationalInterval.mul])

def n722 (b : ℝ) : ℝ := (n702 b) + (n702 b)
def i722 : RationalInterval := ⟨(-283368085716383024336714597979 / 250000000000000000000000000000 : ℚ), (-283368085159834281947881930299 / 250000000000000000000000000000 : ℚ)⟩
theorem b722 (b : ℝ) (hb : rootInterval.Contains b) : i722.Contains (n722 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b702 b hb) (b702 b hb))
    (by norm_num [i722, i702, i702, RationalInterval.add]) (by norm_num [i722, i702, i702, RationalInterval.add])

def n723 (b : ℝ) : ℝ := (n717 b) + (n718 b)
def i723 : RationalInterval := ⟨(-493721213757555136571908456893 / 1000000000000000000000000000000 : ℚ), (-246860606283642044238532091017 / 500000000000000000000000000000 : ℚ)⟩
theorem b723 (b : ℝ) (hb : rootInterval.Contains b) : i723.Contains (n723 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b717 b hb) (b718 b hb))
    (by norm_num [i723, i717, i718, RationalInterval.add]) (by norm_num [i723, i717, i718, RationalInterval.add])

def n724 (b : ℝ) : ℝ := (n718 b) + (n720 b)
def i724 : RationalInterval := ⟨(-493721213757555136571908456893 / 1000000000000000000000000000000 : ℚ), (-246860606283642044238532091017 / 500000000000000000000000000000 : ℚ)⟩
theorem b724 (b : ℝ) (hb : rootInterval.Contains b) : i724.Contains (n724 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b718 b hb) (b720 b hb))
    (by norm_num [i724, i718, i720, RationalInterval.add]) (by norm_num [i724, i718, i720, RationalInterval.add])

def n725 (b : ℝ) : ℝ := (n719 b) + (n721 b)
def i725 : RationalInterval := ⟨(-105176564020586056117596929457 / 500000000000000000000000000000 : ℚ), (-105176563703724903264591125867 / 500000000000000000000000000000 : ℚ)⟩
theorem b725 (b : ℝ) (hb : rootInterval.Contains b) : i725.Contains (n725 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b719 b hb) (b721 b hb))
    (by norm_num [i725, i719, i721, RationalInterval.add]) (by norm_num [i725, i719, i721, RationalInterval.add])

def n726 (b : ℝ) : ℝ := (n709 b) * (n16 b)
def i726 : RationalInterval := ⟨(-896236816941653798813450737239 / 1000000000000000000000000000000 : ℚ), (-896236811657626458612351813229 / 1000000000000000000000000000000 : ℚ)⟩
theorem b726 (b : ℝ) (hb : rootInterval.Contains b) : i726.Contains (n726 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b709 b hb) (b16 b hb))
    (by norm_num [i726, i709, i16, RationalInterval.mul]) (by norm_num [i726, i709, i16, RationalInterval.mul])

def n727 (b : ℝ) : ℝ := (n709 b) * (n152 b)
def i727 : RationalInterval := ⟨(-22405920423541344970336268431 / 50000000000000000000000000000 : ℚ), (-224059202914406614653087953307 / 500000000000000000000000000000 : ℚ)⟩
theorem b727 (b : ℝ) (hb : rootInterval.Contains b) : i727.Contains (n727 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b709 b hb) (b152 b hb))
    (by norm_num [i727, i709, i152, RationalInterval.mul]) (by norm_num [i727, i709, i152, RationalInterval.mul])

def n728 (b : ℝ) : ℝ := (n712 b) * (n16 b)
def i728 : RationalInterval := ⟨(-364838374575608470811023743067 / 1000000000000000000000000000000 : ℚ), (-364838371718499374289472598401 / 1000000000000000000000000000000 : ℚ)⟩
theorem b728 (b : ℝ) (hb : rootInterval.Contains b) : i728.Contains (n728 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b712 b hb) (b16 b hb))
    (by norm_num [i728, i712, i16, RationalInterval.mul]) (by norm_num [i728, i712, i16, RationalInterval.mul])

def n729 (b : ℝ) : ℝ := (n712 b) * (n152 b)
def i729 : RationalInterval := ⟨(-91209593643902117702755935767 / 500000000000000000000000000000 : ℚ), (-114011991162031054465460187 / 625000000000000000000000000 : ℚ)⟩
theorem b729 (b : ℝ) (hb : rootInterval.Contains b) : i729.Contains (n729 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b712 b hb) (b152 b hb))
    (by norm_num [i729, i712, i152, RationalInterval.mul]) (by norm_num [i729, i712, i152, RationalInterval.mul])

def n730 (b : ℝ) : ℝ := (n600 b) * (n689 b)
def i730 : RationalInterval := ⟨(-20621744355617992871793027571 / 250000000000000000000000000000 : ℚ), (-10310872157380835484883803507 / 125000000000000000000000000000 : ℚ)⟩
theorem b730 (b : ℝ) (hb : rootInterval.Contains b) : i730.Contains (n730 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b600 b hb) (b689 b hb))
    (by norm_num [i730, i600, i689, RationalInterval.mul]) (by norm_num [i730, i600, i689, RationalInterval.mul])

def n731 (b : ℝ) : ℝ := (n600 b) * (n690 b)
def i731 : RationalInterval := ⟨(-30616351307897731494390369233 / 1000000000000000000000000000000 : ℚ), (-6123270243027042686775394399 / 200000000000000000000000000000 : ℚ)⟩
theorem b731 (b : ℝ) (hb : rootInterval.Contains b) : i731.Contains (n731 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b600 b hb) (b690 b hb))
    (by norm_num [i731, i600, i690, RationalInterval.mul]) (by norm_num [i731, i600, i690, RationalInterval.mul])

def n732 (b : ℝ) : ℝ := (n726 b) + (n717 b)
def i732 : RationalInterval := ⟨(-589802451329018411575082667609 / 500000000000000000000000000000 : ℚ), (-147450612102182592570029217941 / 125000000000000000000000000000 : ℚ)⟩
theorem b732 (b : ℝ) (hb : rootInterval.Contains b) : i732.Contains (n732 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b726 b hb) (b717 b hb))
    (by norm_num [i732, i726, i717, RationalInterval.add]) (by norm_num [i732, i726, i717, RationalInterval.add])

def n733 (b : ℝ) : ℝ := (n727 b) + (n719 b)
def i733 : RationalInterval := ⟨(-553294972491412955524322298077 / 1000000000000000000000000000000 : ℚ), (-553294969532538132570767032481 / 1000000000000000000000000000000 : ℚ)⟩
theorem b733 (b : ℝ) (hb : rootInterval.Contains b) : i733.Contains (n733 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b727 b hb) (b719 b hb))
    (by norm_num [i733, i727, i719, RationalInterval.add]) (by norm_num [i733, i727, i719, RationalInterval.add])

def n734 (b : ℝ) : ℝ := (n728 b) + (n730 b)
def i734 : RationalInterval := ⟨(-447325351998080442298195853351 / 1000000000000000000000000000000 : ℚ), (-447325348977546058168543026457 / 1000000000000000000000000000000 : ℚ)⟩
theorem b734 (b : ℝ) (hb : rootInterval.Contains b) : i734.Contains (n734 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b728 b hb) (b730 b hb))
    (by norm_num [i734, i728, i730, RationalInterval.add]) (by norm_num [i734, i728, i730, RationalInterval.add])

def n735 (b : ℝ) : ℝ := (n729 b) + (n731 b)
def i735 : RationalInterval := ⟨(-213035538595701966899902240767 / 1000000000000000000000000000000 : ℚ), (-42607107414876980115722654239 / 200000000000000000000000000000 : ℚ)⟩
theorem b735 (b : ℝ) (hb : rootInterval.Contains b) : i735.Contains (n735 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b729 b hb) (b731 b hb))
    (by norm_num [i735, i729, i731, RationalInterval.add]) (by norm_num [i735, i729, i731, RationalInterval.add])

def n736 (b : ℝ) : ℝ := (n689 b) * (n600 b)
def i736 : RationalInterval := ⟨(-20621744355617992871793027571 / 250000000000000000000000000000 : ℚ), (-10310872157380835484883803507 / 125000000000000000000000000000 : ℚ)⟩
theorem b736 (b : ℝ) (hb : rootInterval.Contains b) : i736.Contains (n736 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b689 b hb) (b600 b hb))
    (by norm_num [i736, i689, i600, RationalInterval.mul]) (by norm_num [i736, i689, i600, RationalInterval.mul])

def n737 (b : ℝ) : ℝ := (n690 b) * (n600 b)
def i737 : RationalInterval := ⟨(-30616351307897731494390369233 / 1000000000000000000000000000000 : ℚ), (-6123270243027042686775394399 / 200000000000000000000000000000 : ℚ)⟩
theorem b737 (b : ℝ) (hb : rootInterval.Contains b) : i737.Contains (n737 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b690 b hb) (b600 b hb))
    (by norm_num [i737, i690, i600, RationalInterval.mul]) (by norm_num [i737, i690, i600, RationalInterval.mul])

def n738 (b : ℝ) : ℝ := (n152 b) * (n709 b)
def i738 : RationalInterval := ⟨(-22405920423541344970336268431 / 50000000000000000000000000000 : ℚ), (-224059202914406614653087953307 / 500000000000000000000000000000 : ℚ)⟩
theorem b738 (b : ℝ) (hb : rootInterval.Contains b) : i738.Contains (n738 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b152 b hb) (b709 b hb))
    (by norm_num [i738, i152, i709, RationalInterval.mul]) (by norm_num [i738, i152, i709, RationalInterval.mul])

def n739 (b : ℝ) : ℝ := (n152 b) * (n712 b)
def i739 : RationalInterval := ⟨(-91209593643902117702755935767 / 500000000000000000000000000000 : ℚ), (-114011991162031054465460187 / 625000000000000000000000000 : ℚ)⟩
theorem b739 (b : ℝ) (hb : rootInterval.Contains b) : i739.Contains (n739 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b152 b hb) (b712 b hb))
    (by norm_num [i739, i152, i712, RationalInterval.mul]) (by norm_num [i739, i152, i712, RationalInterval.mul])

def n740 (b : ℝ) : ℝ := (n717 b) + (n726 b)
def i740 : RationalInterval := ⟨(-589802451329018411575082667609 / 500000000000000000000000000000 : ℚ), (-147450612102182592570029217941 / 125000000000000000000000000000 : ℚ)⟩
theorem b740 (b : ℝ) (hb : rootInterval.Contains b) : i740.Contains (n740 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b717 b hb) (b726 b hb))
    (by norm_num [i740, i717, i726, RationalInterval.add]) (by norm_num [i740, i717, i726, RationalInterval.add])

def n741 (b : ℝ) : ℝ := (n736 b) + (n728 b)
def i741 : RationalInterval := ⟨(-447325351998080442298195853351 / 1000000000000000000000000000000 : ℚ), (-447325348977546058168543026457 / 1000000000000000000000000000000 : ℚ)⟩
theorem b741 (b : ℝ) (hb : rootInterval.Contains b) : i741.Contains (n741 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b736 b hb) (b728 b hb))
    (by norm_num [i741, i736, i728, RationalInterval.add]) (by norm_num [i741, i736, i728, RationalInterval.add])

def n742 (b : ℝ) : ℝ := (n719 b) + (n738 b)
def i742 : RationalInterval := ⟨(-553294972491412955524322298077 / 1000000000000000000000000000000 : ℚ), (-553294969532538132570767032481 / 1000000000000000000000000000000 : ℚ)⟩
theorem b742 (b : ℝ) (hb : rootInterval.Contains b) : i742.Contains (n742 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b719 b hb) (b738 b hb))
    (by norm_num [i742, i719, i738, RationalInterval.add]) (by norm_num [i742, i719, i738, RationalInterval.add])

def n743 (b : ℝ) : ℝ := (n737 b) + (n739 b)
def i743 : RationalInterval := ⟨(-213035538595701966899902240767 / 1000000000000000000000000000000 : ℚ), (-42607107414876980115722654239 / 200000000000000000000000000000 : ℚ)⟩
theorem b743 (b : ℝ) (hb : rootInterval.Contains b) : i743.Contains (n743 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b737 b hb) (b739 b hb))
    (by norm_num [i743, i737, i739, RationalInterval.add]) (by norm_num [i743, i737, i739, RationalInterval.add])

def n744 (b : ℝ) : ℝ := (n732 b) + (n740 b)
def i744 : RationalInterval := ⟨(-589802451329018411575082667609 / 250000000000000000000000000000 : ℚ), (-147450612102182592570029217941 / 62500000000000000000000000000 : ℚ)⟩
theorem b744 (b : ℝ) (hb : rootInterval.Contains b) : i744.Contains (n744 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b732 b hb) (b740 b hb))
    (by norm_num [i744, i732, i740, RationalInterval.add]) (by norm_num [i744, i732, i740, RationalInterval.add])

def n745 (b : ℝ) : ℝ := (n733 b) + (n741 b)
def i745 : RationalInterval := ⟨(-250155081122373349455629537857 / 250000000000000000000000000000 : ℚ), (-500310159255042095369655029469 / 500000000000000000000000000000 : ℚ)⟩
theorem b745 (b : ℝ) (hb : rootInterval.Contains b) : i745.Contains (n745 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b733 b hb) (b741 b hb))
    (by norm_num [i745, i733, i741, RationalInterval.add]) (by norm_num [i745, i733, i741, RationalInterval.add])

def n746 (b : ℝ) : ℝ := (n734 b) + (n742 b)
def i746 : RationalInterval := ⟨(-250155081122373349455629537857 / 250000000000000000000000000000 : ℚ), (-500310159255042095369655029469 / 500000000000000000000000000000 : ℚ)⟩
theorem b746 (b : ℝ) (hb : rootInterval.Contains b) : i746.Contains (n746 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b734 b hb) (b742 b hb))
    (by norm_num [i746, i734, i742, RationalInterval.add]) (by norm_num [i746, i734, i742, RationalInterval.add])

def n747 (b : ℝ) : ℝ := (n735 b) + (n743 b)
def i747 : RationalInterval := ⟨(-213035538595701966899902240767 / 500000000000000000000000000000 : ℚ), (-42607107414876980115722654239 / 100000000000000000000000000000 : ℚ)⟩
theorem b747 (b : ℝ) (hb : rootInterval.Contains b) : i747.Contains (n747 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b735 b hb) (b743 b hb))
    (by norm_num [i747, i735, i743, RationalInterval.add]) (by norm_num [i747, i735, i743, RationalInterval.add])

def n748 (b : ℝ) : ℝ := (n413 b) * (n744 b)
def i748 : RationalInterval := ⟨(147450612102182592570029217941 / 31250000000000000000000000000 : ℚ), (589802451329018411575082667609 / 125000000000000000000000000000 : ℚ)⟩
theorem b748 (b : ℝ) (hb : rootInterval.Contains b) : i748.Contains (n748 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b413 b hb) (b744 b hb))
    (by norm_num [i748, i413, i744, RationalInterval.mul]) (by norm_num [i748, i413, i744, RationalInterval.mul])

def n749 (b : ℝ) : ℝ := (n413 b) * (n745 b)
def i749 : RationalInterval := ⟨(500310159255042095369655029469 / 250000000000000000000000000000 : ℚ), (250155081122373349455629537857 / 125000000000000000000000000000 : ℚ)⟩
theorem b749 (b : ℝ) (hb : rootInterval.Contains b) : i749.Contains (n749 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b413 b hb) (b745 b hb))
    (by norm_num [i749, i413, i745, RationalInterval.mul]) (by norm_num [i749, i413, i745, RationalInterval.mul])

def n750 (b : ℝ) : ℝ := (n413 b) * (n746 b)
def i750 : RationalInterval := ⟨(500310159255042095369655029469 / 250000000000000000000000000000 : ℚ), (250155081122373349455629537857 / 125000000000000000000000000000 : ℚ)⟩
theorem b750 (b : ℝ) (hb : rootInterval.Contains b) : i750.Contains (n750 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b413 b hb) (b746 b hb))
    (by norm_num [i750, i413, i746, RationalInterval.mul]) (by norm_num [i750, i413, i746, RationalInterval.mul])

def n751 (b : ℝ) : ℝ := (n413 b) * (n747 b)
def i751 : RationalInterval := ⟨(42607107414876980115722654239 / 50000000000000000000000000000 : ℚ), (213035538595701966899902240767 / 250000000000000000000000000000 : ℚ)⟩
theorem b751 (b : ℝ) (hb : rootInterval.Contains b) : i751.Contains (n751 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b413 b hb) (b747 b hb))
    (by norm_num [i751, i413, i747, RationalInterval.mul]) (by norm_num [i751, i413, i747, RationalInterval.mul])

def n752 (b : ℝ) : ℝ := (n707 b) * (n57 b)
def i752 : RationalInterval := ⟨(-626309930483485020478848840731 / 125000000000000000000000000000 : ℚ), (-1252619853936122910272921814913 / 250000000000000000000000000000 : ℚ)⟩
theorem b752 (b : ℝ) (hb : rootInterval.Contains b) : i752.Contains (n752 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b707 b hb) (b57 b hb))
    (by norm_num [i752, i707, i57, RationalInterval.mul]) (by norm_num [i752, i707, i57, RationalInterval.mul])

def n753 (b : ℝ) : ℝ := (n752 b) * (n605 b)
def i753 : RationalInterval := ⟨(-49547053181182199499967821349 / 25000000000000000000000000000 : ℚ), (-1981882116110628513322176357947 / 1000000000000000000000000000000 : ℚ)⟩
theorem b753 (b : ℝ) (hb : rootInterval.Contains b) : i753.Contains (n753 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b752 b hb) (b605 b hb))
    (by norm_num [i753, i752, i605, RationalInterval.mul]) (by norm_num [i753, i752, i605, RationalInterval.mul])

def n754 (b : ℝ) : ℝ := (n752 b) * (n606 b)
def i754 : RationalInterval := ⟨(-49547053181182199499967821349 / 25000000000000000000000000000 : ℚ), (-1981882116110628513322176357947 / 1000000000000000000000000000000 : ℚ)⟩
theorem b754 (b : ℝ) (hb : rootInterval.Contains b) : i754.Contains (n754 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b752 b hb) (b606 b hb))
    (by norm_num [i754, i752, i606, RationalInterval.mul]) (by norm_num [i754, i752, i606, RationalInterval.mul])

def n755 (b : ℝ) : ℝ := (n752 b) * (n607 b)
def i755 : RationalInterval := ⟨(-364631133140158969520507586249 / 500000000000000000000000000000 : ℚ), (-364631131087252801524627271517 / 500000000000000000000000000000 : ℚ)⟩
theorem b755 (b : ℝ) (hb : rootInterval.Contains b) : i755.Contains (n755 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b752 b hb) (b607 b hb))
    (by norm_num [i755, i752, i607, RationalInterval.mul]) (by norm_num [i755, i752, i607, RationalInterval.mul])

def n756 (b : ℝ) : ℝ := (n748 b) + (n752 b)
def i756 : RationalInterval := ⟨(-36507482074754650198731968967 / 125000000000000000000000000000 : ℚ), (-14602990255617217424551295939 / 50000000000000000000000000000 : ℚ)⟩
theorem b756 (b : ℝ) (hb : rootInterval.Contains b) : i756.Contains (n756 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b748 b hb) (b752 b hb))
    (by norm_num [i756, i748, i752, RationalInterval.add]) (by norm_num [i756, i748, i752, RationalInterval.add])

def n757 (b : ℝ) : ℝ := (n749 b) + (n753 b)
def i757 : RationalInterval := ⟨(4839627443220100369976815979 / 250000000000000000000000000000 : ℚ), (19358532868358282322859944909 / 1000000000000000000000000000000 : ℚ)⟩
theorem b757 (b : ℝ) (hb : rootInterval.Contains b) : i757.Contains (n757 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b749 b hb) (b753 b hb))
    (by norm_num [i757, i749, i753, RationalInterval.add]) (by norm_num [i757, i749, i753, RationalInterval.add])

def n758 (b : ℝ) : ℝ := (n750 b) + (n754 b)
def i758 : RationalInterval := ⟨(4839627443220100369976815979 / 250000000000000000000000000000 : ℚ), (19358532868358282322859944909 / 1000000000000000000000000000000 : ℚ)⟩
theorem b758 (b : ℝ) (hb : rootInterval.Contains b) : i758.Contains (n758 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b750 b hb) (b754 b hb))
    (by norm_num [i758, i750, i754, RationalInterval.add]) (by norm_num [i758, i750, i754, RationalInterval.add])

def n759 (b : ℝ) : ℝ := (n751 b) + (n755 b)
def i759 : RationalInterval := ⟨(61439941008610831636718956141 / 500000000000000000000000000000 : ℚ), (61439946104151132275177210017 / 500000000000000000000000000000 : ℚ)⟩
theorem b759 (b : ℝ) (hb : rootInterval.Contains b) : i759.Contains (n759 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b751 b hb) (b755 b hb))
    (by norm_num [i759, i751, i755, RationalInterval.add]) (by norm_num [i759, i751, i755, RationalInterval.add])

def n760 (b : ℝ) : ℝ := (n707 b) + (n716 b)
def i760 : RationalInterval := ⟨(-1157708372851523597944706495797 / 500000000000000000000000000000 : ℚ), (-463083346762078115996323603831 / 200000000000000000000000000000 : ℚ)⟩
theorem b760 (b : ℝ) (hb : rootInterval.Contains b) : i760.Contains (n760 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b707 b hb) (b716 b hb))
    (by norm_num [i760, i707, i716, RationalInterval.add]) (by norm_num [i760, i707, i716, RationalInterval.add])

def n761 (b : ℝ) : ℝ := (n760 b) * (n57 b)
def i761 : RationalInterval := ⟨(-1157708372851523597944706495797 / 125000000000000000000000000000 : ℚ), (-463083346762078115996323603831 / 50000000000000000000000000000 : ℚ)⟩
theorem b761 (b : ℝ) (hb : rootInterval.Contains b) : i761.Contains (n761 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b760 b hb) (b57 b hb))
    (by norm_num [i761, i760, i57, RationalInterval.mul]) (by norm_num [i761, i760, i57, RationalInterval.mul])

def n762 (b : ℝ) : ℝ := (n663 b) * (n707 b)
def i762 : RationalInterval := ⟨(-6689401840000138161561633209 / 3125000000000000000000000000 : ℚ), (-2140608576778729919751535743757 / 1000000000000000000000000000000 : ℚ)⟩
theorem b762 (b : ℝ) (hb : rootInterval.Contains b) : i762.Contains (n762 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b663 b hb) (b707 b hb))
    (by norm_num [i762, i663, i707, RationalInterval.mul]) (by norm_num [i762, i663, i707, RationalInterval.mul])

def n763 (b : ℝ) : ℝ := (n762 b) * (n665 b)
def i763 : RationalInterval := ⟨(-6689401840000138161561633209 / 390625000000000000000000000 : ℚ), (-2140608576778729919751535743757 / 125000000000000000000000000000 : ℚ)⟩
theorem b763 (b : ℝ) (hb : rootInterval.Contains b) : i763.Contains (n763 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b762 b hb) (b665 b hb))
    (by norm_num [i763, i762, i665, RationalInterval.mul]) (by norm_num [i763, i762, i665, RationalInterval.mul])

def n764 (b : ℝ) : ℝ := -(n763 b)
def i764 : RationalInterval := ⟨(2140608576778729919751535743757 / 125000000000000000000000000000 : ℚ), (6689401840000138161561633209 / 390625000000000000000000000 : ℚ)⟩
theorem b764 (b : ℝ) (hb : rootInterval.Contains b) : i764.Contains (n764 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b763 b hb))
    (by norm_num [i764, i763, RationalInterval.neg]) (by norm_num [i764, i763, RationalInterval.neg])

def n765 (b : ℝ) : ℝ := (n761 b) + (n764 b)
def i765 : RationalInterval := ⟨(24572505098180158045170731199 / 3125000000000000000000000000 : ℚ), (393160088757939568683565446921 / 50000000000000000000000000000 : ℚ)⟩
theorem b765 (b : ℝ) (hb : rootInterval.Contains b) : i765.Contains (n765 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b761 b hb) (b764 b hb))
    (by norm_num [i765, i761, i764, RationalInterval.add]) (by norm_num [i765, i761, i764, RationalInterval.add])

def n766 (b : ℝ) : ℝ := (n765 b) * (n64 b)
def i766 : RationalInterval := ⟨(24572505098180158045170731199 / 6250000000000000000000000000 : ℚ), (393160088757939568683565446921 / 100000000000000000000000000000 : ℚ)⟩
theorem b766 (b : ℝ) (hb : rootInterval.Contains b) : i766.Contains (n766 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b765 b hb) (b64 b hb))
    (by norm_num [i766, i765, i64, RationalInterval.mul]) (by norm_num [i766, i765, i64, RationalInterval.mul])

def n767 (b : ℝ) : ℝ := (n765 b) * (n58 b)
def i767 : RationalInterval := ⟨(24572505098180158045170731199 / 12500000000000000000000000000 : ℚ), (393160088757939568683565446921 / 200000000000000000000000000000 : ℚ)⟩
theorem b767 (b : ℝ) (hb : rootInterval.Contains b) : i767.Contains (n767 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b765 b hb) (b58 b hb))
    (by norm_num [i767, i765, i58, RationalInterval.mul]) (by norm_num [i767, i765, i58, RationalInterval.mul])

def n768 (b : ℝ) : ℝ := (n756 b) + (n765 b)
def i768 : RationalInterval := ⟨(946392721852451671608097278993 / 125000000000000000000000000000 : ℚ), (189278549251161175629507075491 / 25000000000000000000000000000 : ℚ)⟩
theorem b768 (b : ℝ) (hb : rootInterval.Contains b) : i768.Contains (n768 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b756 b hb) (b765 b hb))
    (by norm_num [i768, i756, i765, RationalInterval.add]) (by norm_num [i768, i756, i765, RationalInterval.add])

def n769 (b : ℝ) : ℝ := (n757 b) + (n766 b)
def i769 : RationalInterval := ⟨(987739831370426422176806063939 / 250000000000000000000000000000 : ℚ), (3950959420447753969158514414119 / 1000000000000000000000000000000 : ℚ)⟩
theorem b769 (b : ℝ) (hb : rootInterval.Contains b) : i769.Contains (n769 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b757 b hb) (b766 b hb))
    (by norm_num [i769, i757, i766, RationalInterval.add]) (by norm_num [i769, i757, i766, RationalInterval.add])

def n770 (b : ℝ) : ℝ := (n758 b) + (n766 b)
def i770 : RationalInterval := ⟨(987739831370426422176806063939 / 250000000000000000000000000000 : ℚ), (3950959420447753969158514414119 / 1000000000000000000000000000000 : ℚ)⟩
theorem b770 (b : ℝ) (hb : rootInterval.Contains b) : i770.Contains (n770 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b758 b hb) (b766 b hb))
    (by norm_num [i770, i758, i766, RationalInterval.add]) (by norm_num [i770, i758, i766, RationalInterval.add])

def n771 (b : ℝ) : ℝ := (n759 b) + (n767 b)
def i771 : RationalInterval := ⟨(1044340144935817153443548204101 / 500000000000000000000000000000 : ℚ), (2088680335998000107968181654639 / 1000000000000000000000000000000 : ℚ)⟩
theorem b771 (b : ℝ) (hb : rootInterval.Contains b) : i771.Contains (n771 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b759 b hb) (b767 b hb))
    (by norm_num [i771, i759, i767, RationalInterval.add]) (by norm_num [i771, i759, i767, RationalInterval.add])

def n772 (b : ℝ) : ℝ := (n675 b) * (n722 b)
def i772 : RationalInterval := ⟨(-968498388023421835229678001593 / 250000000000000000000000000000 : ℚ), (-1936996772236820158363577044527 / 500000000000000000000000000000 : ℚ)⟩
theorem b772 (b : ℝ) (hb : rootInterval.Contains b) : i772.Contains (n772 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b675 b hb) (b722 b hb))
    (by norm_num [i772, i675, i722, RationalInterval.mul]) (by norm_num [i772, i675, i722, RationalInterval.mul])

def n773 (b : ℝ) : ℝ := (n675 b) * (n723 b)
def i773 : RationalInterval := ⟨(-843722747479311444736651840721 / 500000000000000000000000000000 : ℚ), (-337489098177112984057787028631 / 200000000000000000000000000000 : ℚ)⟩
theorem b773 (b : ℝ) (hb : rootInterval.Contains b) : i773.Contains (n773 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b675 b hb) (b723 b hb))
    (by norm_num [i773, i675, i723, RationalInterval.mul]) (by norm_num [i773, i675, i723, RationalInterval.mul])

def n774 (b : ℝ) : ℝ := (n675 b) * (n724 b)
def i774 : RationalInterval := ⟨(-843722747479311444736651840721 / 500000000000000000000000000000 : ℚ), (-337489098177112984057787028631 / 200000000000000000000000000000 : ℚ)⟩
theorem b774 (b : ℝ) (hb : rootInterval.Contains b) : i774.Contains (n774 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b675 b hb) (b724 b hb))
    (by norm_num [i774, i675, i724, RationalInterval.mul]) (by norm_num [i774, i675, i724, RationalInterval.mul])

def n775 (b : ℝ) : ℝ := (n675 b) * (n725 b)
def i775 : RationalInterval := ⟨(-718947106935201054243625679849 / 1000000000000000000000000000000 : ℚ), (-718947104767154841107146620887 / 1000000000000000000000000000000 : ℚ)⟩
theorem b775 (b : ℝ) (hb : rootInterval.Contains b) : i775.Contains (n775 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b675 b hb) (b725 b hb))
    (by norm_num [i775, i675, i725, RationalInterval.mul]) (by norm_num [i775, i675, i725, RationalInterval.mul])

def n776 (b : ℝ) : ℝ := (n768 b) + (n772 b)
def i776 : RationalInterval := ⟨(924287055681481507986516556393 / 250000000000000000000000000000 : ℚ), (1848574212786403354226564465293 / 500000000000000000000000000000 : ℚ)⟩
theorem b776 (b : ℝ) (hb : rootInterval.Contains b) : i776.Contains (n776 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b768 b hb) (b772 b hb))
    (by norm_num [i776, i768, i772, RationalInterval.add]) (by norm_num [i776, i768, i772, RationalInterval.add])

def n777 (b : ℝ) : ℝ := (n769 b) + (n773 b)
def i777 : RationalInterval := ⟨(1131756915261541399616960287157 / 500000000000000000000000000000 : ℚ), (565878482390547262217394817741 / 250000000000000000000000000000 : ℚ)⟩
theorem b777 (b : ℝ) (hb : rootInterval.Contains b) : i777.Contains (n777 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b769 b hb) (b773 b hb))
    (by norm_num [i777, i769, i773, RationalInterval.add]) (by norm_num [i777, i769, i773, RationalInterval.add])

def n778 (b : ℝ) : ℝ := (n770 b) + (n774 b)
def i778 : RationalInterval := ⟨(1131756915261541399616960287157 / 500000000000000000000000000000 : ℚ), (565878482390547262217394817741 / 250000000000000000000000000000 : ℚ)⟩
theorem b778 (b : ℝ) (hb : rootInterval.Contains b) : i778.Contains (n778 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b770 b hb) (b774 b hb))
    (by norm_num [i778, i770, i774, RationalInterval.add]) (by norm_num [i778, i770, i774, RationalInterval.add])

def n779 (b : ℝ) : ℝ := (n771 b) + (n775 b)
def i779 : RationalInterval := ⟨(1369733182936433252643470728353 / 1000000000000000000000000000000 : ℚ), (171216653903855658357629379219 / 125000000000000000000000000000 : ℚ)⟩
theorem b779 (b : ℝ) (hb : rootInterval.Contains b) : i779.Contains (n779 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b771 b hb) (b775 b hb))
    (by norm_num [i779, i771, i775, RationalInterval.add]) (by norm_num [i779, i771, i775, RationalInterval.add])

def n780 (b : ℝ) : ℝ := (n196 b) * (n16 b)
def i780 : RationalInterval := ⟨(-749508994092494958215536766851 / 500000000000000000000000000000 : ℚ), (-1499017987006458498787906232757 / 1000000000000000000000000000000 : ℚ)⟩
theorem b780 (b : ℝ) (hb : rootInterval.Contains b) : i780.Contains (n780 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b196 b hb) (b16 b hb))
    (by norm_num [i780, i196, i16, RationalInterval.mul]) (by norm_num [i780, i196, i16, RationalInterval.mul])

def n781 (b : ℝ) : ℝ := (n198 b) * (n16 b)
def i781 : RationalInterval := ⟨(389067928155278712648699664163 / 1000000000000000000000000000000 : ℚ), (97266982230677460743126848381 / 250000000000000000000000000000 : ℚ)⟩
theorem b781 (b : ℝ) (hb : rootInterval.Contains b) : i781.Contains (n781 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b198 b hb) (b16 b hb))
    (by norm_num [i781, i198, i16, RationalInterval.mul]) (by norm_num [i781, i198, i16, RationalInterval.mul])

def n782 (b : ℝ) : ℝ := (n780 b) * (n16 b)
def i782 : RationalInterval := ⟨(1499017987006458498787906232757 / 1000000000000000000000000000000 : ℚ), (749508994092494958215536766851 / 500000000000000000000000000000 : ℚ)⟩
theorem b782 (b : ℝ) (hb : rootInterval.Contains b) : i782.Contains (n782 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b780 b hb) (b16 b hb))
    (by norm_num [i782, i780, i16, RationalInterval.mul]) (by norm_num [i782, i780, i16, RationalInterval.mul])

def n783 (b : ℝ) : ℝ := (n152 b) * (n781 b)
def i783 : RationalInterval := ⟨(-97266982230677460743126848381 / 500000000000000000000000000000 : ℚ), (-194533964077639356324349832081 / 1000000000000000000000000000000 : ℚ)⟩
theorem b783 (b : ℝ) (hb : rootInterval.Contains b) : i783.Contains (n783 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b152 b hb) (b781 b hb))
    (by norm_num [i783, i152, i781, RationalInterval.mul]) (by norm_num [i783, i152, i781, RationalInterval.mul])

def n784 (b : ℝ) : ℝ := (n782 b) + (n783 b)
def i784 : RationalInterval := ⟨(260896804509020715460330507199 / 200000000000000000000000000000 : ℚ), (1304484024107350560106723701621 / 1000000000000000000000000000000 : ℚ)⟩
theorem b784 (b : ℝ) (hb : rootInterval.Contains b) : i784.Contains (n784 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b782 b hb) (b783 b hb))
    (by norm_num [i784, i782, i783, RationalInterval.add]) (by norm_num [i784, i782, i783, RationalInterval.add])

def n785 (b : ℝ) : ℝ := (n15 b) + (n784 b)
def i785 : RationalInterval := ⟨(460896804509020715460330507199 / 200000000000000000000000000000 : ℚ), (2304484024107350560106723701621 / 1000000000000000000000000000000 : ℚ)⟩
theorem b785 (b : ℝ) (hb : rootInterval.Contains b) : i785.Contains (n785 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b15 b hb) (b784 b hb))
    (by norm_num [i785, i15, i784, RationalInterval.add]) (by norm_num [i785, i15, i784, RationalInterval.add])

def n786 (b : ℝ) : ℝ := (n781 b) * (n64 b)
def i786 : RationalInterval := ⟨(194533964077639356324349832081 / 1000000000000000000000000000000 : ℚ), (97266982230677460743126848381 / 500000000000000000000000000000 : ℚ)⟩
theorem b786 (b : ℝ) (hb : rootInterval.Contains b) : i786.Contains (n786 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b781 b hb) (b64 b hb))
    (by norm_num [i786, i781, i64, RationalInterval.mul]) (by norm_num [i786, i781, i64, RationalInterval.mul])

def n787 (b : ℝ) : ℝ := (n780 b) + (n786 b)
def i787 : RationalInterval := ⟨(-1304484024107350560106723701621 / 1000000000000000000000000000000 : ℚ), (-260896804509020715460330507199 / 200000000000000000000000000000 : ℚ)⟩
theorem b787 (b : ℝ) (hb : rootInterval.Contains b) : i787.Contains (n787 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b780 b hb) (b786 b hb))
    (by norm_num [i787, i780, i786, RationalInterval.add]) (by norm_num [i787, i780, i786, RationalInterval.add])

def n788 (b : ℝ) : ℝ := (n780 b) * (n64 b)
def i788 : RationalInterval := ⟨(-749508994092494958215536766851 / 1000000000000000000000000000000 : ℚ), (-374754496751614624696976558189 / 500000000000000000000000000000 : ℚ)⟩
theorem b788 (b : ℝ) (hb : rootInterval.Contains b) : i788.Contains (n788 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b780 b hb) (b64 b hb))
    (by norm_num [i788, i780, i64, RationalInterval.mul]) (by norm_num [i788, i780, i64, RationalInterval.mul])

def n789 (b : ℝ) : ℝ := (n61 b) * (n781 b)
def i789 : RationalInterval := ⟨(27581227579619954715690394629 / 200000000000000000000000000000 : ℚ), (137906138171090401261040176949 / 1000000000000000000000000000000 : ℚ)⟩
theorem b789 (b : ℝ) (hb : rootInterval.Contains b) : i789.Contains (n789 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b61 b hb) (b781 b hb))
    (by norm_num [i789, i61, i781, RationalInterval.mul]) (by norm_num [i789, i61, i781, RationalInterval.mul])

def n790 (b : ℝ) : ℝ := (n788 b) + (n789 b)
def i790 : RationalInterval := ⟨(-305801428097197592318542396853 / 500000000000000000000000000000 : ℚ), (-611602855332138848132912939429 / 1000000000000000000000000000000 : ℚ)⟩
theorem b790 (b : ℝ) (hb : rootInterval.Contains b) : i790.Contains (n790 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b788 b hb) (b789 b hb))
    (by norm_num [i790, i788, i789, RationalInterval.add]) (by norm_num [i790, i788, i789, RationalInterval.add])

def n791 (b : ℝ) : ℝ := (n787 b) + (n16 b)
def i791 : RationalInterval := ⟨(-2304484024107350560106723701621 / 1000000000000000000000000000000 : ℚ), (-460896804509020715460330507199 / 200000000000000000000000000000 : ℚ)⟩
theorem b791 (b : ℝ) (hb : rootInterval.Contains b) : i791.Contains (n791 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b787 b hb) (b16 b hb))
    (by norm_num [i791, i787, i16, RationalInterval.add]) (by norm_num [i791, i787, i16, RationalInterval.add])

def n792 (b : ℝ) : ℝ := (n780 b) * (n152 b)
def i792 : RationalInterval := ⟨(374754496751614624696976558189 / 500000000000000000000000000000 : ℚ), (749508994092494958215536766851 / 1000000000000000000000000000000 : ℚ)⟩
theorem b792 (b : ℝ) (hb : rootInterval.Contains b) : i792.Contains (n792 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b780 b hb) (b152 b hb))
    (by norm_num [i792, i780, i152, RationalInterval.mul]) (by norm_num [i792, i780, i152, RationalInterval.mul])

def n793 (b : ℝ) : ℝ := (n781 b) * (n600 b)
def i793 : RationalInterval := ⟨(-56627826291237190047520294421 / 1000000000000000000000000000000 : ℚ), (-56627826178566912925509662153 / 1000000000000000000000000000000 : ℚ)⟩
theorem b793 (b : ℝ) (hb : rootInterval.Contains b) : i793.Contains (n793 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b781 b hb) (b600 b hb))
    (by norm_num [i793, i781, i600, RationalInterval.mul]) (by norm_num [i793, i781, i600, RationalInterval.mul])

def n794 (b : ℝ) : ℝ := (n792 b) + (n793 b)
def i794 : RationalInterval := ⟨(692881167211992059346432821957 / 1000000000000000000000000000000 : ℚ), (346440583956964022645013552349 / 500000000000000000000000000000 : ℚ)⟩
theorem b794 (b : ℝ) (hb : rootInterval.Contains b) : i794.Contains (n794 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b792 b hb) (b793 b hb))
    (by norm_num [i794, i792, i793, RationalInterval.add]) (by norm_num [i794, i792, i793, RationalInterval.add])

def n795 (b : ℝ) : ℝ := (n794 b) * (n13 b)
def i795 : RationalInterval := ⟨(692881167211992059346432821957 / 500000000000000000000000000000 : ℚ), (346440583956964022645013552349 / 250000000000000000000000000000 : ℚ)⟩
theorem b795 (b : ℝ) (hb : rootInterval.Contains b) : i795.Contains (n795 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b794 b hb) (b13 b hb))
    (by norm_num [i795, i794, i13, RationalInterval.mul]) (by norm_num [i795, i794, i13, RationalInterval.mul])

def n796 (b : ℝ) : ℝ := (n795 b) + (n15 b)
def i796 : RationalInterval := ⟨(1192881167211992059346432821957 / 500000000000000000000000000000 : ℚ), (596440583956964022645013552349 / 250000000000000000000000000000 : ℚ)⟩
theorem b796 (b : ℝ) (hb : rootInterval.Contains b) : i796.Contains (n796 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b795 b hb) (b15 b hb))
    (by norm_num [i796, i795, i15, RationalInterval.add]) (by norm_num [i796, i795, i15, RationalInterval.add])

def n797 (b : ℝ) : ℝ := (n791 b) * (n16 b)
def i797 : RationalInterval := ⟨(460896804509020715460330507199 / 200000000000000000000000000000 : ℚ), (2304484024107350560106723701621 / 1000000000000000000000000000000 : ℚ)⟩
theorem b797 (b : ℝ) (hb : rootInterval.Contains b) : i797.Contains (n797 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b791 b hb) (b16 b hb))
    (by norm_num [i797, i791, i16, RationalInterval.mul]) (by norm_num [i797, i791, i16, RationalInterval.mul])

def n798 (b : ℝ) : ℝ := (n791 b) * (n152 b)
def i798 : RationalInterval := ⟨(1152242011272551788650826267997 / 1000000000000000000000000000000 : ℚ), (1152242012053675280053361850811 / 1000000000000000000000000000000 : ℚ)⟩
theorem b798 (b : ℝ) (hb : rootInterval.Contains b) : i798.Contains (n798 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b791 b hb) (b152 b hb))
    (by norm_num [i798, i791, i152, RationalInterval.mul]) (by norm_num [i798, i791, i152, RationalInterval.mul])

def n799 (b : ℝ) : ℝ := (n790 b) * (n16 b)
def i799 : RationalInterval := ⟨(611602855332138848132912939429 / 1000000000000000000000000000000 : ℚ), (305801428097197592318542396853 / 500000000000000000000000000000 : ℚ)⟩
theorem b799 (b : ℝ) (hb : rootInterval.Contains b) : i799.Contains (n799 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b790 b hb) (b16 b hb))
    (by norm_num [i799, i790, i16, RationalInterval.mul]) (by norm_num [i799, i790, i16, RationalInterval.mul])

def n800 (b : ℝ) : ℝ := (n790 b) * (n152 b)
def i800 : RationalInterval := ⟨(152900713833034712033228234857 / 500000000000000000000000000000 : ℚ), (305801428097197592318542396853 / 1000000000000000000000000000000 : ℚ)⟩
theorem b800 (b : ℝ) (hb : rootInterval.Contains b) : i800.Contains (n800 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b790 b hb) (b152 b hb))
    (by norm_num [i800, i790, i152, RationalInterval.mul]) (by norm_num [i800, i790, i152, RationalInterval.mul])

def n801 (b : ℝ) : ℝ := (n797 b) + (n64 b)
def i801 : RationalInterval := ⟨(560896804509020715460330507199 / 200000000000000000000000000000 : ℚ), (2804484024107350560106723701621 / 1000000000000000000000000000000 : ℚ)⟩
theorem b801 (b : ℝ) (hb : rootInterval.Contains b) : i801.Contains (n801 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b797 b hb) (b64 b hb))
    (by norm_num [i801, i797, i64, RationalInterval.add]) (by norm_num [i801, i797, i64, RationalInterval.add])

def n802 (b : ℝ) : ℝ := (n799 b) + (n602 b)
def i802 : RationalInterval := ⟨(757150257419638848132912939429 / 1000000000000000000000000000000 : ℚ), (378575129142197592318542396853 / 500000000000000000000000000000 : ℚ)⟩
theorem b802 (b : ℝ) (hb : rootInterval.Contains b) : i802.Contains (n802 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b799 b hb) (b602 b hb))
    (by norm_num [i802, i799, i602, RationalInterval.add]) (by norm_num [i802, i799, i602, RationalInterval.add])

def n803 (b : ℝ) : ℝ := (n16 b) * (n600 b)
def i803 : RationalInterval := ⟨(11643792167 / 80000000000 : ℚ), (14554740209 / 100000000000 : ℚ)⟩
theorem b803 (b : ℝ) (hb : rootInterval.Contains b) : i803.Contains (n803 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b16 b hb) (b600 b hb))
    (by norm_num [i803, i16, i600, RationalInterval.mul]) (by norm_num [i803, i16, i600, RationalInterval.mul])

def n804 (b : ℝ) : ℝ := (n152 b) * (n791 b)
def i804 : RationalInterval := ⟨(1152242011272551788650826267997 / 1000000000000000000000000000000 : ℚ), (1152242012053675280053361850811 / 1000000000000000000000000000000 : ℚ)⟩
theorem b804 (b : ℝ) (hb : rootInterval.Contains b) : i804.Contains (n804 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b152 b hb) (b791 b hb))
    (by norm_num [i804, i152, i791, RationalInterval.mul]) (by norm_num [i804, i152, i791, RationalInterval.mul])

def n805 (b : ℝ) : ℝ := (n152 b) * (n790 b)
def i805 : RationalInterval := ⟨(152900713833034712033228234857 / 500000000000000000000000000000 : ℚ), (305801428097197592318542396853 / 1000000000000000000000000000000 : ℚ)⟩
theorem b805 (b : ℝ) (hb : rootInterval.Contains b) : i805.Contains (n805 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b152 b hb) (b790 b hb))
    (by norm_num [i805, i152, i790, RationalInterval.mul]) (by norm_num [i805, i152, i790, RationalInterval.mul])

def n806 (b : ℝ) : ℝ := (n64 b) + (n797 b)
def i806 : RationalInterval := ⟨(560896804509020715460330507199 / 200000000000000000000000000000 : ℚ), (2804484024107350560106723701621 / 1000000000000000000000000000000 : ℚ)⟩
theorem b806 (b : ℝ) (hb : rootInterval.Contains b) : i806.Contains (n806 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b64 b hb) (b797 b hb))
    (by norm_num [i806, i64, i797, RationalInterval.add]) (by norm_num [i806, i64, i797, RationalInterval.add])

def n807 (b : ℝ) : ℝ := (n803 b) + (n799 b)
def i807 : RationalInterval := ⟨(757150257419638848132912939429 / 1000000000000000000000000000000 : ℚ), (378575129142197592318542396853 / 500000000000000000000000000000 : ℚ)⟩
theorem b807 (b : ℝ) (hb : rootInterval.Contains b) : i807.Contains (n807 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b803 b hb) (b799 b hb))
    (by norm_num [i807, i803, i799, RationalInterval.add]) (by norm_num [i807, i803, i799, RationalInterval.add])

def n808 (b : ℝ) : ℝ := (n801 b) + (n806 b)
def i808 : RationalInterval := ⟨(560896804509020715460330507199 / 100000000000000000000000000000 : ℚ), (2804484024107350560106723701621 / 500000000000000000000000000000 : ℚ)⟩
theorem b808 (b : ℝ) (hb : rootInterval.Contains b) : i808.Contains (n808 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b801 b hb) (b806 b hb))
    (by norm_num [i808, i801, i806, RationalInterval.add]) (by norm_num [i808, i801, i806, RationalInterval.add])

def n809 (b : ℝ) : ℝ := (n798 b) + (n807 b)
def i809 : RationalInterval := ⟨(954696134346095318391869603713 / 500000000000000000000000000000 : ℚ), (1909392270338070464690446644517 / 1000000000000000000000000000000 : ℚ)⟩
theorem b809 (b : ℝ) (hb : rootInterval.Contains b) : i809.Contains (n809 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b798 b hb) (b807 b hb))
    (by norm_num [i809, i798, i807, RationalInterval.add]) (by norm_num [i809, i798, i807, RationalInterval.add])

