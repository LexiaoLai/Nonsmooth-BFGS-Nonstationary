import BFGS.Counterexample.Certificates.IntervalTrace8

/-! Generated arithmetic proofs. Each bound is checked by the Lean kernel. -/
namespace BFGS.Counterexample.Trace
noncomputable section
open BFGS RationalInterval
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false

def n810 (b : ℝ) : ℝ := (n802 b) + (n804 b)
def i810 : RationalInterval := ⟨(954696134346095318391869603713 / 500000000000000000000000000000 : ℚ), (1909392270338070464690446644517 / 1000000000000000000000000000000 : ℚ)⟩
theorem b810 (b : ℝ) (hb : rootInterval.Contains b) : i810.Contains (n810 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b802 b hb) (b804 b hb))
    (by norm_num [i810, i802, i804, RationalInterval.add]) (by norm_num [i810, i802, i804, RationalInterval.add])

def n811 (b : ℝ) : ℝ := (n800 b) + (n805 b)
def i811 : RationalInterval := ⟨(152900713833034712033228234857 / 250000000000000000000000000000 : ℚ), (305801428097197592318542396853 / 500000000000000000000000000000 : ℚ)⟩
theorem b811 (b : ℝ) (hb : rootInterval.Contains b) : i811.Contains (n811 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b800 b hb) (b805 b hb))
    (by norm_num [i811, i800, i805, RationalInterval.add]) (by norm_num [i811, i800, i805, RationalInterval.add])

def n812 (b : ℝ) : ℝ := (n413 b) * (n808 b)
def i812 : RationalInterval := ⟨(-2804484024107350560106723701621 / 250000000000000000000000000000 : ℚ), (-560896804509020715460330507199 / 50000000000000000000000000000 : ℚ)⟩
theorem b812 (b : ℝ) (hb : rootInterval.Contains b) : i812.Contains (n812 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b413 b hb) (b808 b hb))
    (by norm_num [i812, i413, i808, RationalInterval.mul]) (by norm_num [i812, i413, i808, RationalInterval.mul])

def n813 (b : ℝ) : ℝ := (n413 b) * (n809 b)
def i813 : RationalInterval := ⟨(-1909392270338070464690446644517 / 500000000000000000000000000000 : ℚ), (-954696134346095318391869603713 / 250000000000000000000000000000 : ℚ)⟩
theorem b813 (b : ℝ) (hb : rootInterval.Contains b) : i813.Contains (n813 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b413 b hb) (b809 b hb))
    (by norm_num [i813, i413, i809, RationalInterval.mul]) (by norm_num [i813, i413, i809, RationalInterval.mul])

def n814 (b : ℝ) : ℝ := (n413 b) * (n810 b)
def i814 : RationalInterval := ⟨(-1909392270338070464690446644517 / 500000000000000000000000000000 : ℚ), (-954696134346095318391869603713 / 250000000000000000000000000000 : ℚ)⟩
theorem b814 (b : ℝ) (hb : rootInterval.Contains b) : i814.Contains (n814 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b413 b hb) (b810 b hb))
    (by norm_num [i814, i413, i810, RationalInterval.mul]) (by norm_num [i814, i413, i810, RationalInterval.mul])

def n815 (b : ℝ) : ℝ := (n413 b) * (n811 b)
def i815 : RationalInterval := ⟨(-305801428097197592318542396853 / 250000000000000000000000000000 : ℚ), (-152900713833034712033228234857 / 125000000000000000000000000000 : ℚ)⟩
theorem b815 (b : ℝ) (hb : rootInterval.Contains b) : i815.Contains (n815 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b413 b hb) (b811 b hb))
    (by norm_num [i815, i413, i811, RationalInterval.mul]) (by norm_num [i815, i413, i811, RationalInterval.mul])

def n816 (b : ℝ) : ℝ := (n812 b) + (n15 b)
def i816 : RationalInterval := ⟨(-2554484024107350560106723701621 / 250000000000000000000000000000 : ℚ), (-510896804509020715460330507199 / 50000000000000000000000000000 : ℚ)⟩
theorem b816 (b : ℝ) (hb : rootInterval.Contains b) : i816.Contains (n816 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b812 b hb) (b15 b hb))
    (by norm_num [i816, i812, i15, RationalInterval.add]) (by norm_num [i816, i812, i15, RationalInterval.add])

def n817 (b : ℝ) : ℝ := (n785 b) * (n57 b)
def i817 : RationalInterval := ⟨(460896804509020715460330507199 / 50000000000000000000000000000 : ℚ), (2304484024107350560106723701621 / 250000000000000000000000000000 : ℚ)⟩
theorem b817 (b : ℝ) (hb : rootInterval.Contains b) : i817.Contains (n817 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b785 b hb) (b57 b hb))
    (by norm_num [i817, i785, i57, RationalInterval.mul]) (by norm_num [i817, i785, i57, RationalInterval.mul])

def n818 (b : ℝ) : ℝ := (n817 b) * (n605 b)
def i818 : RationalInterval := ⟨(3646130673079469999181085575733 / 1000000000000000000000000000000 : ℚ), (3646130675574285781292483813271 / 1000000000000000000000000000000 : ℚ)⟩
theorem b818 (b : ℝ) (hb : rootInterval.Contains b) : i818.Contains (n818 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b817 b hb) (b605 b hb))
    (by norm_num [i818, i817, i605, RationalInterval.mul]) (by norm_num [i818, i817, i605, RationalInterval.mul])

def n819 (b : ℝ) : ℝ := (n817 b) * (n606 b)
def i819 : RationalInterval := ⟨(3646130673079469999181085575733 / 1000000000000000000000000000000 : ℚ), (3646130675574285781292483813271 / 1000000000000000000000000000000 : ℚ)⟩
theorem b819 (b : ℝ) (hb : rootInterval.Contains b) : i819.Contains (n819 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b817 b hb) (b606 b hb))
    (by norm_num [i819, i817, i606, RationalInterval.mul]) (by norm_num [i819, i817, i606, RationalInterval.mul])

def n820 (b : ℝ) : ℝ := (n817 b) * (n607 b)
def i820 : RationalInterval := ⟨(670823325267183210939716519869 / 500000000000000000000000000000 : ℚ), (26832933029338704423715202233 / 20000000000000000000000000000 : ℚ)⟩
theorem b820 (b : ℝ) (hb : rootInterval.Contains b) : i820.Contains (n820 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b817 b hb) (b607 b hb))
    (by norm_num [i820, i817, i607, RationalInterval.mul]) (by norm_num [i820, i817, i607, RationalInterval.mul])

def n821 (b : ℝ) : ℝ := (n816 b) + (n817 b)
def i821 : RationalInterval := ⟨(-125000000781123491402535582813 / 125000000000000000000000000000 : ℚ), (-124999999218876508597464417187 / 125000000000000000000000000000 : ℚ)⟩
theorem b821 (b : ℝ) (hb : rootInterval.Contains b) : i821.Contains (n821 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b816 b hb) (b817 b hb))
    (by norm_num [i821, i816, i817, RationalInterval.add]) (by norm_num [i821, i816, i817, RationalInterval.add])

def n822 (b : ℝ) : ℝ := (n813 b) + (n818 b)
def i822 : RationalInterval := ⟨(-172653867596670930199807713301 / 1000000000000000000000000000000 : ℚ), (-172653861810095492274994601581 / 1000000000000000000000000000000 : ℚ)⟩
theorem b822 (b : ℝ) (hb : rootInterval.Contains b) : i822.Contains (n822 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b813 b hb) (b818 b hb))
    (by norm_num [i822, i813, i818, RationalInterval.add]) (by norm_num [i822, i813, i818, RationalInterval.add])

def n823 (b : ℝ) : ℝ := (n814 b) + (n819 b)
def i823 : RationalInterval := ⟨(-172653867596670930199807713301 / 1000000000000000000000000000000 : ℚ), (-172653861810095492274994601581 / 1000000000000000000000000000000 : ℚ)⟩
theorem b823 (b : ℝ) (hb : rootInterval.Contains b) : i823.Contains (n823 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b814 b hb) (b819 b hb))
    (by norm_num [i823, i814, i819, RationalInterval.add]) (by norm_num [i823, i814, i819, RationalInterval.add])

def n824 (b : ℝ) : ℝ := (n815 b) + (n820 b)
def i824 : RationalInterval := ⟨(59220469072788026302631726163 / 500000000000000000000000000000 : ℚ), (59220470401328762459967116397 / 500000000000000000000000000000 : ℚ)⟩
theorem b824 (b : ℝ) (hb : rootInterval.Contains b) : i824.Contains (n824 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b815 b hb) (b820 b hb))
    (by norm_num [i824, i815, i820, RationalInterval.add]) (by norm_num [i824, i815, i820, RationalInterval.add])

def n825 (b : ℝ) : ℝ := (n785 b) + (n796 b)
def i825 : RationalInterval := ⟨(4690246356969087695994518179909 / 1000000000000000000000000000000 : ℚ), (4690246359935206650686777911017 / 1000000000000000000000000000000 : ℚ)⟩
theorem b825 (b : ℝ) (hb : rootInterval.Contains b) : i825.Contains (n825 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b785 b hb) (b796 b hb))
    (by norm_num [i825, i785, i796, RationalInterval.add]) (by norm_num [i825, i785, i796, RationalInterval.add])

def n826 (b : ℝ) : ℝ := (n825 b) * (n57 b)
def i826 : RationalInterval := ⟨(4690246356969087695994518179909 / 250000000000000000000000000000 : ℚ), (4690246359935206650686777911017 / 250000000000000000000000000000 : ℚ)⟩
theorem b826 (b : ℝ) (hb : rootInterval.Contains b) : i826.Contains (n826 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b825 b hb) (b57 b hb))
    (by norm_num [i826, i825, i57, RationalInterval.mul]) (by norm_num [i826, i825, i57, RationalInterval.mul])

def n827 (b : ℝ) : ℝ := (n663 b) * (n785 b)
def i827 : RationalInterval := ⟨(1969072359905750761775431517117 / 500000000000000000000000000000 : ℚ), (1969072361246377964870552050109 / 500000000000000000000000000000 : ℚ)⟩
theorem b827 (b : ℝ) (hb : rootInterval.Contains b) : i827.Contains (n827 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b663 b hb) (b785 b hb))
    (by norm_num [i827, i663, i785, RationalInterval.mul]) (by norm_num [i827, i663, i785, RationalInterval.mul])

def n828 (b : ℝ) : ℝ := (n827 b) * (n665 b)
def i828 : RationalInterval := ⟨(1969072359905750761775431517117 / 62500000000000000000000000000 : ℚ), (1969072361246377964870552050109 / 62500000000000000000000000000 : ℚ)⟩
theorem b828 (b : ℝ) (hb : rootInterval.Contains b) : i828.Contains (n828 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b827 b hb) (b665 b hb))
    (by norm_num [i828, i827, i665, RationalInterval.mul]) (by norm_num [i828, i827, i665, RationalInterval.mul])

def n829 (b : ℝ) : ℝ := -(n828 b)
def i829 : RationalInterval := ⟨(-1969072361246377964870552050109 / 62500000000000000000000000000 : ℚ), (-1969072359905750761775431517117 / 62500000000000000000000000000 : ℚ)⟩
theorem b829 (b : ℝ) (hb : rootInterval.Contains b) : i829.Contains (n829 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b828 b hb))
    (by norm_num [i829, i828, RationalInterval.neg]) (by norm_num [i829, i828, RationalInterval.neg])

def n830 (b : ℝ) : ℝ := (n826 b) + (n829 b)
def i830 : RationalInterval := ⟨(-3186043088016424163487690020527 / 250000000000000000000000000000 : ℚ), (-3186043079687796396414948157451 / 250000000000000000000000000000 : ℚ)⟩
theorem b830 (b : ℝ) (hb : rootInterval.Contains b) : i830.Contains (n830 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b826 b hb) (b829 b hb))
    (by norm_num [i830, i826, i829, RationalInterval.add]) (by norm_num [i830, i826, i829, RationalInterval.add])

def n831 (b : ℝ) : ℝ := (n830 b) * (n64 b)
def i831 : RationalInterval := ⟨(-3186043088016424163487690020527 / 500000000000000000000000000000 : ℚ), (-3186043079687796396414948157451 / 500000000000000000000000000000 : ℚ)⟩
theorem b831 (b : ℝ) (hb : rootInterval.Contains b) : i831.Contains (n831 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b830 b hb) (b64 b hb))
    (by norm_num [i831, i830, i64, RationalInterval.mul]) (by norm_num [i831, i830, i64, RationalInterval.mul])

def n832 (b : ℝ) : ℝ := (n830 b) * (n58 b)
def i832 : RationalInterval := ⟨(-3186043088016424163487690020527 / 1000000000000000000000000000000 : ℚ), (-3186043079687796396414948157451 / 1000000000000000000000000000000 : ℚ)⟩
theorem b832 (b : ℝ) (hb : rootInterval.Contains b) : i832.Contains (n832 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b830 b hb) (b58 b hb))
    (by norm_num [i832, i830, i58, RationalInterval.mul]) (by norm_num [i832, i830, i58, RationalInterval.mul])

def n833 (b : ℝ) : ℝ := (n821 b) + (n830 b)
def i833 : RationalInterval := ⟨(-3436043089578671146292761186153 / 250000000000000000000000000000 : ℚ), (-137441723125021976544395079673 / 10000000000000000000000000000 : ℚ)⟩
theorem b833 (b : ℝ) (hb : rootInterval.Contains b) : i833.Contains (n833 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b821 b hb) (b830 b hb))
    (by norm_num [i833, i821, i830, RationalInterval.add]) (by norm_num [i833, i821, i830, RationalInterval.add])

def n834 (b : ℝ) : ℝ := (n822 b) + (n831 b)
def i834 : RationalInterval := ⟨(-1308948008725903851435037550871 / 200000000000000000000000000000 : ℚ), (-6544740021185688285104890916483 / 1000000000000000000000000000000 : ℚ)⟩
theorem b834 (b : ℝ) (hb : rootInterval.Contains b) : i834.Contains (n834 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b822 b hb) (b831 b hb))
    (by norm_num [i834, i822, i831, RationalInterval.add]) (by norm_num [i834, i822, i831, RationalInterval.add])

def n835 (b : ℝ) : ℝ := (n823 b) + (n831 b)
def i835 : RationalInterval := ⟨(-1308948008725903851435037550871 / 200000000000000000000000000000 : ℚ), (-6544740021185688285104890916483 / 1000000000000000000000000000000 : ℚ)⟩
theorem b835 (b : ℝ) (hb : rootInterval.Contains b) : i835.Contains (n835 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b823 b hb) (b831 b hb))
    (by norm_num [i835, i823, i831, RationalInterval.add]) (by norm_num [i835, i823, i831, RationalInterval.add])

def n836 (b : ℝ) : ℝ := (n824 b) + (n832 b)
def i836 : RationalInterval := ⟨(-3067602149870848110882426568201 / 1000000000000000000000000000000 : ℚ), (-3067602138885138871495013924657 / 1000000000000000000000000000000 : ℚ)⟩
theorem b836 (b : ℝ) (hb : rootInterval.Contains b) : i836.Contains (n836 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b824 b hb) (b832 b hb))
    (by norm_num [i836, i824, i832, RationalInterval.add]) (by norm_num [i836, i824, i832, RationalInterval.add])

def n837 (b : ℝ) : ℝ := (n675 b) * (n13 b)
def i837 : RationalInterval := ⟨(85445259791 / 12500000000 : ℚ), (68356207833 / 10000000000 : ℚ)⟩
theorem b837 (b : ℝ) (hb : rootInterval.Contains b) : i837.Contains (n837 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b675 b hb) (b13 b hb))
    (by norm_num [i837, i675, i13, RationalInterval.mul]) (by norm_num [i837, i675, i13, RationalInterval.mul])

def n838 (b : ℝ) : ℝ := (n675 b) * (n64 b)
def i838 : RationalInterval := ⟨(85445259791 / 50000000000 : ℚ), (68356207833 / 40000000000 : ℚ)⟩
theorem b838 (b : ℝ) (hb : rootInterval.Contains b) : i838.Contains (n838 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b675 b hb) (b64 b hb))
    (by norm_num [i838, i675, i64, RationalInterval.mul]) (by norm_num [i838, i675, i64, RationalInterval.mul])

def n839 (b : ℝ) : ℝ := (n833 b) + (n837 b)
def i839 : RationalInterval := ⟨(-1727137893758671146292761186153 / 250000000000000000000000000000 : ℚ), (-69085515292021976544395079673 / 10000000000000000000000000000 : ℚ)⟩
theorem b839 (b : ℝ) (hb : rootInterval.Contains b) : i839.Contains (n839 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b833 b hb) (b837 b hb))
    (by norm_num [i839, i833, i837, RationalInterval.add]) (by norm_num [i839, i833, i837, RationalInterval.add])

def n840 (b : ℝ) : ℝ := (n834 b) + (n838 b)
def i840 : RationalInterval := ⟨(-967166969561903851435037550871 / 200000000000000000000000000000 : ℚ), (-4835834825360688285104890916483 / 1000000000000000000000000000000 : ℚ)⟩
theorem b840 (b : ℝ) (hb : rootInterval.Contains b) : i840.Contains (n840 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b834 b hb) (b838 b hb))
    (by norm_num [i840, i834, i838, RationalInterval.add]) (by norm_num [i840, i834, i838, RationalInterval.add])

def n841 (b : ℝ) : ℝ := (n835 b) + (n838 b)
def i841 : RationalInterval := ⟨(-967166969561903851435037550871 / 200000000000000000000000000000 : ℚ), (-4835834825360688285104890916483 / 1000000000000000000000000000000 : ℚ)⟩
theorem b841 (b : ℝ) (hb : rootInterval.Contains b) : i841.Contains (n841 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b835 b hb) (b838 b hb))
    (by norm_num [i841, i835, i838, RationalInterval.add]) (by norm_num [i841, i835, i838, RationalInterval.add])

def n842 (b : ℝ) : ℝ := (n197 b) * (n16 b)
def i842 : RationalInterval := ⟨(389067928155278712648699664163 / 1000000000000000000000000000000 : ℚ), (97266982230677460743126848381 / 250000000000000000000000000000 : ℚ)⟩
theorem b842 (b : ℝ) (hb : rootInterval.Contains b) : i842.Contains (n842 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b197 b hb) (b16 b hb))
    (by norm_num [i842, i197, i16, RationalInterval.mul]) (by norm_num [i842, i197, i16, RationalInterval.mul])

def n843 (b : ℝ) : ℝ := (n199 b) * (n16 b)
def i843 : RationalInterval := ⟨(-6311375785235329689686924373 / 62500000000000000000000000000 : ℚ), (-25245503061196577524106475969 / 250000000000000000000000000000 : ℚ)⟩
theorem b843 (b : ℝ) (hb : rootInterval.Contains b) : i843.Contains (n843 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b199 b hb) (b16 b hb))
    (by norm_num [i843, i199, i16, RationalInterval.mul]) (by norm_num [i843, i199, i16, RationalInterval.mul])

def n844 (b : ℝ) : ℝ := (n842 b) * (n16 b)
def i844 : RationalInterval := ⟨(-97266982230677460743126848381 / 250000000000000000000000000000 : ℚ), (-389067928155278712648699664163 / 1000000000000000000000000000000 : ℚ)⟩
theorem b844 (b : ℝ) (hb : rootInterval.Contains b) : i844.Contains (n844 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b842 b hb) (b16 b hb))
    (by norm_num [i844, i842, i16, RationalInterval.mul]) (by norm_num [i844, i842, i16, RationalInterval.mul])

def n845 (b : ℝ) : ℝ := (n152 b) * (n843 b)
def i845 : RationalInterval := ⟨(25245503061196577524106475969 / 500000000000000000000000000000 : ℚ), (6311375785235329689686924373 / 125000000000000000000000000000 : ℚ)⟩
theorem b845 (b : ℝ) (hb : rootInterval.Contains b) : i845.Contains (n845 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b152 b hb) (b843 b hb))
    (by norm_num [i845, i152, i843, RationalInterval.mul]) (by norm_num [i845, i152, i843, RationalInterval.mul])

def n846 (b : ℝ) : ℝ := (n844 b) + (n845 b)
def i846 : RationalInterval := ⟨(-169288461400158343962147220793 / 500000000000000000000000000000 : ℚ), (-338576921873396075131204269179 / 1000000000000000000000000000000 : ℚ)⟩
theorem b846 (b : ℝ) (hb : rootInterval.Contains b) : i846.Contains (n846 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b844 b hb) (b845 b hb))
    (by norm_num [i846, i844, i845, RationalInterval.add]) (by norm_num [i846, i844, i845, RationalInterval.add])

def n847 (b : ℝ) : ℝ := (n16 b) + (n846 b)
def i847 : RationalInterval := ⟨(-669288461400158343962147220793 / 500000000000000000000000000000 : ℚ), (-1338576921873396075131204269179 / 1000000000000000000000000000000 : ℚ)⟩
theorem b847 (b : ℝ) (hb : rootInterval.Contains b) : i847.Contains (n847 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b16 b hb) (b846 b hb))
    (by norm_num [i847, i16, i846, RationalInterval.add]) (by norm_num [i847, i16, i846, RationalInterval.add])

def n848 (b : ℝ) : ℝ := (n843 b) * (n64 b)
def i848 : RationalInterval := ⟨(-6311375785235329689686924373 / 125000000000000000000000000000 : ℚ), (-25245503061196577524106475969 / 500000000000000000000000000000 : ℚ)⟩
theorem b848 (b : ℝ) (hb : rootInterval.Contains b) : i848.Contains (n848 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b843 b hb) (b64 b hb))
    (by norm_num [i848, i843, i64, RationalInterval.mul]) (by norm_num [i848, i843, i64, RationalInterval.mul])

def n849 (b : ℝ) : ℝ := (n842 b) + (n848 b)
def i849 : RationalInterval := ⟨(338576921873396075131204269179 / 1000000000000000000000000000000 : ℚ), (169288461400158343962147220793 / 500000000000000000000000000000 : ℚ)⟩
theorem b849 (b : ℝ) (hb : rootInterval.Contains b) : i849.Contains (n849 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b842 b hb) (b848 b hb))
    (by norm_num [i849, i842, i848, RationalInterval.add]) (by norm_num [i849, i842, i848, RationalInterval.add])

def n850 (b : ℝ) : ℝ := (n842 b) * (n64 b)
def i850 : RationalInterval := ⟨(194533964077639356324349832081 / 1000000000000000000000000000000 : ℚ), (97266982230677460743126848381 / 500000000000000000000000000000 : ℚ)⟩
theorem b850 (b : ℝ) (hb : rootInterval.Contains b) : i850.Contains (n850 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b842 b hb) (b64 b hb))
    (by norm_num [i850, i842, i64, RationalInterval.mul]) (by norm_num [i850, i842, i64, RationalInterval.mul])

def n851 (b : ℝ) : ℝ := (n61 b) * (n843 b)
def i851 : RationalInterval := ⟨(-7158667339131863259801512969 / 200000000000000000000000000000 : ℚ), (-17896668291171969233240512117 / 500000000000000000000000000000 : ℚ)⟩
theorem b851 (b : ℝ) (hb : rootInterval.Contains b) : i851.Contains (n851 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b61 b hb) (b843 b hb))
    (by norm_num [i851, i61, i843, RationalInterval.mul]) (by norm_num [i851, i61, i843, RationalInterval.mul])

def n852 (b : ℝ) : ℝ := (n850 b) + (n851 b)
def i852 : RationalInterval := ⟨(39685156845495010006335566809 / 250000000000000000000000000000 : ℚ), (9921289242438186438735792033 / 62500000000000000000000000000 : ℚ)⟩
theorem b852 (b : ℝ) (hb : rootInterval.Contains b) : i852.Contains (n852 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b850 b hb) (b851 b hb))
    (by norm_num [i852, i850, i851, RationalInterval.add]) (by norm_num [i852, i850, i851, RationalInterval.add])

def n853 (b : ℝ) : ℝ := (n849 b) + (n15 b)
def i853 : RationalInterval := ⟨(1338576921873396075131204269179 / 1000000000000000000000000000000 : ℚ), (669288461400158343962147220793 / 500000000000000000000000000000 : ℚ)⟩
theorem b853 (b : ℝ) (hb : rootInterval.Contains b) : i853.Contains (n853 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b849 b hb) (b15 b hb))
    (by norm_num [i853, i849, i15, RationalInterval.add]) (by norm_num [i853, i849, i15, RationalInterval.add])

def n854 (b : ℝ) : ℝ := (n852 b) + (n16 b)
def i854 : RationalInterval := ⟨(-210314843154504989993664433191 / 250000000000000000000000000000 : ℚ), (-52578710757561813561264207967 / 62500000000000000000000000000 : ℚ)⟩
theorem b854 (b : ℝ) (hb : rootInterval.Contains b) : i854.Contains (n854 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b852 b hb) (b16 b hb))
    (by norm_num [i854, i852, i16, RationalInterval.add]) (by norm_num [i854, i852, i16, RationalInterval.add])

def n855 (b : ℝ) : ℝ := (n842 b) * (n152 b)
def i855 : RationalInterval := ⟨(-97266982230677460743126848381 / 500000000000000000000000000000 : ℚ), (-194533964077639356324349832081 / 1000000000000000000000000000000 : ℚ)⟩
theorem b855 (b : ℝ) (hb : rootInterval.Contains b) : i855.Contains (n855 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b842 b hb) (b152 b hb))
    (by norm_num [i855, i842, i152, RationalInterval.mul]) (by norm_num [i855, i842, i152, RationalInterval.mul])

def n856 (b : ℝ) : ℝ := (n843 b) * (n600 b)
def i856 : RationalInterval := ⟨(1837208692474595193889995241 / 125000000000000000000000000000 : ℚ), (14697669586475776249897243327 / 1000000000000000000000000000000 : ℚ)⟩
theorem b856 (b : ℝ) (hb : rootInterval.Contains b) : i856.Contains (n856 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b843 b hb) (b600 b hb))
    (by norm_num [i856, i843, i600, RationalInterval.mul]) (by norm_num [i856, i843, i600, RationalInterval.mul])

def n857 (b : ℝ) : ℝ := (n855 b) + (n856 b)
def i857 : RationalInterval := ⟨(-89918147460779079967566867417 / 500000000000000000000000000000 : ℚ), (-89918147245581790037226294377 / 500000000000000000000000000000 : ℚ)⟩
theorem b857 (b : ℝ) (hb : rootInterval.Contains b) : i857.Contains (n857 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b855 b hb) (b856 b hb))
    (by norm_num [i857, i855, i856, RationalInterval.add]) (by norm_num [i857, i855, i856, RationalInterval.add])

def n858 (b : ℝ) : ℝ := (n857 b) * (n13 b)
def i858 : RationalInterval := ⟨(-89918147460779079967566867417 / 250000000000000000000000000000 : ℚ), (-89918147245581790037226294377 / 250000000000000000000000000000 : ℚ)⟩
theorem b858 (b : ℝ) (hb : rootInterval.Contains b) : i858.Contains (n858 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b857 b hb) (b13 b hb))
    (by norm_num [i858, i857, i13, RationalInterval.mul]) (by norm_num [i858, i857, i13, RationalInterval.mul])

def n859 (b : ℝ) : ℝ := (n858 b) + (n413 b)
def i859 : RationalInterval := ⟨(-589918147460779079967566867417 / 250000000000000000000000000000 : ℚ), (-589918147245581790037226294377 / 250000000000000000000000000000 : ℚ)⟩
theorem b859 (b : ℝ) (hb : rootInterval.Contains b) : i859.Contains (n859 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b858 b hb) (b413 b hb))
    (by norm_num [i859, i858, i413, RationalInterval.add]) (by norm_num [i859, i858, i413, RationalInterval.add])

def n860 (b : ℝ) : ℝ := (n853 b) * (n16 b)
def i860 : RationalInterval := ⟨(-669288461400158343962147220793 / 500000000000000000000000000000 : ℚ), (-1338576921873396075131204269179 / 1000000000000000000000000000000 : ℚ)⟩
theorem b860 (b : ℝ) (hb : rootInterval.Contains b) : i860.Contains (n860 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b853 b hb) (b16 b hb))
    (by norm_num [i860, i853, i16, RationalInterval.mul]) (by norm_num [i860, i853, i16, RationalInterval.mul])

def n861 (b : ℝ) : ℝ := (n853 b) * (n152 b)
def i861 : RationalInterval := ⟨(-669288461400158343962147220793 / 1000000000000000000000000000000 : ℚ), (-669288460936698037565602134589 / 1000000000000000000000000000000 : ℚ)⟩
theorem b861 (b : ℝ) (hb : rootInterval.Contains b) : i861.Contains (n861 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b853 b hb) (b152 b hb))
    (by norm_num [i861, i853, i152, RationalInterval.mul]) (by norm_num [i861, i853, i152, RationalInterval.mul])

def n862 (b : ℝ) : ℝ := (n854 b) * (n16 b)
def i862 : RationalInterval := ⟨(52578710757561813561264207967 / 62500000000000000000000000000 : ℚ), (210314843154504989993664433191 / 250000000000000000000000000000 : ℚ)⟩
theorem b862 (b : ℝ) (hb : rootInterval.Contains b) : i862.Contains (n862 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b854 b hb) (b16 b hb))
    (by norm_num [i862, i854, i16, RationalInterval.mul]) (by norm_num [i862, i854, i16, RationalInterval.mul])

def n863 (b : ℝ) : ℝ := (n854 b) * (n152 b)
def i863 : RationalInterval := ⟨(52578710757561813561264207967 / 125000000000000000000000000000 : ℚ), (210314843154504989993664433191 / 500000000000000000000000000000 : ℚ)⟩
theorem b863 (b : ℝ) (hb : rootInterval.Contains b) : i863.Contains (n863 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b854 b hb) (b152 b hb))
    (by norm_num [i863, i854, i152, RationalInterval.mul]) (by norm_num [i863, i854, i152, RationalInterval.mul])

def n864 (b : ℝ) : ℝ := (n861 b) + (n64 b)
def i864 : RationalInterval := ⟨(-169288461400158343962147220793 / 1000000000000000000000000000000 : ℚ), (-169288460936698037565602134589 / 1000000000000000000000000000000 : ℚ)⟩
theorem b864 (b : ℝ) (hb : rootInterval.Contains b) : i864.Contains (n864 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b861 b hb) (b64 b hb))
    (by norm_num [i864, i861, i64, RationalInterval.add]) (by norm_num [i864, i861, i64, RationalInterval.add])

def n865 (b : ℝ) : ℝ := (n863 b) + (n602 b)
def i865 : RationalInterval := ⟨(70772136018499313561264207967 / 125000000000000000000000000000 : ℚ), (283088544199504989993664433191 / 500000000000000000000000000000 : ℚ)⟩
theorem b865 (b : ℝ) (hb : rootInterval.Contains b) : i865.Contains (n865 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b863 b hb) (b602 b hb))
    (by norm_num [i865, i863, i602, RationalInterval.add]) (by norm_num [i865, i863, i602, RationalInterval.add])

def n866 (b : ℝ) : ℝ := (n152 b) * (n853 b)
def i866 : RationalInterval := ⟨(-669288461400158343962147220793 / 1000000000000000000000000000000 : ℚ), (-669288460936698037565602134589 / 1000000000000000000000000000000 : ℚ)⟩
theorem b866 (b : ℝ) (hb : rootInterval.Contains b) : i866.Contains (n866 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b152 b hb) (b853 b hb))
    (by norm_num [i866, i152, i853, RationalInterval.mul]) (by norm_num [i866, i152, i853, RationalInterval.mul])

def n867 (b : ℝ) : ℝ := (n152 b) * (n854 b)
def i867 : RationalInterval := ⟨(52578710757561813561264207967 / 125000000000000000000000000000 : ℚ), (210314843154504989993664433191 / 500000000000000000000000000000 : ℚ)⟩
theorem b867 (b : ℝ) (hb : rootInterval.Contains b) : i867.Contains (n867 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b152 b hb) (b854 b hb))
    (by norm_num [i867, i152, i854, RationalInterval.mul]) (by norm_num [i867, i152, i854, RationalInterval.mul])

def n868 (b : ℝ) : ℝ := (n64 b) + (n866 b)
def i868 : RationalInterval := ⟨(-169288461400158343962147220793 / 1000000000000000000000000000000 : ℚ), (-169288460936698037565602134589 / 1000000000000000000000000000000 : ℚ)⟩
theorem b868 (b : ℝ) (hb : rootInterval.Contains b) : i868.Contains (n868 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b64 b hb) (b866 b hb))
    (by norm_num [i868, i64, i866, RationalInterval.add]) (by norm_num [i868, i64, i866, RationalInterval.add])

def n869 (b : ℝ) : ℝ := (n803 b) + (n867 b)
def i869 : RationalInterval := ⟨(70772136018499313561264207967 / 125000000000000000000000000000 : ℚ), (283088544199504989993664433191 / 500000000000000000000000000000 : ℚ)⟩
theorem b869 (b : ℝ) (hb : rootInterval.Contains b) : i869.Contains (n869 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b803 b hb) (b867 b hb))
    (by norm_num [i869, i803, i867, RationalInterval.add]) (by norm_num [i869, i803, i867, RationalInterval.add])

def n870 (b : ℝ) : ℝ := (n860 b) + (n860 b)
def i870 : RationalInterval := ⟨(-669288461400158343962147220793 / 250000000000000000000000000000 : ℚ), (-1338576921873396075131204269179 / 500000000000000000000000000000 : ℚ)⟩
theorem b870 (b : ℝ) (hb : rootInterval.Contains b) : i870.Contains (n870 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b860 b hb) (b860 b hb))
    (by norm_num [i870, i860, i860, RationalInterval.add]) (by norm_num [i870, i860, i860, RationalInterval.add])

def n871 (b : ℝ) : ℝ := (n864 b) + (n862 b)
def i871 : RationalInterval := ⟨(671970910720830673018080106679 / 1000000000000000000000000000000 : ℚ), (26878836467252876896362223927 / 40000000000000000000000000000 : ℚ)⟩
theorem b871 (b : ℝ) (hb : rootInterval.Contains b) : i871.Contains (n871 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b864 b hb) (b862 b hb))
    (by norm_num [i871, i864, i862, RationalInterval.add]) (by norm_num [i871, i864, i862, RationalInterval.add])

def n872 (b : ℝ) : ℝ := (n862 b) + (n868 b)
def i872 : RationalInterval := ⟨(671970910720830673018080106679 / 1000000000000000000000000000000 : ℚ), (26878836467252876896362223927 / 40000000000000000000000000000 : ℚ)⟩
theorem b872 (b : ℝ) (hb : rootInterval.Contains b) : i872.Contains (n872 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b862 b hb) (b868 b hb))
    (by norm_num [i872, i862, i868, RationalInterval.add]) (by norm_num [i872, i862, i868, RationalInterval.add])

def n873 (b : ℝ) : ℝ := (n865 b) + (n869 b)
def i873 : RationalInterval := ⟨(70772136018499313561264207967 / 62500000000000000000000000000 : ℚ), (283088544199504989993664433191 / 250000000000000000000000000000 : ℚ)⟩
theorem b873 (b : ℝ) (hb : rootInterval.Contains b) : i873.Contains (n873 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b865 b hb) (b869 b hb))
    (by norm_num [i873, i865, i869, RationalInterval.add]) (by norm_num [i873, i865, i869, RationalInterval.add])

def n874 (b : ℝ) : ℝ := (n413 b) * (n870 b)
def i874 : RationalInterval := ⟨(1338576921873396075131204269179 / 250000000000000000000000000000 : ℚ), (669288461400158343962147220793 / 125000000000000000000000000000 : ℚ)⟩
theorem b874 (b : ℝ) (hb : rootInterval.Contains b) : i874.Contains (n874 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b413 b hb) (b870 b hb))
    (by norm_num [i874, i413, i870, RationalInterval.mul]) (by norm_num [i874, i413, i870, RationalInterval.mul])

def n875 (b : ℝ) : ℝ := (n413 b) * (n871 b)
def i875 : RationalInterval := ⟨(-26878836467252876896362223927 / 20000000000000000000000000000 : ℚ), (-671970910720830673018080106679 / 500000000000000000000000000000 : ℚ)⟩
theorem b875 (b : ℝ) (hb : rootInterval.Contains b) : i875.Contains (n875 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b413 b hb) (b871 b hb))
    (by norm_num [i875, i413, i871, RationalInterval.mul]) (by norm_num [i875, i413, i871, RationalInterval.mul])

def n876 (b : ℝ) : ℝ := (n413 b) * (n872 b)
def i876 : RationalInterval := ⟨(-26878836467252876896362223927 / 20000000000000000000000000000 : ℚ), (-671970910720830673018080106679 / 500000000000000000000000000000 : ℚ)⟩
theorem b876 (b : ℝ) (hb : rootInterval.Contains b) : i876.Contains (n876 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b413 b hb) (b872 b hb))
    (by norm_num [i876, i413, i872, RationalInterval.mul]) (by norm_num [i876, i413, i872, RationalInterval.mul])

def n877 (b : ℝ) : ℝ := (n413 b) * (n873 b)
def i877 : RationalInterval := ⟨(-283088544199504989993664433191 / 125000000000000000000000000000 : ℚ), (-70772136018499313561264207967 / 31250000000000000000000000000 : ℚ)⟩
theorem b877 (b : ℝ) (hb : rootInterval.Contains b) : i877.Contains (n877 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b413 b hb) (b873 b hb))
    (by norm_num [i877, i413, i873, RationalInterval.mul]) (by norm_num [i877, i413, i873, RationalInterval.mul])

def n878 (b : ℝ) : ℝ := (n875 b) + (n15 b)
def i878 : RationalInterval := ⟨(-6878836467252876896362223927 / 20000000000000000000000000000 : ℚ), (-171970910720830673018080106679 / 500000000000000000000000000000 : ℚ)⟩
theorem b878 (b : ℝ) (hb : rootInterval.Contains b) : i878.Contains (n878 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b875 b hb) (b15 b hb))
    (by norm_num [i878, i875, i15, RationalInterval.add]) (by norm_num [i878, i875, i15, RationalInterval.add])

def n879 (b : ℝ) : ℝ := (n876 b) + (n15 b)
def i879 : RationalInterval := ⟨(-6878836467252876896362223927 / 20000000000000000000000000000 : ℚ), (-171970910720830673018080106679 / 500000000000000000000000000000 : ℚ)⟩
theorem b879 (b : ℝ) (hb : rootInterval.Contains b) : i879.Contains (n879 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b876 b hb) (b15 b hb))
    (by norm_num [i879, i876, i15, RationalInterval.add]) (by norm_num [i879, i876, i15, RationalInterval.add])

def n880 (b : ℝ) : ℝ := (n847 b) * (n57 b)
def i880 : RationalInterval := ⟨(-669288461400158343962147220793 / 125000000000000000000000000000 : ℚ), (-1338576921873396075131204269179 / 250000000000000000000000000000 : ℚ)⟩
theorem b880 (b : ℝ) (hb : rootInterval.Contains b) : i880.Contains (n880 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b847 b hb) (b57 b hb))
    (by norm_num [i880, i847, i57, RationalInterval.mul]) (by norm_num [i880, i847, i57, RationalInterval.mul])

def n881 (b : ℝ) : ℝ := (n880 b) * (n605 b)
def i881 : RationalInterval := ⟨(-2117882497245167014950911763863 / 1000000000000000000000000000000 : ℚ), (-529470623941304271099066814379 / 250000000000000000000000000000 : ℚ)⟩
theorem b881 (b : ℝ) (hb : rootInterval.Contains b) : i881.Contains (n881 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b880 b hb) (b605 b hb))
    (by norm_num [i881, i880, i605, RationalInterval.mul]) (by norm_num [i881, i880, i605, RationalInterval.mul])

def n882 (b : ℝ) : ℝ := (n880 b) * (n606 b)
def i882 : RationalInterval := ⟨(-2117882497245167014950911763863 / 1000000000000000000000000000000 : ℚ), (-529470623941304271099066814379 / 250000000000000000000000000000 : ℚ)⟩
theorem b882 (b : ℝ) (hb : rootInterval.Contains b) : i882.Contains (n882 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b880 b hb) (b606 b hb))
    (by norm_num [i882, i880, i606, RationalInterval.mul]) (by norm_num [i882, i880, i606, RationalInterval.mul])

def n883 (b : ℝ) : ℝ := (n880 b) * (n607 b)
def i883 : RationalInterval := ⟨(-779305574444850327026617322277 / 1000000000000000000000000000000 : ℚ), (-779305573891821009265062988337 / 1000000000000000000000000000000 : ℚ)⟩
theorem b883 (b : ℝ) (hb : rootInterval.Contains b) : i883.Contains (n883 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b880 b hb) (b607 b hb))
    (by norm_num [i883, i880, i607, RationalInterval.mul]) (by norm_num [i883, i880, i607, RationalInterval.mul])

def n884 (b : ℝ) : ℝ := (n874 b) + (n880 b)
def i884 : RationalInterval := ⟨(-926920612793090172407 / 250000000000000000000000000000 : ℚ), (926920612793090172407 / 250000000000000000000000000000 : ℚ)⟩
theorem b884 (b : ℝ) (hb : rootInterval.Contains b) : i884.Contains (n884 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b874 b hb) (b880 b hb))
    (by norm_num [i884, i874, i880, RationalInterval.add]) (by norm_num [i884, i874, i880, RationalInterval.add])

def n885 (b : ℝ) : ℝ := (n878 b) + (n881 b)
def i885 : RationalInterval := ⟨(-2461824320607810859769022960213 / 1000000000000000000000000000000 : ℚ), (-1230912158603439215216213735437 / 500000000000000000000000000000 : ℚ)⟩
theorem b885 (b : ℝ) (hb : rootInterval.Contains b) : i885.Contains (n885 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b878 b hb) (b881 b hb))
    (by norm_num [i885, i878, i881, RationalInterval.add]) (by norm_num [i885, i878, i881, RationalInterval.add])

def n886 (b : ℝ) : ℝ := (n879 b) + (n882 b)
def i886 : RationalInterval := ⟨(-2461824320607810859769022960213 / 1000000000000000000000000000000 : ℚ), (-1230912158603439215216213735437 / 500000000000000000000000000000 : ℚ)⟩
theorem b886 (b : ℝ) (hb : rootInterval.Contains b) : i886.Contains (n886 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b879 b hb) (b882 b hb))
    (by norm_num [i886, i879, i882, RationalInterval.add]) (by norm_num [i886, i879, i882, RationalInterval.add])

def n887 (b : ℝ) : ℝ := (n877 b) + (n883 b)
def i887 : RationalInterval := ⟨(-608802785608178049395186557561 / 200000000000000000000000000000 : ℚ), (-3044013926483799043225517643281 / 1000000000000000000000000000000 : ℚ)⟩
theorem b887 (b : ℝ) (hb : rootInterval.Contains b) : i887.Contains (n887 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b877 b hb) (b883 b hb))
    (by norm_num [i887, i877, i883, RationalInterval.add]) (by norm_num [i887, i877, i883, RationalInterval.add])

def n888 (b : ℝ) : ℝ := (n847 b) + (n859 b)
def i888 : RationalInterval := ⟨(-1849124756321716503897280955627 / 500000000000000000000000000000 : ℚ), (-3698249510855723235280109446687 / 1000000000000000000000000000000 : ℚ)⟩
theorem b888 (b : ℝ) (hb : rootInterval.Contains b) : i888.Contains (n888 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b847 b hb) (b859 b hb))
    (by norm_num [i888, i847, i859, RationalInterval.add]) (by norm_num [i888, i847, i859, RationalInterval.add])

def n889 (b : ℝ) : ℝ := (n888 b) * (n57 b)
def i889 : RationalInterval := ⟨(-1849124756321716503897280955627 / 125000000000000000000000000000 : ℚ), (-3698249510855723235280109446687 / 250000000000000000000000000000 : ℚ)⟩
theorem b889 (b : ℝ) (hb : rootInterval.Contains b) : i889.Contains (n889 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b888 b hb) (b57 b hb))
    (by norm_num [i889, i888, i57, RationalInterval.mul]) (by norm_num [i889, i888, i57, RationalInterval.mul])

def n890 (b : ℝ) : ℝ := (n663 b) * (n847 b)
def i890 : RationalInterval := ⟨(-1143750529192450548474640902737 / 500000000000000000000000000000 : ℚ), (-2287501056794188761020510063813 / 1000000000000000000000000000000 : ℚ)⟩
theorem b890 (b : ℝ) (hb : rootInterval.Contains b) : i890.Contains (n890 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b663 b hb) (b847 b hb))
    (by norm_num [i890, i663, i847, RationalInterval.mul]) (by norm_num [i890, i663, i847, RationalInterval.mul])

def n891 (b : ℝ) : ℝ := (n890 b) * (n665 b)
def i891 : RationalInterval := ⟨(-1143750529192450548474640902737 / 62500000000000000000000000000 : ℚ), (-2287501056794188761020510063813 / 125000000000000000000000000000 : ℚ)⟩
theorem b891 (b : ℝ) (hb : rootInterval.Contains b) : i891.Contains (n891 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b890 b hb) (b665 b hb))
    (by norm_num [i891, i890, i665, RationalInterval.mul]) (by norm_num [i891, i890, i665, RationalInterval.mul])

def n892 (b : ℝ) : ℝ := -(n891 b)
def i892 : RationalInterval := ⟨(2287501056794188761020510063813 / 125000000000000000000000000000 : ℚ), (1143750529192450548474640902737 / 62500000000000000000000000000 : ℚ)⟩
theorem b892 (b : ℝ) (hb : rootInterval.Contains b) : i892.Contains (n892 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b891 b hb))
    (by norm_num [i892, i891, RationalInterval.neg]) (by norm_num [i892, i891, RationalInterval.neg])

def n893 (b : ℝ) : ℝ := (n889 b) + (n892 b)
def i893 : RationalInterval := ⟨(219188150236236128561614554093 / 62500000000000000000000000000 : ℚ), (876752605914078958618454164261 / 250000000000000000000000000000 : ℚ)⟩
theorem b893 (b : ℝ) (hb : rootInterval.Contains b) : i893.Contains (n893 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b889 b hb) (b892 b hb))
    (by norm_num [i893, i889, i892, RationalInterval.add]) (by norm_num [i893, i889, i892, RationalInterval.add])

def n894 (b : ℝ) : ℝ := (n893 b) * (n64 b)
def i894 : RationalInterval := ⟨(219188150236236128561614554093 / 125000000000000000000000000000 : ℚ), (876752605914078958618454164261 / 500000000000000000000000000000 : ℚ)⟩
theorem b894 (b : ℝ) (hb : rootInterval.Contains b) : i894.Contains (n894 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b893 b hb) (b64 b hb))
    (by norm_num [i894, i893, i64, RationalInterval.mul]) (by norm_num [i894, i893, i64, RationalInterval.mul])

def n895 (b : ℝ) : ℝ := (n893 b) * (n58 b)
def i895 : RationalInterval := ⟨(219188150236236128561614554093 / 250000000000000000000000000000 : ℚ), (876752605914078958618454164261 / 1000000000000000000000000000000 : ℚ)⟩
theorem b895 (b : ℝ) (hb : rootInterval.Contains b) : i895.Contains (n895 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b893 b hb) (b58 b hb))
    (by norm_num [i895, i893, i58, RationalInterval.mul]) (by norm_num [i895, i893, i58, RationalInterval.mul])

def n896 (b : ℝ) : ℝ := (n884 b) + (n893 b)
def i896 : RationalInterval := ⟨(175350520003604780290673608793 / 50000000000000000000000000000 : ℚ), (219188151710249892852886084167 / 62500000000000000000000000000 : ℚ)⟩
theorem b896 (b : ℝ) (hb : rootInterval.Contains b) : i896.Contains (n896 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b884 b hb) (b893 b hb))
    (by norm_num [i896, i884, i893, RationalInterval.add]) (by norm_num [i896, i884, i893, RationalInterval.add])

def n897 (b : ℝ) : ℝ := (n885 b) + (n894 b)
def i897 : RationalInterval := ⟨(-708319118717921831276106527469 / 1000000000000000000000000000000 : ℚ), (-44269944086170032074719946397 / 62500000000000000000000000000 : ℚ)⟩
theorem b897 (b : ℝ) (hb : rootInterval.Contains b) : i897.Contains (n897 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b885 b hb) (b894 b hb))
    (by norm_num [i897, i885, i894, RationalInterval.add]) (by norm_num [i897, i885, i894, RationalInterval.add])

def n898 (b : ℝ) : ℝ := (n886 b) + (n894 b)
def i898 : RationalInterval := ⟨(-708319118717921831276106527469 / 1000000000000000000000000000000 : ℚ), (-44269944086170032074719946397 / 62500000000000000000000000000 : ℚ)⟩
theorem b898 (b : ℝ) (hb : rootInterval.Contains b) : i898.Contains (n898 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b886 b hb) (b894 b hb))
    (by norm_num [i898, i886, i894, RationalInterval.add]) (by norm_num [i898, i886, i894, RationalInterval.add])

def n899 (b : ℝ) : ℝ := (n887 b) + (n895 b)
def i899 : RationalInterval := ⟨(-2167261327095945732729474571433 / 1000000000000000000000000000000 : ℚ), (-108363066028486004230353173951 / 50000000000000000000000000000 : ℚ)⟩
theorem b899 (b : ℝ) (hb : rootInterval.Contains b) : i899.Contains (n899 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b887 b hb) (b895 b hb))
    (by norm_num [i899, i887, i895, RationalInterval.add]) (by norm_num [i899, i887, i895, RationalInterval.add])

