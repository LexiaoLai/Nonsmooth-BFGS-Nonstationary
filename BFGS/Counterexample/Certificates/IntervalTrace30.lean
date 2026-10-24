import BFGS.Counterexample.Certificates.IntervalTrace29

/-! Generated arithmetic proofs. Each bound is checked by the Lean kernel. -/
namespace BFGS.Counterexample.Trace
noncomputable section
open BFGS RationalInterval
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false

def n2700 (b : ℝ) : ℝ := (n2698 b) + (n2699 b)
def i2700 : RationalInterval := ⟨(-105115467045081833713979076702223 / 1000000000000000000000000000000 : ℚ), (-105115352875903748756347683836357 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2700 (b : ℝ) (hb : rootInterval.Contains b) : i2700.Contains (n2700 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2698 b hb) (b2699 b hb))
    (by norm_num [i2700, i2698, i2699, RationalInterval.add]) (by norm_num [i2700, i2698, i2699, RationalInterval.add])

def n2701 (b : ℝ) : ℝ := (n331 b) * (n2118 b)
def i2701 : RationalInterval := ⟨(54634118135318878194619617514551 / 1000000000000000000000000000000 : ℚ), (54634157517810826615642984726103 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2701 (b : ℝ) (hb : rootInterval.Contains b) : i2701.Contains (n2701 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b331 b hb) (b2118 b hb))
    (by norm_num [i2701, i331, i2118, RationalInterval.mul]) (by norm_num [i2701, i331, i2118, RationalInterval.mul])

def n2702 (b : ℝ) : ℝ := (n2700 b) + (n2701 b)
def i2702 : RationalInterval := ⟨(-6310168613720369439919932398459 / 125000000000000000000000000000 : ℚ), (-25240597679046461070352349555127 / 500000000000000000000000000000 : ℚ)⟩
theorem b2702 (b : ℝ) (hb : rootInterval.Contains b) : i2702.Contains (n2702 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2700 b hb) (b2701 b hb))
    (by norm_num [i2702, i2700, i2701, RationalInterval.add]) (by norm_num [i2702, i2700, i2701, RationalInterval.add])

def n2703 (b : ℝ) : ℝ := (n2190 b) * (n2004 b)
def i2703 : RationalInterval := ⟨(-856015719525722951830602796787 / 250000000000000000000000000000 : ℚ), (-856015410920866149426386335699 / 250000000000000000000000000000 : ℚ)⟩
theorem b2703 (b : ℝ) (hb : rootInterval.Contains b) : i2703.Contains (n2703 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2190 b hb) (b2004 b hb))
    (by norm_num [i2703, i2190, i2004, RationalInterval.mul]) (by norm_num [i2703, i2190, i2004, RationalInterval.mul])

def n2704 (b : ℝ) : ℝ := (n2333 b) * (n2039 b)
def i2704 : RationalInterval := ⟨(254535480742694409066461173939 / 500000000000000000000000000000 : ℚ), (509071128465121914209765690279 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2704 (b : ℝ) (hb : rootInterval.Contains b) : i2704.Contains (n2704 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2333 b hb) (b2039 b hb))
    (by norm_num [i2704, i2333, i2039, RationalInterval.mul]) (by norm_num [i2704, i2333, i2039, RationalInterval.mul])

def n2705 (b : ℝ) : ℝ := (n2703 b) + (n2704 b)
def i2705 : RationalInterval := ⟨(-291499191661750298918948883927 / 100000000000000000000000000000 : ℚ), (-2914990515218342683495779652517 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2705 (b : ℝ) (hb : rootInterval.Contains b) : i2705.Contains (n2705 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2703 b hb) (b2704 b hb))
    (by norm_num [i2705, i2703, i2704, RationalInterval.add]) (by norm_num [i2705, i2703, i2704, RationalInterval.add])

def n2706 (b : ℝ) : ℝ := (n330 b) * (n2082 b)
def i2706 : RationalInterval := ⟨(13982869441450882399742717211537 / 250000000000000000000000000000 : ℚ), (55931538388186840825603804375319 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2706 (b : ℝ) (hb : rootInterval.Contains b) : i2706.Contains (n2706 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b330 b hb) (b2082 b hb))
    (by norm_num [i2706, i330, i2082, RationalInterval.mul]) (by norm_num [i2706, i330, i2082, RationalInterval.mul])

def n2707 (b : ℝ) : ℝ := (n2705 b) + (n2706 b)
def i2707 : RationalInterval := ⟨(26508242924593013304890690003439 / 500000000000000000000000000000 : ℚ), (26508273936484249071054012361401 / 500000000000000000000000000000 : ℚ)⟩
theorem b2707 (b : ℝ) (hb : rootInterval.Contains b) : i2707.Contains (n2707 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2705 b hb) (b2706 b hb))
    (by norm_num [i2707, i2705, i2706, RationalInterval.add]) (by norm_num [i2707, i2705, i2706, RationalInterval.add])

def n2708 (b : ℝ) : ℝ := (n331 b) * (n2127 b)
def i2708 : RationalInterval := ⟨(-1460518874529738706601525536287 / 50000000000000000000000000000 : ℚ), (-5842071244922048270356488709947 / 200000000000000000000000000000 : ℚ)⟩
theorem b2708 (b : ℝ) (hb : rootInterval.Contains b) : i2708.Contains (n2708 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b331 b hb) (b2127 b hb))
    (by norm_num [i2708, i331, i2127, RationalInterval.mul]) (by norm_num [i2708, i331, i2127, RationalInterval.mul])

def n2709 (b : ℝ) : ℝ := (n2707 b) + (n2708 b)
def i2709 : RationalInterval := ⟨(11903054179295626238875434640569 / 500000000000000000000000000000 : ℚ), (23806191648358256790325581173067 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2709 (b : ℝ) (hb : rootInterval.Contains b) : i2709.Contains (n2709 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2707 b hb) (b2708 b hb))
    (by norm_num [i2709, i2707, i2708, RationalInterval.add]) (by norm_num [i2709, i2707, i2708, RationalInterval.add])

def n2710 (b : ℝ) : ℝ := (n2190 b) * (n2011 b)
def i2710 : RationalInterval := ⟨(-2257305702569139567312425076341 / 500000000000000000000000000000 : ℚ), (-902921980026509082298664264537 / 200000000000000000000000000000 : ℚ)⟩
theorem b2710 (b : ℝ) (hb : rootInterval.Contains b) : i2710.Contains (n2710 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2190 b hb) (b2011 b hb))
    (by norm_num [i2710, i2190, i2011, RationalInterval.mul]) (by norm_num [i2710, i2190, i2011, RationalInterval.mul])

def n2711 (b : ℝ) : ℝ := (n2333 b) * (n2046 b)
def i2711 : RationalInterval := ⟨(188405174916509513879760726893 / 250000000000000000000000000000 : ℚ), (753620904546263251558756907167 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2711 (b : ℝ) (hb : rootInterval.Contains b) : i2711.Contains (n2711 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2333 b hb) (b2046 b hb))
    (by norm_num [i2711, i2333, i2046, RationalInterval.mul]) (by norm_num [i2711, i2333, i2046, RationalInterval.mul])

def n2712 (b : ℝ) : ℝ := (n2710 b) + (n2711 b)
def i2712 : RationalInterval := ⟨(-376099070547224107910580724511 / 100000000000000000000000000000 : ℚ), (-1880494497793141079967282207759 / 500000000000000000000000000000 : ℚ)⟩
theorem b2712 (b : ℝ) (hb : rootInterval.Contains b) : i2712.Contains (n2712 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2710 b hb) (b2711 b hb))
    (by norm_num [i2712, i2710, i2711, RationalInterval.add]) (by norm_num [i2712, i2710, i2711, RationalInterval.add])

def n2713 (b : ℝ) : ℝ := (n330 b) * (n2091 b)
def i2713 : RationalInterval := ⟨(83630017949166271593507739428643 / 1000000000000000000000000000000 : ℚ), (16726019447572715534150323005797 / 200000000000000000000000000000 : ℚ)⟩
theorem b2713 (b : ℝ) (hb : rootInterval.Contains b) : i2713.Contains (n2713 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b330 b hb) (b2091 b hb))
    (by norm_num [i2713, i330, i2091, RationalInterval.mul]) (by norm_num [i2713, i330, i2091, RationalInterval.mul])

def n2714 (b : ℝ) : ℝ := (n2712 b) + (n2713 b)
def i2714 : RationalInterval := ⟨(79869027243694030514401932183533 / 1000000000000000000000000000000 : ℚ), (79869108242277295510817050613467 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2714 (b : ℝ) (hb : rootInterval.Contains b) : i2714.Contains (n2714 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2712 b hb) (b2713 b hb))
    (by norm_num [i2714, i2712, i2713, RationalInterval.add]) (by norm_num [i2714, i2712, i2713, RationalInterval.add])

def n2715 (b : ℝ) : ℝ := (n331 b) * (n2136 b)
def i2715 : RationalInterval := ⟨(-20108681890286570862272115136149 / 500000000000000000000000000000 : ℚ), (-628395858067614392916742462477 / 15625000000000000000000000000 : ℚ)⟩
theorem b2715 (b : ℝ) (hb : rootInterval.Contains b) : i2715.Contains (n2715 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b331 b hb) (b2136 b hb))
    (by norm_num [i2715, i331, i2136, RationalInterval.mul]) (by norm_num [i2715, i331, i2136, RationalInterval.mul])

def n2716 (b : ℝ) : ℝ := (n2714 b) + (n2715 b)
def i2716 : RationalInterval := ⟨(7930332692624177757971540382247 / 200000000000000000000000000000 : ℚ), (39651773325949974364145533014939 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2716 (b : ℝ) (hb : rootInterval.Contains b) : i2716.Contains (n2716 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2714 b hb) (b2715 b hb))
    (by norm_num [i2716, i2714, i2715, RationalInterval.add]) (by norm_num [i2716, i2714, i2715, RationalInterval.add])

def n2717 (b : ℝ) : ℝ := (n2189 b) * (n1983 b)
def i2717 : RationalInterval := ⟨(112447366469417472968737873249 / 500000000000000000000000000000 : ℚ), (56223758447405000828370090751 / 250000000000000000000000000000 : ℚ)⟩
theorem b2717 (b : ℝ) (hb : rootInterval.Contains b) : i2717.Contains (n2717 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2189 b hb) (b1983 b hb))
    (by norm_num [i2717, i2189, i1983, RationalInterval.mul]) (by norm_num [i2717, i2189, i1983, RationalInterval.mul])

def n2718 (b : ℝ) : ℝ := (n2335 b) * (n2018 b)
def i2718 : RationalInterval := ⟨(-61034774385860958722992200711 / 62500000000000000000000000000 : ℚ), (-976555542820031318214405128909 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2718 (b : ℝ) (hb : rootInterval.Contains b) : i2718.Contains (n2718 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2335 b hb) (b2018 b hb))
    (by norm_num [i2718, i2335, i2018, RationalInterval.mul]) (by norm_num [i2718, i2335, i2018, RationalInterval.mul])

def n2719 (b : ℝ) : ℝ := (n2717 b) + (n2718 b)
def i2719 : RationalInterval := ⟨(-375830828617470196815199732439 / 500000000000000000000000000000 : ℚ), (-150332101806082262980184953181 / 200000000000000000000000000000 : ℚ)⟩
theorem b2719 (b : ℝ) (hb : rootInterval.Contains b) : i2719.Contains (n2719 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2717 b hb) (b2718 b hb))
    (by norm_num [i2719, i2717, i2718, RationalInterval.add]) (by norm_num [i2719, i2717, i2718, RationalInterval.add])

def n2720 (b : ℝ) : ℝ := (n330 b) * (n2100 b)
def i2720 : RationalInterval := ⟨(5407598043714257016581589362781 / 1000000000000000000000000000000 : ℚ), (2703801717242925491923786195473 / 500000000000000000000000000000 : ℚ)⟩
theorem b2720 (b : ℝ) (hb : rootInterval.Contains b) : i2720.Contains (n2720 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b330 b hb) (b2100 b hb))
    (by norm_num [i2720, i330, i2100, RationalInterval.mul]) (by norm_num [i2720, i330, i2100, RationalInterval.mul])

def n2721 (b : ℝ) : ℝ := (n2719 b) + (n2720 b)
def i2721 : RationalInterval := ⟨(4655936386479316622951189897903 / 1000000000000000000000000000000 : ℚ), (4655942925455439668946647625041 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2721 (b : ℝ) (hb : rootInterval.Contains b) : i2721.Contains (n2721 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2719 b hb) (b2720 b hb))
    (by norm_num [i2721, i2719, i2720, RationalInterval.add]) (by norm_num [i2721, i2719, i2720, RationalInterval.add])

def n2722 (b : ℝ) : ℝ := (n331 b) * (n2145 b)
def i2722 : RationalInterval := ⟨(-1253031502193945478664089118199 / 500000000000000000000000000000 : ℚ), (-626515017632420351757789367793 / 250000000000000000000000000000 : ℚ)⟩
theorem b2722 (b : ℝ) (hb : rootInterval.Contains b) : i2722.Contains (n2722 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b331 b hb) (b2145 b hb))
    (by norm_num [i2722, i331, i2145, RationalInterval.mul]) (by norm_num [i2722, i331, i2145, RationalInterval.mul])

def n2723 (b : ℝ) : ℝ := (n2721 b) + (n2722 b)
def i2723 : RationalInterval := ⟨(429974676418285133124602332301 / 200000000000000000000000000000 : ℚ), (2149882854925758261915490153869 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2723 (b : ℝ) (hb : rootInterval.Contains b) : i2723.Contains (n2723 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2721 b hb) (b2722 b hb))
    (by norm_num [i2723, i2721, i2722, RationalInterval.add]) (by norm_num [i2723, i2721, i2722, RationalInterval.add])

def n2724 (b : ℝ) : ℝ := (n2189 b) * (n1990 b)
def i2724 : RationalInterval := ⟨(67777890112286452737692960283 / 125000000000000000000000000000 : ℚ), (108444788986797188496220057037 / 200000000000000000000000000000 : ℚ)⟩
theorem b2724 (b : ℝ) (hb : rootInterval.Contains b) : i2724.Contains (n2724 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2189 b hb) (b1990 b hb))
    (by norm_num [i2724, i2189, i1990, RationalInterval.mul]) (by norm_num [i2724, i2189, i1990, RationalInterval.mul])

def n2725 (b : ℝ) : ℝ := (n2335 b) * (n2025 b)
def i2725 : RationalInterval := ⟨(-40901933363213079376644600571 / 62500000000000000000000000000 : ℚ), (-654428694497472780921630803729 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2725 (b : ℝ) (hb : rootInterval.Contains b) : i2725.Contains (n2725 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2335 b hb) (b2025 b hb))
    (by norm_num [i2725, i2335, i2025, RationalInterval.mul]) (by norm_num [i2725, i2335, i2025, RationalInterval.mul])

def n2726 (b : ℝ) : ℝ := (n2724 b) + (n2725 b)
def i2726 : RationalInterval := ⟨(-14025976614139706015596240859 / 125000000000000000000000000000 : ℚ), (-7012796847717927402533157409 / 62500000000000000000000000000 : ℚ)⟩
theorem b2726 (b : ℝ) (hb : rootInterval.Contains b) : i2726.Contains (n2726 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2724 b hb) (b2725 b hb))
    (by norm_num [i2726, i2724, i2725, RationalInterval.add]) (by norm_num [i2726, i2724, i2725, RationalInterval.add])

def n2727 (b : ℝ) : ℝ := (n330 b) * (n2109 b)
def i2727 : RationalInterval := ⟨(6151100777045741057256264887307 / 500000000000000000000000000000 : ℚ), (12302214826644762534213271965989 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2727 (b : ℝ) (hb : rootInterval.Contains b) : i2727.Contains (n2727 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b330 b hb) (b2109 b hb))
    (by norm_num [i2727, i330, i2109, RationalInterval.mul]) (by norm_num [i2727, i330, i2109, RationalInterval.mul])

def n2728 (b : ℝ) : ℝ := (n2726 b) + (n2727 b)
def i2728 : RationalInterval := ⟨(6094996870589182233193879923871 / 500000000000000000000000000000 : ℚ), (2438002015416255139154548289489 / 200000000000000000000000000000 : ℚ)⟩
theorem b2728 (b : ℝ) (hb : rootInterval.Contains b) : i2728.Contains (n2728 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2726 b hb) (b2727 b hb))
    (by norm_num [i2728, i2726, i2727, RationalInterval.add]) (by norm_num [i2728, i2726, i2727, RationalInterval.add])

def n2729 (b : ℝ) : ℝ := (n331 b) * (n2154 b)
def i2729 : RationalInterval := ⟨(-6093334093947719279393613345493 / 1000000000000000000000000000000 : ℚ), (-6093326861406262523474868979773 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2729 (b : ℝ) (hb : rootInterval.Contains b) : i2729.Contains (n2729 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b331 b hb) (b2154 b hb))
    (by norm_num [i2729, i331, i2154, RationalInterval.mul]) (by norm_num [i2729, i331, i2154, RationalInterval.mul])

def n2730 (b : ℝ) : ℝ := (n2728 b) + (n2729 b)
def i2730 : RationalInterval := ⟨(6096659647230645186994146502249 / 1000000000000000000000000000000 : ℚ), (762085401959376646537234058459 / 125000000000000000000000000000 : ℚ)⟩
theorem b2730 (b : ℝ) (hb : rootInterval.Contains b) : i2730.Contains (n2730 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2728 b hb) (b2729 b hb))
    (by norm_num [i2730, i2728, i2729, RationalInterval.add]) (by norm_num [i2730, i2728, i2729, RationalInterval.add])

def n2731 (b : ℝ) : ℝ := (n2189 b) * (n1997 b)
def i2731 : RationalInterval := ⟨(-1279758157892603612172369434673 / 500000000000000000000000000000 : ℚ), (-2559515378907940557437782093759 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2731 (b : ℝ) (hb : rootInterval.Contains b) : i2731.Contains (n2731 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2189 b hb) (b1997 b hb))
    (by norm_num [i2731, i2189, i1997, RationalInterval.mul]) (by norm_num [i2731, i2189, i1997, RationalInterval.mul])

def n2732 (b : ℝ) : ℝ := (n2335 b) * (n2032 b)
def i2732 : RationalInterval := ⟨(1888658669479402710407988875817 / 250000000000000000000000000000 : ℚ), (7554637132198350027044340168741 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2732 (b : ℝ) (hb : rootInterval.Contains b) : i2732.Contains (n2732 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2335 b hb) (b2032 b hb))
    (by norm_num [i2732, i2335, i2032, RationalInterval.mul]) (by norm_num [i2732, i2335, i2032, RationalInterval.mul])

def n2733 (b : ℝ) : ℝ := (n2731 b) + (n2732 b)
def i2733 : RationalInterval := ⟨(2497559181066201808643608316961 / 500000000000000000000000000000 : ℚ), (2497560876645204734803279037491 / 500000000000000000000000000000 : ℚ)⟩
theorem b2733 (b : ℝ) (hb : rootInterval.Contains b) : i2733.Contains (n2733 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2731 b hb) (b2732 b hb))
    (by norm_num [i2733, i2731, i2732, RationalInterval.add]) (by norm_num [i2733, i2731, i2732, RationalInterval.add])

def n2734 (b : ℝ) : ℝ := (n330 b) * (n2118 b)
def i2734 : RationalInterval := ⟨(-28864489339403697385182776744461 / 500000000000000000000000000000 : ℚ), (-360805856683495453438772741867 / 6250000000000000000000000000 : ℚ)⟩
theorem b2734 (b : ℝ) (hb : rootInterval.Contains b) : i2734.Contains (n2734 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b330 b hb) (b2118 b hb))
    (by norm_num [i2734, i330, i2118, RationalInterval.mul]) (by norm_num [i2734, i330, i2118, RationalInterval.mul])

def n2735 (b : ℝ) : ℝ := (n2733 b) + (n2734 b)
def i2735 : RationalInterval := ⟨(-10546772063334998230615667371 / 200000000000000000000000000 : ℚ), (-26366907658034431540298540311869 / 500000000000000000000000000000 : ℚ)⟩
theorem b2735 (b : ℝ) (hb : rootInterval.Contains b) : i2735.Contains (n2735 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2733 b hb) (b2734 b hb))
    (by norm_num [i2735, i2733, i2734, RationalInterval.add]) (by norm_num [i2735, i2733, i2734, RationalInterval.add])

def n2736 (b : ℝ) : ℝ := (n331 b) * (n2163 b)
def i2736 : RationalInterval := ⟨(7091700122959692706851304197887 / 250000000000000000000000000000 : ℚ), (3545853003734869356778275170733 / 125000000000000000000000000000 : ℚ)⟩
theorem b2736 (b : ℝ) (hb : rootInterval.Contains b) : i2736.Contains (n2736 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b331 b hb) (b2163 b hb))
    (by norm_num [i2736, i331, i2163, RationalInterval.mul]) (by norm_num [i2736, i331, i2163, RationalInterval.mul])

def n2737 (b : ℝ) : ℝ := (n2735 b) + (n2736 b)
def i2737 : RationalInterval := ⟨(-6091764956209055081418280015863 / 250000000000000000000000000000 : ℚ), (-12183495643094954113185439628937 / 500000000000000000000000000000 : ℚ)⟩
theorem b2737 (b : ℝ) (hb : rootInterval.Contains b) : i2737.Contains (n2737 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2735 b hb) (b2736 b hb))
    (by norm_num [i2737, i2735, i2736, RationalInterval.add]) (by norm_num [i2737, i2735, i2736, RationalInterval.add])

def n2738 (b : ℝ) : ℝ := (n2189 b) * (n2004 b)
def i2738 : RationalInterval := ⟨(709466007016011951635936409941 / 500000000000000000000000000000 : ℚ), (283786505667633410459809516893 / 200000000000000000000000000000 : ℚ)⟩
theorem b2738 (b : ℝ) (hb : rootInterval.Contains b) : i2738.Contains (n2738 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2189 b hb) (b2004 b hb))
    (by norm_num [i2738, i2189, i2004, RationalInterval.mul]) (by norm_num [i2738, i2189, i2004, RationalInterval.mul])

def n2739 (b : ℝ) : ℝ := (n2335 b) * (n2039 b)
def i2739 : RationalInterval := ⟨(-4249775037264563960988644518501 / 1000000000000000000000000000000 : ℚ), (-1062443422903226237236000320107 / 250000000000000000000000000000 : ℚ)⟩
theorem b2739 (b : ℝ) (hb : rootInterval.Contains b) : i2739.Contains (n2739 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2335 b hb) (b2039 b hb))
    (by norm_num [i2739, i2335, i2039, RationalInterval.mul]) (by norm_num [i2739, i2335, i2039, RationalInterval.mul])

def n2740 (b : ℝ) : ℝ := (n2738 b) + (n2739 b)
def i2740 : RationalInterval := ⟨(-2830843023232540057716771698619 / 1000000000000000000000000000000 : ℚ), (-2830841163274737896644953695963 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2740 (b : ℝ) (hb : rootInterval.Contains b) : i2740.Contains (n2740 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2738 b hb) (b2739 b hb))
    (by norm_num [i2740, i2738, i2739, RationalInterval.add]) (by norm_num [i2740, i2738, i2739, RationalInterval.add])

def n2741 (b : ℝ) : ℝ := (n330 b) * (n2127 b)
def i2741 : RationalInterval := ⟨(6173002782208262146081258037781 / 200000000000000000000000000000 : ℚ), (6173007275914264280511573113467 / 200000000000000000000000000000 : ℚ)⟩
theorem b2741 (b : ℝ) (hb : rootInterval.Contains b) : i2741.Contains (n2741 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b330 b hb) (b2127 b hb))
    (by norm_num [i2741, i330, i2127, RationalInterval.mul]) (by norm_num [i2741, i330, i2127, RationalInterval.mul])

def n2742 (b : ℝ) : ℝ := (n2740 b) + (n2741 b)
def i2742 : RationalInterval := ⟨(14017085443904385336344759245143 / 500000000000000000000000000000 : ℚ), (7008548804074145876478227967843 / 250000000000000000000000000000 : ℚ)⟩
theorem b2742 (b : ℝ) (hb : rootInterval.Contains b) : i2742.Contains (n2742 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2740 b hb) (b2741 b hb))
    (by norm_num [i2742, i2740, i2741, RationalInterval.add]) (by norm_num [i2742, i2740, i2741, RationalInterval.add])

def n2743 (b : ℝ) : ℝ := (n331 b) * (n2172 b)
def i2743 : RationalInterval := ⟨(-1923886682898794873349909924231 / 125000000000000000000000000000 : ℚ), (-1923885095012395548474462679533 / 125000000000000000000000000000 : ℚ)⟩
theorem b2743 (b : ℝ) (hb : rootInterval.Contains b) : i2743.Contains (n2743 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b331 b hb) (b2172 b hb))
    (by norm_num [i2743, i331, i2172, RationalInterval.mul]) (by norm_num [i2743, i331, i2172, RationalInterval.mul])

def n2744 (b : ℝ) : ℝ := (n2742 b) + (n2743 b)
def i2744 : RationalInterval := ⟨(6321538712309205842945119548219 / 500000000000000000000000000000 : ℚ), (3160778614049354779529302608777 / 250000000000000000000000000000 : ℚ)⟩
theorem b2744 (b : ℝ) (hb : rootInterval.Contains b) : i2744.Contains (n2744 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2742 b hb) (b2743 b hb))
    (by norm_num [i2744, i2742, i2743, RationalInterval.add]) (by norm_num [i2744, i2742, i2743, RationalInterval.add])

def n2745 (b : ℝ) : ℝ := (n2189 b) * (n2011 b)
def i2745 : RationalInterval := ⟨(1870855488241957291419084496347 / 1000000000000000000000000000000 : ℚ), (467714028889738138903718294751 / 250000000000000000000000000000 : ℚ)⟩
theorem b2745 (b : ℝ) (hb : rootInterval.Contains b) : i2745.Contains (n2745 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2189 b hb) (b2011 b hb))
    (by norm_num [i2745, i2189, i2011, RationalInterval.mul]) (by norm_num [i2745, i2189, i2011, RationalInterval.mul])

def n2746 (b : ℝ) : ℝ := (n2335 b) * (n2046 b)
def i2746 : RationalInterval := ⟨(-6291300230201286732088838875463 / 1000000000000000000000000000000 : ℚ), (-314564929568032548140151713821 / 50000000000000000000000000000 : ℚ)⟩
theorem b2746 (b : ℝ) (hb : rootInterval.Contains b) : i2746.Contains (n2746 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2335 b hb) (b2046 b hb))
    (by norm_num [i2746, i2335, i2046, RationalInterval.mul]) (by norm_num [i2746, i2335, i2046, RationalInterval.mul])

def n2747 (b : ℝ) : ℝ := (n2745 b) + (n2746 b)
def i2747 : RationalInterval := ⟨(-1105111185489832360167438594779 / 250000000000000000000000000000 : ℚ), (-552555309475212300898520137177 / 125000000000000000000000000000 : ℚ)⟩
theorem b2747 (b : ℝ) (hb : rootInterval.Contains b) : i2747.Contains (n2747 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2745 b hb) (b2746 b hb))
    (by norm_num [i2747, i2745, i2746, RationalInterval.add]) (by norm_num [i2747, i2745, i2746, RationalInterval.add])

def n2748 (b : ℝ) : ℝ := (n330 b) * (n2136 b)
def i2748 : RationalInterval := ⟨(42495496874893492782765973389813 / 1000000000000000000000000000000 : ℚ), (10623881842827297137689508347741 / 250000000000000000000000000000 : ℚ)⟩
theorem b2748 (b : ℝ) (hb : rootInterval.Contains b) : i2748.Contains (n2748 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b330 b hb) (b2136 b hb))
    (by norm_num [i2748, i330, i2136, RationalInterval.mul]) (by norm_num [i2748, i330, i2136, RationalInterval.mul])

def n2749 (b : ℝ) : ℝ := (n2747 b) + (n2748 b)
def i2749 : RationalInterval := ⟨(38075052132934163342096219010697 / 1000000000000000000000000000000 : ℚ), (9518771223876872535892468073387 / 250000000000000000000000000000 : ℚ)⟩
theorem b2749 (b : ℝ) (hb : rootInterval.Contains b) : i2749.Contains (n2749 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2747 b hb) (b2748 b hb))
    (by norm_num [i2749, i2747, i2748, RationalInterval.add]) (by norm_num [i2749, i2747, i2748, RationalInterval.add])

def n2750 (b : ℝ) : ℝ := (n331 b) * (n2181 b)
def i2750 : RationalInterval := ⟨(-10522980035744120600031777653391 / 500000000000000000000000000000 : ℚ), (-21045942743119800838565848223587 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2750 (b : ℝ) (hb : rootInterval.Contains b) : i2750.Contains (n2750 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b331 b hb) (b2181 b hb))
    (by norm_num [i2750, i331, i2181, RationalInterval.mul]) (by norm_num [i2750, i331, i2181, RationalInterval.mul])

def n2751 (b : ℝ) : ℝ := (n2749 b) + (n2750 b)
def i2751 : RationalInterval := ⟨(3405818412289184428406532740783 / 200000000000000000000000000000 : ℚ), (17029142152387689305004024069961 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2751 (b : ℝ) (hb : rootInterval.Contains b) : i2751.Contains (n2751 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2749 b hb) (b2750 b hb))
    (by norm_num [i2751, i2749, i2750, RationalInterval.add]) (by norm_num [i2751, i2749, i2750, RationalInterval.add])

def n2752 (b : ℝ) : ℝ := (n2323 b) * (n1983 b)
def i2752 : RationalInterval := ⟨(60454222355274597517978201307 / 125000000000000000000000000000 : ℚ), (60454358855092056805185888077 / 125000000000000000000000000000 : ℚ)⟩
theorem b2752 (b : ℝ) (hb : rootInterval.Contains b) : i2752.Contains (n2752 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2323 b hb) (b1983 b hb))
    (by norm_num [i2752, i2323, i1983, RationalInterval.mul]) (by norm_num [i2752, i2323, i1983, RationalInterval.mul])

def n2753 (b : ℝ) : ℝ := (n2434 b) * (n2018 b)
def i2753 : RationalInterval := ⟨(-326925272314187559226181401133 / 1000000000000000000000000000000 : ℚ), (-326924387426173490535380749863 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2753 (b : ℝ) (hb : rootInterval.Contains b) : i2753.Contains (n2753 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2434 b hb) (b2018 b hb))
    (by norm_num [i2753, i2434, i2018, RationalInterval.mul]) (by norm_num [i2753, i2434, i2018, RationalInterval.mul])

def n2754 (b : ℝ) : ℝ := (n2752 b) + (n2753 b)
def i2754 : RationalInterval := ⟨(156708506528009220917644209323 / 1000000000000000000000000000000 : ℚ), (156710483414562963906106354753 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2754 (b : ℝ) (hb : rootInterval.Contains b) : i2754.Contains (n2754 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2752 b hb) (b2753 b hb))
    (by norm_num [i2754, i2752, i2753, RationalInterval.add]) (by norm_num [i2754, i2752, i2753, RationalInterval.add])

def n2755 (b : ℝ) : ℝ := (n2514 b) * (n2055 b)
def i2755 : RationalInterval := ⟨(1081707290596868097226048977177 / 1000000000000000000000000000000 : ℚ), (540861624723248328107055098937 / 500000000000000000000000000000 : ℚ)⟩
theorem b2755 (b : ℝ) (hb : rootInterval.Contains b) : i2755.Contains (n2755 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2514 b hb) (b2055 b hb))
    (by norm_num [i2755, i2514, i2055, RationalInterval.mul]) (by norm_num [i2755, i2514, i2055, RationalInterval.mul])

def n2756 (b : ℝ) : ℝ := (n2754 b) + (n2755 b)
def i2756 : RationalInterval := ⟨(2476831594249754636287386373 / 2000000000000000000000000000 : ℚ), (1238433732861059620120216552627 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2756 (b : ℝ) (hb : rootInterval.Contains b) : i2756.Contains (n2756 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2754 b hb) (b2755 b hb))
    (by norm_num [i2756, i2754, i2755, RationalInterval.add]) (by norm_num [i2756, i2754, i2755, RationalInterval.add])

def n2757 (b : ℝ) : ℝ := (n2608 b) * (n2100 b)
def i2757 : RationalInterval := ⟨(343660619162110183453270296643 / 200000000000000000000000000000 : ℚ), (1718314509810146553705656713283 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2757 (b : ℝ) (hb : rootInterval.Contains b) : i2757.Contains (n2757 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2608 b hb) (b2100 b hb))
    (by norm_num [i2757, i2608, i2100, RationalInterval.mul]) (by norm_num [i2757, i2608, i2100, RationalInterval.mul])

def n2758 (b : ℝ) : ℝ := (n2756 b) + (n2757 b)
def i2758 : RationalInterval := ⟨(591343778587085647082008933943 / 200000000000000000000000000000 : ℚ), (295674824267120617382587326591 / 100000000000000000000000000000 : ℚ)⟩
theorem b2758 (b : ℝ) (hb : rootInterval.Contains b) : i2758.Contains (n2758 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2756 b hb) (b2757 b hb))
    (by norm_num [i2758, i2756, i2757, RationalInterval.add]) (by norm_num [i2758, i2756, i2757, RationalInterval.add])

def n2759 (b : ℝ) : ℝ := (n2672 b) * (n2145 b)
def i2759 : RationalInterval := ⟨(-346602157503025900673942329911 / 500000000000000000000000000000 : ℚ), (-86650241102603168897259518389 / 125000000000000000000000000000 : ℚ)⟩
theorem b2759 (b : ℝ) (hb : rootInterval.Contains b) : i2759.Contains (n2759 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2672 b hb) (b2145 b hb))
    (by norm_num [i2759, i2672, i2145, RationalInterval.mul]) (by norm_num [i2759, i2672, i2145, RationalInterval.mul])

def n2760 (b : ℝ) : ℝ := (n2758 b) + (n2759 b)
def i2760 : RationalInterval := ⟨(2263514577929376434062160009893 / 1000000000000000000000000000000 : ℚ), (1131773156925190411323898559399 / 500000000000000000000000000000 : ℚ)⟩
theorem b2760 (b : ℝ) (hb : rootInterval.Contains b) : i2760.Contains (n2760 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2758 b hb) (b2759 b hb))
    (by norm_num [i2760, i2758, i2759, RationalInterval.add]) (by norm_num [i2760, i2758, i2759, RationalInterval.add])

def n2761 (b : ℝ) : ℝ := (n2323 b) * (n1990 b)
def i2761 : RationalInterval := ⟨(145755646157668859903493364781 / 125000000000000000000000000000 : ℚ), (1166048014293708522857748384559 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2761 (b : ℝ) (hb : rootInterval.Contains b) : i2761.Contains (n2761 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2323 b hb) (b1990 b hb))
    (by norm_num [i2761, i2323, i1990, RationalInterval.mul]) (by norm_num [i2761, i2323, i1990, RationalInterval.mul])

def n2762 (b : ℝ) : ℝ := (n2434 b) * (n2025 b)
def i2762 : RationalInterval := ⟨(-109543091110719809212876749227 / 500000000000000000000000000000 : ℚ), (-54771257414829185752528909459 / 250000000000000000000000000000 : ℚ)⟩
theorem b2762 (b : ℝ) (hb : rootInterval.Contains b) : i2762.Contains (n2762 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2434 b hb) (b2025 b hb))
    (by norm_num [i2762, i2434, i2025, RationalInterval.mul]) (by norm_num [i2762, i2434, i2025, RationalInterval.mul])

def n2763 (b : ℝ) : ℝ := (n2761 b) + (n2762 b)
def i2763 : RationalInterval := ⟨(473479493519955630401096709897 / 500000000000000000000000000000 : ℚ), (946962984634391779847632746723 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2763 (b : ℝ) (hb : rootInterval.Contains b) : i2763.Contains (n2763 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2761 b hb) (b2762 b hb))
    (by norm_num [i2763, i2761, i2762, RationalInterval.add]) (by norm_num [i2763, i2761, i2762, RationalInterval.add])

def n2764 (b : ℝ) : ℝ := (n2514 b) * (n2064 b)
def i2764 : RationalInterval := ⟨(2300571016956820451811253194471 / 1000000000000000000000000000000 : ℚ), (2300606335833201864718365831541 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2764 (b : ℝ) (hb : rootInterval.Contains b) : i2764.Contains (n2764 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2514 b hb) (b2064 b hb))
    (by norm_num [i2764, i2514, i2064, RationalInterval.mul]) (by norm_num [i2764, i2514, i2064, RationalInterval.mul])

def n2765 (b : ℝ) : ℝ := (n2763 b) + (n2764 b)
def i2765 : RationalInterval := ⟨(649506000799346342522689322853 / 200000000000000000000000000000 : ℚ), (405946165058449205570749822283 / 125000000000000000000000000000 : ℚ)⟩
theorem b2765 (b : ℝ) (hb : rootInterval.Contains b) : i2765.Contains (n2765 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2763 b hb) (b2764 b hb))
    (by norm_num [i2765, i2763, i2764, RationalInterval.add]) (by norm_num [i2765, i2763, i2764, RationalInterval.add])

def n2766 (b : ℝ) : ℝ := (n2608 b) * (n2109 b)
def i2766 : RationalInterval := ⟨(3909112852840910220888900447131 / 1000000000000000000000000000000 : ℚ), (3909139140014451196344529758169 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2766 (b : ℝ) (hb : rootInterval.Contains b) : i2766.Contains (n2766 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2608 b hb) (b2109 b hb))
    (by norm_num [i2766, i2608, i2109, RationalInterval.mul]) (by norm_num [i2766, i2608, i2109, RationalInterval.mul])

def n2767 (b : ℝ) : ℝ := (n2765 b) + (n2766 b)
def i2767 : RationalInterval := ⟨(1789160714209410483375586765349 / 250000000000000000000000000000 : ℚ), (7156708460482044840910528336433 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2767 (b : ℝ) (hb : rootInterval.Contains b) : i2767.Contains (n2767 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2765 b hb) (b2766 b hb))
    (by norm_num [i2767, i2765, i2766, RationalInterval.add]) (by norm_num [i2767, i2765, i2766, RationalInterval.add])

def n2768 (b : ℝ) : ℝ := (n2672 b) * (n2154 b)
def i2768 : RationalInterval := ⟨(-842741279708917205027036077753 / 500000000000000000000000000000 : ℚ), (-1685476730160662688126925088033 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2768 (b : ℝ) (hb : rootInterval.Contains b) : i2768.Contains (n2768 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2672 b hb) (b2154 b hb))
    (by norm_num [i2768, i2672, i2154, RationalInterval.mul]) (by norm_num [i2768, i2672, i2154, RationalInterval.mul])

def n2769 (b : ℝ) : ℝ := (n2767 b) + (n2768 b)
def i2769 : RationalInterval := ⟨(547116029741980752344827490589 / 100000000000000000000000000000 : ℚ), (13678079325803455381959008121 / 2500000000000000000000000000 : ℚ)⟩
theorem b2769 (b : ℝ) (hb : rootInterval.Contains b) : i2769.Contains (n2769 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2767 b hb) (b2768 b hb))
    (by norm_num [i2769, i2767, i2768, RationalInterval.add]) (by norm_num [i2769, i2767, i2768, RationalInterval.add])

def n2770 (b : ℝ) : ℝ := (n2323 b) * (n1997 b)
def i2770 : RationalInterval := ⟨(-1100843644202044699115439999603 / 200000000000000000000000000000 : ℚ), (-1100842228299432685139099459669 / 200000000000000000000000000000 : ℚ)⟩
theorem b2770 (b : ℝ) (hb : rootInterval.Contains b) : i2770.Contains (n2770 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2323 b hb) (b1997 b hb))
    (by norm_num [i2770, i2323, i1997, RationalInterval.mul]) (by norm_num [i2770, i2323, i1997, RationalInterval.mul])

def n2771 (b : ℝ) : ℝ := (n2434 b) * (n2032 b)
def i2771 : RationalInterval := ⟨(505817479090771781322684218557 / 200000000000000000000000000000 : ℚ), (2529092868092670583002443223099 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2771 (b : ℝ) (hb : rootInterval.Contains b) : i2771.Contains (n2771 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2434 b hb) (b2032 b hb))
    (by norm_num [i2771, i2434, i2032, RationalInterval.mul]) (by norm_num [i2771, i2434, i2032, RationalInterval.mul])

def n2772 (b : ℝ) : ℝ := (n2770 b) + (n2771 b)
def i2772 : RationalInterval := ⟨(-297513082555636458896377890523 / 100000000000000000000000000000 : ℚ), (-1487559136702246421346527037623 / 500000000000000000000000000000 : ℚ)⟩
theorem b2772 (b : ℝ) (hb : rootInterval.Contains b) : i2772.Contains (n2772 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2770 b hb) (b2771 b hb))
    (by norm_num [i2772, i2770, i2771, RationalInterval.add]) (by norm_num [i2772, i2770, i2771, RationalInterval.add])

def n2773 (b : ℝ) : ℝ := (n2514 b) * (n2073 b)
def i2773 : RationalInterval := ⟨(-5410070232892628298655416927381 / 500000000000000000000000000000 : ℚ), (-1352498886568725038467075502573 / 125000000000000000000000000000 : ℚ)⟩
theorem b2773 (b : ℝ) (hb : rootInterval.Contains b) : i2773.Contains (n2773 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2514 b hb) (b2073 b hb))
    (by norm_num [i2773, i2514, i2073, RationalInterval.mul]) (by norm_num [i2773, i2514, i2073, RationalInterval.mul])

def n2774 (b : ℝ) : ℝ := (n2772 b) + (n2773 b)
def i2774 : RationalInterval := ⟨(-1724408911417702648284326594999 / 125000000000000000000000000000 : ℚ), (-1379510936595429315042965809583 / 100000000000000000000000000000 : ℚ)⟩
theorem b2774 (b : ℝ) (hb : rootInterval.Contains b) : i2774.Contains (n2774 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2772 b hb) (b2773 b hb))
    (by norm_num [i2774, i2772, i2773, RationalInterval.add]) (by norm_num [i2774, i2772, i2773, RationalInterval.add])

def n2775 (b : ℝ) : ℝ := (n2608 b) * (n2118 b)
def i2775 : RationalInterval := ⟨(-4585975233858232662467021213877 / 250000000000000000000000000000 : ℚ), (-18343784150051023687840328644649 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2775 (b : ℝ) (hb : rootInterval.Contains b) : i2775.Contains (n2775 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2608 b hb) (b2118 b hb))
    (by norm_num [i2775, i2608, i2118, RationalInterval.mul]) (by norm_num [i2775, i2608, i2118, RationalInterval.mul])

def n2776 (b : ℝ) : ℝ := (n2774 b) + (n2775 b)
def i2776 : RationalInterval := ⟨(-64278344453549103672285395231 / 2000000000000000000000000000 : ℚ), (-32138893516005316838269986740479 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2776 (b : ℝ) (hb : rootInterval.Contains b) : i2776.Contains (n2776 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2774 b hb) (b2775 b hb))
    (by norm_num [i2776, i2774, i2775, RationalInterval.add]) (by norm_num [i2776, i2774, i2775, RationalInterval.add])

def n2777 (b : ℝ) : ℝ := (n2672 b) * (n2163 b)
def i2777 : RationalInterval := ⟨(7846548072274262186763777882683 / 1000000000000000000000000000000 : ℚ), (1569314481407653894229714666383 / 200000000000000000000000000000 : ℚ)⟩
theorem b2777 (b : ℝ) (hb : rootInterval.Contains b) : i2777.Contains (n2777 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2672 b hb) (b2163 b hb))
    (by norm_num [i2777, i2672, i2163, RationalInterval.mul]) (by norm_num [i2777, i2672, i2163, RationalInterval.mul])

def n2778 (b : ℝ) : ℝ := (n2776 b) + (n2777 b)
def i2778 : RationalInterval := ⟨(-24292624154500289649378919732817 / 1000000000000000000000000000000 : ℚ), (-6073080277241761841780353352141 / 250000000000000000000000000000 : ℚ)⟩
theorem b2778 (b : ℝ) (hb : rootInterval.Contains b) : i2778.Contains (n2778 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2776 b hb) (b2777 b hb))
    (by norm_num [i2778, i2776, i2777, RationalInterval.add]) (by norm_num [i2778, i2776, i2777, RationalInterval.add])

def n2779 (b : ℝ) : ℝ := (n2323 b) * (n2004 b)
def i2779 : RationalInterval := ⟨(381424813121966078519495968053 / 125000000000000000000000000000 : ℚ), (1525701209383981044448719227121 / 500000000000000000000000000000 : ℚ)⟩
theorem b2779 (b : ℝ) (hb : rootInterval.Contains b) : i2779.Contains (n2779 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2323 b hb) (b2004 b hb))
    (by norm_num [i2779, i2323, i2004, RationalInterval.mul]) (by norm_num [i2779, i2323, i2004, RationalInterval.mul])

def n2780 (b : ℝ) : ℝ := (n2434 b) * (n2039 b)
def i2780 : RationalInterval := ⟨(-1422712375149705209575311026683 / 1000000000000000000000000000000 : ℚ), (-355677327072030146328193781543 / 250000000000000000000000000000 : ℚ)⟩
theorem b2780 (b : ℝ) (hb : rootInterval.Contains b) : i2780.Contains (n2780 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2434 b hb) (b2039 b hb))
    (by norm_num [i2780, i2434, i2039, RationalInterval.mul]) (by norm_num [i2780, i2434, i2039, RationalInterval.mul])

def n2781 (b : ℝ) : ℝ := (n2779 b) + (n2780 b)
def i2781 : RationalInterval := ⟨(1628686129826023418580656717741 / 1000000000000000000000000000000 : ℚ), (162869311047984150358466332807 / 100000000000000000000000000000 : ℚ)⟩
theorem b2781 (b : ℝ) (hb : rootInterval.Contains b) : i2781.Contains (n2781 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2779 b hb) (b2780 b hb))
    (by norm_num [i2781, i2779, i2780, RationalInterval.add]) (by norm_num [i2781, i2779, i2780, RationalInterval.add])

def n2782 (b : ℝ) : ℝ := (n2514 b) * (n2082 b)
def i2782 : RationalInterval := ⟨(5482339360895042161822291098059 / 1000000000000000000000000000000 : ℚ), (219296617799642284285569259887 / 40000000000000000000000000000 : ℚ)⟩
theorem b2782 (b : ℝ) (hb : rootInterval.Contains b) : i2782.Contains (n2782 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2514 b hb) (b2082 b hb))
    (by norm_num [i2782, i2514, i2082, RationalInterval.mul]) (by norm_num [i2782, i2514, i2082, RationalInterval.mul])

def n2783 (b : ℝ) : ℝ := (n2781 b) + (n2782 b)
def i2783 : RationalInterval := ⟨(35555127453605327902014739079 / 5000000000000000000000000000 : ℚ), (1422221711094179722144778965049 / 200000000000000000000000000000 : ℚ)⟩
theorem b2783 (b : ℝ) (hb : rootInterval.Contains b) : i2783.Contains (n2783 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2781 b hb) (b2782 b hb))
    (by norm_num [i2783, i2781, i2782, RationalInterval.add]) (by norm_num [i2783, i2781, i2782, RationalInterval.add])

def n2784 (b : ℝ) : ℝ := (n2608 b) * (n2127 b)
def i2784 : RationalInterval := ⟨(122594746611265628607521837021 / 12500000000000000000000000000 : ℚ), (9807642239186872849391878283677 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2784 (b : ℝ) (hb : rootInterval.Contains b) : i2784.Contains (n2784 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2608 b hb) (b2127 b hb))
    (by norm_num [i2784, i2608, i2127, RationalInterval.mul]) (by norm_num [i2784, i2608, i2127, RationalInterval.mul])

def n2785 (b : ℝ) : ℝ := (n2783 b) + (n2784 b)
def i2785 : RationalInterval := ⟨(422965130490557896725117369437 / 25000000000000000000000000000 : ℚ), (8459375397328885730057886554461 / 500000000000000000000000000000 : ℚ)⟩
theorem b2785 (b : ℝ) (hb : rootInterval.Contains b) : i2785.Contains (n2785 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2783 b hb) (b2784 b hb))
    (by norm_num [i2785, i2783, i2784, RationalInterval.add]) (by norm_num [i2785, i2783, i2784, RationalInterval.add])

def n2786 (b : ℝ) : ℝ := (n2672 b) * (n2172 b)
def i2786 : RationalInterval := ⟨(-1064336010573580246266354683 / 250000000000000000000000000 : ℚ), (-1064332714427193129474655867269 / 250000000000000000000000000000 : ℚ)⟩
theorem b2786 (b : ℝ) (hb : rootInterval.Contains b) : i2786.Contains (n2786 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2672 b hb) (b2172 b hb))
    (by norm_num [i2786, i2672, i2172, RationalInterval.mul]) (by norm_num [i2786, i2672, i2172, RationalInterval.mul])

def n2787 (b : ℝ) : ℝ := (n2785 b) + (n2786 b)
def i2787 : RationalInterval := ⟨(316531529433199872098481901137 / 25000000000000000000000000000 : ℚ), (6330709968474499471108574819923 / 500000000000000000000000000000 : ℚ)⟩
theorem b2787 (b : ℝ) (hb : rootInterval.Contains b) : i2787.Contains (n2787 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2785 b hb) (b2786 b hb))
    (by norm_num [i2787, i2785, i2786, RationalInterval.add]) (by norm_num [i2787, i2785, i2786, RationalInterval.add])

def n2788 (b : ℝ) : ℝ := (n2323 b) * (n2011 b)
def i2788 : RationalInterval := ⟨(4023255225333371745261321531639 / 1000000000000000000000000000000 : ℚ), (2011630138210098088600882044721 / 500000000000000000000000000000 : ℚ)⟩
theorem b2788 (b : ℝ) (hb : rootInterval.Contains b) : i2788.Contains (n2788 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2323 b hb) (b2011 b hb))
    (by norm_num [i2788, i2323, i2011, RationalInterval.mul]) (by norm_num [i2788, i2323, i2011, RationalInterval.mul])

def n2789 (b : ℝ) : ℝ := (n2434 b) * (n2046 b)
def i2789 : RationalInterval := ⟨(-526540264767216281821642300939 / 250000000000000000000000000000 : ℚ), (-2106156637190652069490140060439 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2789 (b : ℝ) (hb : rootInterval.Contains b) : i2789.Contains (n2789 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2434 b hb) (b2046 b hb))
    (by norm_num [i2789, i2434, i2046, RationalInterval.mul]) (by norm_num [i2789, i2434, i2046, RationalInterval.mul])

