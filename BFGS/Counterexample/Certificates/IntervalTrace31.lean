import BFGS.Counterexample.Certificates.IntervalTrace30

/-! Generated arithmetic proofs. Each bound is checked by the Lean kernel. -/
namespace BFGS.Counterexample.Trace
noncomputable section
open BFGS RationalInterval
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false

def n2790 (b : ℝ) : ℝ := (n2788 b) + (n2789 b)
def i2790 : RationalInterval := ⟨(1917094166264506617974752327883 / 1000000000000000000000000000000 : ℚ), (1917103639229544107711624029003 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2790 (b : ℝ) (hb : rootInterval.Contains b) : i2790.Contains (n2790 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2788 b hb) (b2789 b hb))
    (by norm_num [i2790, i2788, i2789, RationalInterval.add]) (by norm_num [i2790, i2788, i2789, RationalInterval.add])

def n2791 (b : ℝ) : ℝ := (n2514 b) * (n2091 b)
def i2791 : RationalInterval := ⟨(4098659265493182467929347422953 / 500000000000000000000000000000 : ℚ), (4098715590306423445196082812109 / 500000000000000000000000000000 : ℚ)⟩
theorem b2791 (b : ℝ) (hb : rootInterval.Contains b) : i2791.Contains (n2791 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2514 b hb) (b2091 b hb))
    (by norm_num [i2791, i2514, i2091, RationalInterval.mul]) (by norm_num [i2791, i2514, i2091, RationalInterval.mul])

def n2792 (b : ℝ) : ℝ := (n2790 b) + (n2791 b)
def i2792 : RationalInterval := ⟨(10114412697250871553833447173789 / 1000000000000000000000000000000 : ℚ), (10114534819842390998103789653221 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2792 (b : ℝ) (hb : rootInterval.Contains b) : i2792.Contains (n2792 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2790 b hb) (b2791 b hb))
    (by norm_num [i2792, i2790, i2791, RationalInterval.add]) (by norm_num [i2792, i2790, i2791, RationalInterval.add])

def n2793 (b : ℝ) : ℝ := (n2608 b) * (n2136 b)
def i2793 : RationalInterval := ⟨(2700649835577739887264200139331 / 200000000000000000000000000000 : ℚ), (6751667551884519849034949327401 / 500000000000000000000000000000 : ℚ)⟩
theorem b2793 (b : ℝ) (hb : rootInterval.Contains b) : i2793.Contains (n2793 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2608 b hb) (b2136 b hb))
    (by norm_num [i2793, i2608, i2136, RationalInterval.mul]) (by norm_num [i2793, i2608, i2136, RationalInterval.mul])

def n2794 (b : ℝ) : ℝ := (n2792 b) + (n2793 b)
def i2794 : RationalInterval := ⟨(5904415468784892747538611967611 / 250000000000000000000000000000 : ℚ), (23617869923611430696173688308023 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2794 (b : ℝ) (hb : rootInterval.Contains b) : i2794.Contains (n2794 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2792 b hb) (b2793 b hb))
    (by norm_num [i2794, i2792, i2793, RationalInterval.add]) (by norm_num [i2794, i2792, i2793, RationalInterval.add])

def n2795 (b : ℝ) : ℝ := (n2672 b) * (n2181 b)
def i2795 : RationalInterval := ⟨(-5821541720801285908119751800857 / 1000000000000000000000000000000 : ℚ), (-2910761851829781788280363099347 / 500000000000000000000000000000 : ℚ)⟩
theorem b2795 (b : ℝ) (hb : rootInterval.Contains b) : i2795.Contains (n2795 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2672 b hb) (b2181 b hb))
    (by norm_num [i2795, i2672, i2181, RationalInterval.mul]) (by norm_num [i2795, i2672, i2181, RationalInterval.mul])

def n2796 (b : ℝ) : ℝ := (n2794 b) + (n2795 b)
def i2796 : RationalInterval := ⟨(17796120154338285082034696069587 / 1000000000000000000000000000000 : ℚ), (17796346219951867119612962109329 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2796 (b : ℝ) (hb : rootInterval.Contains b) : i2796.Contains (n2796 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2794 b hb) (b2795 b hb))
    (by norm_num [i2796, i2794, i2795, RationalInterval.add]) (by norm_num [i2796, i2794, i2795, RationalInterval.add])

def n2797 (b : ℝ) : ℝ := (n2324 b) * (n1983 b)
def i2797 : RationalInterval := ⟨(196917928149350138226554873449 / 1000000000000000000000000000000 : ℚ), (196918397751701143567371451557 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2797 (b : ℝ) (hb : rootInterval.Contains b) : i2797.Contains (n2797 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2324 b hb) (b1983 b hb))
    (by norm_num [i2797, i2324, i1983, RationalInterval.mul]) (by norm_num [i2797, i2324, i1983, RationalInterval.mul])

def n2798 (b : ℝ) : ℝ := (n2435 b) * (n2018 b)
def i2798 : RationalInterval := ⟨(-57857199627946808978403884969 / 500000000000000000000000000000 : ℚ), (-11571402669651853056713861449 / 100000000000000000000000000000 : ℚ)⟩
theorem b2798 (b : ℝ) (hb : rootInterval.Contains b) : i2798.Contains (n2798 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2435 b hb) (b2018 b hb))
    (by norm_num [i2798, i2435, i2018, RationalInterval.mul]) (by norm_num [i2798, i2435, i2018, RationalInterval.mul])

def n2799 (b : ℝ) : ℝ := (n2797 b) + (n2798 b)
def i2799 : RationalInterval := ⟨(81203528893456520269747103511 / 1000000000000000000000000000000 : ℚ), (81204371055182613000232837067 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2799 (b : ℝ) (hb : rootInterval.Contains b) : i2799.Contains (n2799 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2797 b hb) (b2798 b hb))
    (by norm_num [i2799, i2797, i2798, RationalInterval.add]) (by norm_num [i2799, i2797, i2798, RationalInterval.add])

def n2800 (b : ℝ) : ℝ := (n2515 b) * (n2055 b)
def i2800 : RationalInterval := ⟨(-107860761817432575612390995449 / 200000000000000000000000000000 : ℚ), (-539297102438071122087648511509 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2800 (b : ℝ) (hb : rootInterval.Contains b) : i2800.Contains (n2800 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2515 b hb) (b2055 b hb))
    (by norm_num [i2800, i2515, i2055, RationalInterval.mul]) (by norm_num [i2800, i2515, i2055, RationalInterval.mul])

def n2801 (b : ℝ) : ℝ := (n2799 b) + (n2800 b)
def i2801 : RationalInterval := ⟨(-229050140096853178896103936867 / 500000000000000000000000000000 : ℚ), (-229046365691444254543707837221 / 500000000000000000000000000000 : ℚ)⟩
theorem b2801 (b : ℝ) (hb : rootInterval.Contains b) : i2801.Contains (n2801 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2799 b hb) (b2800 b hb))
    (by norm_num [i2801, i2799, i2800, RationalInterval.add]) (by norm_num [i2801, i2799, i2800, RationalInterval.add])

def n2802 (b : ℝ) : ℝ := (n2609 b) * (n2100 b)
def i2802 : RationalInterval := ⟨(893278120771731840138422744447 / 500000000000000000000000000000 : ℚ), (446640533958018575646434460567 / 250000000000000000000000000000 : ℚ)⟩
theorem b2802 (b : ℝ) (hb : rootInterval.Contains b) : i2802.Contains (n2802 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2609 b hb) (b2100 b hb))
    (by norm_num [i2802, i2609, i2100, RationalInterval.mul]) (by norm_num [i2802, i2609, i2100, RationalInterval.mul])

def n2803 (b : ℝ) : ℝ := (n2801 b) + (n2802 b)
def i2803 : RationalInterval := ⟨(33211399033743933062115940379 / 25000000000000000000000000000 : ℚ), (664234702224592896749161083913 / 500000000000000000000000000000 : ℚ)⟩
theorem b2803 (b : ℝ) (hb : rootInterval.Contains b) : i2803.Contains (n2803 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2801 b hb) (b2802 b hb))
    (by norm_num [i2803, i2801, i2802, RationalInterval.add]) (by norm_num [i2803, i2801, i2802, RationalInterval.add])

def n2804 (b : ℝ) : ℝ := (n2679 b) * (n2145 b)
def i2804 : RationalInterval := ⟨(-35961122310697106606781750207 / 1000000000000000000000000000000 : ℚ), (-35960123739103164612840180423 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2804 (b : ℝ) (hb : rootInterval.Contains b) : i2804.Contains (n2804 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2679 b hb) (b2145 b hb))
    (by norm_num [i2804, i2679, i2145, RationalInterval.mul]) (by norm_num [i2804, i2679, i2145, RationalInterval.mul])

def n2805 (b : ℝ) : ℝ := (n2803 b) + (n2804 b)
def i2805 : RationalInterval := ⟨(1292494839039060215877855864953 / 1000000000000000000000000000000 : ℚ), (1292509280710082628885481987403 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2805 (b : ℝ) (hb : rootInterval.Contains b) : i2805.Contains (n2805 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2803 b hb) (b2804 b hb))
    (by norm_num [i2805, i2803, i2804, RationalInterval.add]) (by norm_num [i2805, i2803, i2804, RationalInterval.add])

def n2806 (b : ℝ) : ℝ := (n2324 b) * (n1990 b)
def i2806 : RationalInterval := ⟨(94954161146144374115006982427 / 200000000000000000000000000000 : ℚ), (237386012175995133357246747581 / 500000000000000000000000000000 : ℚ)⟩
theorem b2806 (b : ℝ) (hb : rootInterval.Contains b) : i2806.Contains (n2806 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2324 b hb) (b1990 b hb))
    (by norm_num [i2806, i2324, i1990, RationalInterval.mul]) (by norm_num [i2806, i2324, i1990, RationalInterval.mul])

def n2807 (b : ℝ) : ℝ := (n2435 b) * (n2025 b)
def i2807 : RationalInterval := ⟨(-77545017494571194842175346941 / 1000000000000000000000000000000 : ℚ), (-77544569771597649883631883243 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2807 (b : ℝ) (hb : rootInterval.Contains b) : i2807.Contains (n2807 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2435 b hb) (b2025 b hb))
    (by norm_num [i2807, i2435, i2025, RationalInterval.mul]) (by norm_num [i2807, i2435, i2025, RationalInterval.mul])

def n2808 (b : ℝ) : ℝ := (n2806 b) + (n2807 b)
def i2808 : RationalInterval := ⟨(198612894118075337866429782597 / 500000000000000000000000000000 : ℚ), (397227454580392616830861611919 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2808 (b : ℝ) (hb : rootInterval.Contains b) : i2808.Contains (n2808 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2806 b hb) (b2807 b hb))
    (by norm_num [i2808, i2806, i2807, RationalInterval.add]) (by norm_num [i2808, i2806, i2807, RationalInterval.add])

def n2809 (b : ℝ) : ℝ := (n2515 b) * (n2064 b)
def i2809 : RationalInterval := ⟨(-1146990009468474704003189331683 / 1000000000000000000000000000000 : ℚ), (-71685941184307530796764746269 / 62500000000000000000000000000 : ℚ)⟩
theorem b2809 (b : ℝ) (hb : rootInterval.Contains b) : i2809.Contains (n2809 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2515 b hb) (b2064 b hb))
    (by norm_num [i2809, i2515, i2064, RationalInterval.mul]) (by norm_num [i2809, i2515, i2064, RationalInterval.mul])

def n2810 (b : ℝ) : ℝ := (n2808 b) + (n2809 b)
def i2810 : RationalInterval := ⟨(-749764221232324028270329766489 / 1000000000000000000000000000000 : ℚ), (-149949520873705575183474865677 / 200000000000000000000000000000 : ℚ)⟩
theorem b2810 (b : ℝ) (hb : rootInterval.Contains b) : i2810.Contains (n2810 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2808 b hb) (b2809 b hb))
    (by norm_num [i2810, i2808, i2809, RationalInterval.add]) (by norm_num [i2810, i2808, i2809, RationalInterval.add])

def n2811 (b : ℝ) : ℝ := (n2609 b) * (n2109 b)
def i2811 : RationalInterval := ⟨(2032193849609026751809733631763 / 500000000000000000000000000000 : ℚ), (4064401441864456294845806618873 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2811 (b : ℝ) (hb : rootInterval.Contains b) : i2811.Contains (n2811 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2609 b hb) (b2109 b hb))
    (by norm_num [i2811, i2609, i2109, RationalInterval.mul]) (by norm_num [i2811, i2609, i2109, RationalInterval.mul])

def n2812 (b : ℝ) : ℝ := (n2810 b) + (n2811 b)
def i2812 : RationalInterval := ⟨(3314623477985729475349137497037 / 1000000000000000000000000000000 : ℚ), (414331729686991052366054036311 / 125000000000000000000000000000 : ℚ)⟩
theorem b2812 (b : ℝ) (hb : rootInterval.Contains b) : i2812.Contains (n2812 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2810 b hb) (b2811 b hb))
    (by norm_num [i2812, i2810, i2811, RationalInterval.add]) (by norm_num [i2812, i2810, i2811, RationalInterval.add])

def n2813 (b : ℝ) : ℝ := (n2679 b) * (n2154 b)
def i2813 : RationalInterval := ⟨(-21859300050390769017728809307 / 250000000000000000000000000000 : ℚ), (-43717385408215244252055507061 / 500000000000000000000000000000 : ℚ)⟩
theorem b2813 (b : ℝ) (hb : rootInterval.Contains b) : i2813.Contains (n2813 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2679 b hb) (b2154 b hb))
    (by norm_num [i2813, i2679, i2154, RationalInterval.mul]) (by norm_num [i2813, i2679, i2154, RationalInterval.mul])

def n2814 (b : ℝ) : ℝ := (n2812 b) + (n2813 b)
def i2814 : RationalInterval := ⟨(3227186277784166399278222259809 / 1000000000000000000000000000000 : ℚ), (1613609533339748965212160638183 / 500000000000000000000000000000 : ℚ)⟩
theorem b2814 (b : ℝ) (hb : rootInterval.Contains b) : i2814.Contains (n2814 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2812 b hb) (b2813 b hb))
    (by norm_num [i2814, i2812, i2813, RationalInterval.add]) (by norm_num [i2814, i2812, i2813, RationalInterval.add])

def n2815 (b : ℝ) : ℝ := (n2324 b) * (n1997 b)
def i2815 : RationalInterval := ⟨(-44822319411040985008563365219 / 20000000000000000000000000000 : ℚ), (-280139100466410388739042952099 / 125000000000000000000000000000 : ℚ)⟩
theorem b2815 (b : ℝ) (hb : rootInterval.Contains b) : i2815.Contains (n2815 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2324 b hb) (b1997 b hb))
    (by norm_num [i2815, i2324, i1997, RationalInterval.mul]) (by norm_num [i2815, i2324, i1997, RationalInterval.mul])

def n2816 (b : ℝ) : ℝ := (n2435 b) * (n2032 b)
def i2816 : RationalInterval := ⟨(111895478607214324352423640807 / 125000000000000000000000000000 : ℚ), (223791556264621143780267738773 / 250000000000000000000000000000 : ℚ)⟩
theorem b2816 (b : ℝ) (hb : rootInterval.Contains b) : i2816.Contains (n2816 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2435 b hb) (b2032 b hb))
    (by norm_num [i2816, i2435, i2032, RationalInterval.mul]) (by norm_num [i2816, i2435, i2032, RationalInterval.mul])

def n2817 (b : ℝ) : ℝ := (n2815 b) + (n2816 b)
def i2817 : RationalInterval := ⟨(-672976070847167327804389567247 / 500000000000000000000000000000 : ℚ), (-13459465786727985347912726617 / 10000000000000000000000000000 : ℚ)⟩
theorem b2817 (b : ℝ) (hb : rootInterval.Contains b) : i2817.Contains (n2817 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2815 b hb) (b2816 b hb))
    (by norm_num [i2817, i2815, i2816, RationalInterval.add]) (by norm_num [i2817, i2815, i2816, RationalInterval.add])

def n2818 (b : ℝ) : ℝ := (n2515 b) * (n2073 b)
def i2818 : RationalInterval := ⟨(2697212959246158913256154717951 / 500000000000000000000000000000 : ℚ), (674310986086552721249210146177 / 125000000000000000000000000000 : ℚ)⟩
theorem b2818 (b : ℝ) (hb : rootInterval.Contains b) : i2818.Contains (n2818 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2515 b hb) (b2073 b hb))
    (by norm_num [i2818, i2515, i2073, RationalInterval.mul]) (by norm_num [i2818, i2515, i2073, RationalInterval.mul])

def n2819 (b : ℝ) : ℝ := (n2817 b) + (n2818 b)
def i2819 : RationalInterval := ⟨(126514805524936974090735321919 / 31250000000000000000000000000 : ℚ), (1012135327504905808800602126929 / 250000000000000000000000000000 : ℚ)⟩
theorem b2819 (b : ℝ) (hb : rootInterval.Contains b) : i2819.Contains (n2819 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2817 b hb) (b2818 b hb))
    (by norm_num [i2819, i2817, i2818, RationalInterval.add]) (by norm_num [i2819, i2817, i2818, RationalInterval.add])

def n2820 (b : ℝ) : ℝ := (n2609 b) * (n2118 b)
def i2820 : RationalInterval := ⟨(-19072479832763571515389814809927 / 1000000000000000000000000000000 : ℚ), (-19072422174354838134320158747161 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2820 (b : ℝ) (hb : rootInterval.Contains b) : i2820.Contains (n2820 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2609 b hb) (b2118 b hb))
    (by norm_num [i2820, i2609, i2118, RationalInterval.mul]) (by norm_num [i2820, i2609, i2118, RationalInterval.mul])

def n2821 (b : ℝ) : ℝ := (n2819 b) + (n2820 b)
def i2821 : RationalInterval := ⟨(-15024006055965588344486284508519 / 1000000000000000000000000000000 : ℚ), (-3004776172867042979823550047889 / 200000000000000000000000000000 : ℚ)⟩
theorem b2821 (b : ℝ) (hb : rootInterval.Contains b) : i2821.Contains (n2821 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2819 b hb) (b2820 b hb))
    (by norm_num [i2821, i2819, i2820, RationalInterval.add]) (by norm_num [i2821, i2819, i2820, RationalInterval.add])

def n2822 (b : ℝ) : ℝ := (n2679 b) * (n2163 b)
def i2822 : RationalInterval := ⟨(203521389563772850147853625049 / 500000000000000000000000000000 : ℚ), (407053943463668141137487620727 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2822 (b : ℝ) (hb : rootInterval.Contains b) : i2822.Contains (n2822 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2679 b hb) (b2163 b hb))
    (by norm_num [i2822, i2679, i2163, RationalInterval.mul]) (by norm_num [i2822, i2679, i2163, RationalInterval.mul])

def n2823 (b : ℝ) : ℝ := (n2821 b) + (n2822 b)
def i2823 : RationalInterval := ⟨(-14616963276838042644190577258421 / 1000000000000000000000000000000 : ℚ), (-7308413460435773378990131309359 / 500000000000000000000000000000 : ℚ)⟩
theorem b2823 (b : ℝ) (hb : rootInterval.Contains b) : i2823.Contains (n2823 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2821 b hb) (b2822 b hb))
    (by norm_num [i2823, i2821, i2822, RationalInterval.add]) (by norm_num [i2823, i2821, i2822, RationalInterval.add])

def n2824 (b : ℝ) : ℝ := (n2324 b) * (n2004 b)
def i2824 : RationalInterval := ⟨(1242417502343033079425538424303 / 1000000000000000000000000000000 : ℚ), (49696770140242810784263160061 / 40000000000000000000000000000 : ℚ)⟩
theorem b2824 (b : ℝ) (hb : rootInterval.Contains b) : i2824.Contains (n2824 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2324 b hb) (b2004 b hb))
    (by norm_num [i2824, i2324, i2004, RationalInterval.mul]) (by norm_num [i2824, i2324, i2004, RationalInterval.mul])

def n2825 (b : ℝ) : ℝ := (n2435 b) * (n2039 b)
def i2825 : RationalInterval := ⟨(-251782779959206788028650219589 / 500000000000000000000000000000 : ℚ), (-503564216107351080070594487277 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2825 (b : ℝ) (hb : rootInterval.Contains b) : i2825.Contains (n2825 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2435 b hb) (b2039 b hb))
    (by norm_num [i2825, i2435, i2039, RationalInterval.mul]) (by norm_num [i2825, i2435, i2039, RationalInterval.mul])

def n2826 (b : ℝ) : ℝ := (n2824 b) + (n2825 b)
def i2826 : RationalInterval := ⟨(5910815539396956026945903881 / 8000000000000000000000000000 : ℚ), (92356879674839898691998064281 / 125000000000000000000000000000 : ℚ)⟩
theorem b2826 (b : ℝ) (hb : rootInterval.Contains b) : i2826.Contains (n2826 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2824 b hb) (b2825 b hb))
    (by norm_num [i2826, i2824, i2825, RationalInterval.add]) (by norm_num [i2826, i2824, i2825, RationalInterval.add])

def n2827 (b : ℝ) : ℝ := (n2515 b) * (n2082 b)
def i2827 : RationalInterval := ⟨(-546662472863529134830849922713 / 200000000000000000000000000000 : ℚ), (-341660095759532464357646945139 / 125000000000000000000000000000 : ℚ)⟩
theorem b2827 (b : ℝ) (hb : rootInterval.Contains b) : i2827.Contains (n2827 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2515 b hb) (b2082 b hb))
    (by norm_num [i2827, i2515, i2082, RationalInterval.mul]) (by norm_num [i2827, i2515, i2082, RationalInterval.mul])

def n2828 (b : ℝ) : ℝ := (n2826 b) + (n2827 b)
def i2828 : RationalInterval := ⟨(-49861510547325654269650290711 / 25000000000000000000000000000 : ℚ), (-124651608042346282832824440429 / 62500000000000000000000000000 : ℚ)⟩
theorem b2828 (b : ℝ) (hb : rootInterval.Contains b) : i2828.Contains (n2828 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2826 b hb) (b2827 b hb))
    (by norm_num [i2828, i2826, i2827, RationalInterval.add]) (by norm_num [i2828, i2826, i2827, RationalInterval.add])

def n2829 (b : ℝ) : ℝ := (n2609 b) * (n2127 b)
def i2829 : RationalInterval := ⟨(10197149048863449573675934982703 / 1000000000000000000000000000000 : ℚ), (2039435989893903305728972054281 / 200000000000000000000000000000 : ℚ)⟩
theorem b2829 (b : ℝ) (hb : rootInterval.Contains b) : i2829.Contains (n2829 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2609 b hb) (b2127 b hb))
    (by norm_num [i2829, i2609, i2127, RationalInterval.mul]) (by norm_num [i2829, i2609, i2127, RationalInterval.mul])

def n2830 (b : ℝ) : ℝ := (n2828 b) + (n2829 b)
def i2830 : RationalInterval := ⟨(8202688626970423402889923354263 / 1000000000000000000000000000000 : ℚ), (8202754220791976003319669224541 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2830 (b : ℝ) (hb : rootInterval.Contains b) : i2830.Contains (n2830 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2828 b hb) (b2829 b hb))
    (by norm_num [i2830, i2828, i2829, RationalInterval.add]) (by norm_num [i2830, i2828, i2829, RationalInterval.add])

def n2831 (b : ℝ) : ℝ := (n2679 b) * (n2172 b)
def i2831 : RationalInterval := ⟨(-220856775570312385158014523053 / 1000000000000000000000000000000 : ℚ), (-220850719071037838515200866697 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2831 (b : ℝ) (hb : rootInterval.Contains b) : i2831.Contains (n2831 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2679 b hb) (b2172 b hb))
    (by norm_num [i2831, i2679, i2172, RationalInterval.mul]) (by norm_num [i2831, i2679, i2172, RationalInterval.mul])

def n2832 (b : ℝ) : ℝ := (n2830 b) + (n2831 b)
def i2832 : RationalInterval := ⟨(798183185140011101773190883121 / 100000000000000000000000000000 : ℚ), (1995475875430234541201117089461 / 250000000000000000000000000000 : ℚ)⟩
theorem b2832 (b : ℝ) (hb : rootInterval.Contains b) : i2832.Contains (n2832 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2830 b hb) (b2831 b hb))
    (by norm_num [i2832, i2830, i2831, RationalInterval.add]) (by norm_num [i2832, i2830, i2831, RationalInterval.add])

def n2833 (b : ℝ) : ℝ := (n2324 b) * (n2011 b)
def i2833 : RationalInterval := ⟨(327624379457248500942084091363 / 200000000000000000000000000000 : ℚ), (819062080856060462143225900891 / 500000000000000000000000000000 : ℚ)⟩
theorem b2833 (b : ℝ) (hb : rootInterval.Contains b) : i2833.Contains (n2833 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2324 b hb) (b2011 b hb))
    (by norm_num [i2833, i2324, i2011, RationalInterval.mul]) (by norm_num [i2833, i2324, i2011, RationalInterval.mul])

def n2834 (b : ℝ) : ℝ := (n2435 b) * (n2046 b)
def i2834 : RationalInterval := ⟨(-372735273662313920904174236873 / 500000000000000000000000000000 : ℚ), (-745468599824062226763925741841 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2834 (b : ℝ) (hb : rootInterval.Contains b) : i2834.Contains (n2834 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2435 b hb) (b2046 b hb))
    (by norm_num [i2834, i2435, i2046, RationalInterval.mul]) (by norm_num [i2834, i2435, i2046, RationalInterval.mul])

def n2835 (b : ℝ) : ℝ := (n2833 b) + (n2834 b)
def i2835 : RationalInterval := ⟨(892651349961614662902071983069 / 1000000000000000000000000000000 : ℚ), (892655561888058697522526059941 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2835 (b : ℝ) (hb : rootInterval.Contains b) : i2835.Contains (n2835 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2833 b hb) (b2834 b hb))
    (by norm_num [i2835, i2833, i2834, RationalInterval.add]) (by norm_num [i2835, i2833, i2834, RationalInterval.add])

def n2836 (b : ℝ) : ℝ := (n2515 b) * (n2091 b)
def i2836 : RationalInterval := ⟨(-408691027274906541803445219511 / 100000000000000000000000000000 : ℚ), (-4086863581259153619121393012687 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2836 (b : ℝ) (hb : rootInterval.Contains b) : i2836.Contains (n2836 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2515 b hb) (b2091 b hb))
    (by norm_num [i2836, i2515, i2091, RationalInterval.mul]) (by norm_num [i2836, i2515, i2091, RationalInterval.mul])

def n2837 (b : ℝ) : ℝ := (n2835 b) + (n2836 b)
def i2837 : RationalInterval := ⟨(-3194258922787450755132380212041 / 1000000000000000000000000000000 : ℚ), (-1597104009685547460799433476373 / 500000000000000000000000000000 : ℚ)⟩
theorem b2837 (b : ℝ) (hb : rootInterval.Contains b) : i2837.Contains (n2837 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2835 b hb) (b2836 b hb))
    (by norm_num [i2837, i2835, i2836, RationalInterval.add]) (by norm_num [i2837, i2835, i2836, RationalInterval.add])

def n2838 (b : ℝ) : ℝ := (n2609 b) * (n2136 b)
def i2838 : RationalInterval := ⟨(2807923021112160398380044186493 / 200000000000000000000000000000 : ℚ), (87747859407120839053630937937 / 6250000000000000000000000000 : ℚ)⟩
theorem b2838 (b : ℝ) (hb : rootInterval.Contains b) : i2838.Contains (n2838 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2609 b hb) (b2136 b hb))
    (by norm_num [i2838, i2609, i2136, RationalInterval.mul]) (by norm_num [i2838, i2609, i2136, RationalInterval.mul])

def n2839 (b : ℝ) : ℝ := (n2837 b) + (n2838 b)
def i2839 : RationalInterval := ⟨(1355669522846668904595980090053 / 125000000000000000000000000000 : ℚ), (5422724742884119663491041558587 / 500000000000000000000000000000 : ℚ)⟩
theorem b2839 (b : ℝ) (hb : rootInterval.Contains b) : i2839.Contains (n2839 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2837 b hb) (b2838 b hb))
    (by norm_num [i2839, i2837, i2838, RationalInterval.add]) (by norm_num [i2839, i2837, i2838, RationalInterval.add])

def n2840 (b : ℝ) : ℝ := (n2679 b) * (n2181 b)
def i2840 : RationalInterval := ⟨(-302002121635283663944912915667 / 1000000000000000000000000000000 : ℚ), (-1887461503189116999185193173 / 6250000000000000000000000000 : ℚ)⟩
theorem b2840 (b : ℝ) (hb : rootInterval.Contains b) : i2840.Contains (n2840 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2679 b hb) (b2181 b hb))
    (by norm_num [i2840, i2679, i2181, RationalInterval.mul]) (by norm_num [i2840, i2679, i2181, RationalInterval.mul])

def n2841 (b : ℝ) : ℝ := (n2839 b) + (n2840 b)
def i2841 : RationalInterval := ⟨(10543354061138067572822927804757 / 1000000000000000000000000000000 : ℚ), (5271727822628990303556226104747 / 500000000000000000000000000000 : ℚ)⟩
theorem b2841 (b : ℝ) (hb : rootInterval.Contains b) : i2841.Contains (n2841 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2839 b hb) (b2840 b hb))
    (by norm_num [i2841, i2839, i2840, RationalInterval.add]) (by norm_num [i2841, i2839, i2840, RationalInterval.add])

def n2842 (b : ℝ) : ℝ := (n2326 b) * (n1983 b)
def i2842 : RationalInterval := ⟨(75565059389695972224782993809 / 1000000000000000000000000000000 : ℚ), (2361414248573148776624323563 / 31250000000000000000000000000 : ℚ)⟩
theorem b2842 (b : ℝ) (hb : rootInterval.Contains b) : i2842.Contains (n2842 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2326 b hb) (b1983 b hb))
    (by norm_num [i2842, i2326, i1983, RationalInterval.mul]) (by norm_num [i2842, i2326, i1983, RationalInterval.mul])

def n2843 (b : ℝ) : ℝ := (n2437 b) * (n2018 b)
def i2843 : RationalInterval := ⟨(-40150455067046235152335758729 / 1000000000000000000000000000000 : ℚ), (-8030059395287576821061599991 / 200000000000000000000000000000 : ℚ)⟩
theorem b2843 (b : ℝ) (hb : rootInterval.Contains b) : i2843.Contains (n2843 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2437 b hb) (b2018 b hb))
    (by norm_num [i2843, i2437, i2018, RationalInterval.mul]) (by norm_num [i2843, i2437, i2018, RationalInterval.mul])

def n2844 (b : ℝ) : ℝ := (n2842 b) + (n2843 b)
def i2844 : RationalInterval := ⟨(885365108066243426811180877 / 25000000000000000000000000000 : ℚ), (35414958977902876746670354061 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2844 (b : ℝ) (hb : rootInterval.Contains b) : i2844.Contains (n2844 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2842 b hb) (b2843 b hb))
    (by norm_num [i2844, i2842, i2843, RationalInterval.add]) (by norm_num [i2844, i2842, i2843, RationalInterval.add])

def n2845 (b : ℝ) : ℝ := (n2510 b) * (n2055 b)
def i2845 : RationalInterval := ⟨(914195133159105819235827382529 / 500000000000000000000000000000 : ℚ), (457099021993749901683526736301 / 250000000000000000000000000000 : ℚ)⟩
theorem b2845 (b : ℝ) (hb : rootInterval.Contains b) : i2845.Contains (n2845 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2510 b hb) (b2055 b hb))
    (by norm_num [i2845, i2510, i2055, RationalInterval.mul]) (by norm_num [i2845, i2510, i2055, RationalInterval.mul])

def n2846 (b : ℝ) : ℝ := (n2844 b) + (n2845 b)
def i2846 : RationalInterval := ⟨(931902435320430687772051000069 / 500000000000000000000000000000 : ℚ), (372762209390580496696155459853 / 200000000000000000000000000000 : ℚ)⟩
theorem b2846 (b : ℝ) (hb : rootInterval.Contains b) : i2846.Contains (n2846 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2844 b hb) (b2845 b hb))
    (by norm_num [i2846, i2844, i2845, RationalInterval.add]) (by norm_num [i2846, i2844, i2845, RationalInterval.add])

def n2847 (b : ℝ) : ℝ := (n2611 b) * (n2100 b)
def i2847 : RationalInterval := ⟨(-1005626356938908641560880674993 / 250000000000000000000000000000 : ℚ), (-160899967479385674778460277059 / 40000000000000000000000000000 : ℚ)⟩
theorem b2847 (b : ℝ) (hb : rootInterval.Contains b) : i2847.Contains (n2847 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2611 b hb) (b2100 b hb))
    (by norm_num [i2847, i2611, i2100, RationalInterval.mul]) (by norm_num [i2847, i2611, i2100, RationalInterval.mul])

def n2848 (b : ℝ) : ℝ := (n2846 b) + (n2847 b)
def i2848 : RationalInterval := ⟨(-1079350278557386595349710349917 / 500000000000000000000000000000 : ℚ), (-215868814003173938598072962721 / 100000000000000000000000000000 : ℚ)⟩
theorem b2848 (b : ℝ) (hb : rootInterval.Contains b) : i2848.Contains (n2848 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2846 b hb) (b2847 b hb))
    (by norm_num [i2848, i2846, i2847, RationalInterval.add]) (by norm_num [i2848, i2846, i2847, RationalInterval.add])

def n2849 (b : ℝ) : ℝ := (n2681 b) * (n2145 b)
def i2849 : RationalInterval := ⟨(2833268462406731753984501220233 / 1000000000000000000000000000000 : ℚ), (566654471107338926865203525057 / 200000000000000000000000000000 : ℚ)⟩
theorem b2849 (b : ℝ) (hb : rootInterval.Contains b) : i2849.Contains (n2849 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2681 b hb) (b2145 b hb))
    (by norm_num [i2849, i2681, i2145, RationalInterval.mul]) (by norm_num [i2849, i2681, i2145, RationalInterval.mul])

def n2850 (b : ℝ) : ℝ := (n2848 b) + (n2849 b)
def i2850 : RationalInterval := ⟨(674567905291958563285080520399 / 1000000000000000000000000000000 : ℚ), (26983368620198209933811519923 / 40000000000000000000000000000 : ℚ)⟩
theorem b2850 (b : ℝ) (hb : rootInterval.Contains b) : i2850.Contains (n2850 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2848 b hb) (b2849 b hb))
    (by norm_num [i2850, i2848, i2849, RationalInterval.add]) (by norm_num [i2850, i2848, i2849, RationalInterval.add])

def n2851 (b : ℝ) : ℝ := (n2326 b) * (n1990 b)
def i2851 : RationalInterval := ⟨(182188003239227682300066799303 / 1000000000000000000000000000000 : ℚ), (45547127578901804771487783803 / 250000000000000000000000000000 : ℚ)⟩
theorem b2851 (b : ℝ) (hb : rootInterval.Contains b) : i2851.Contains (n2851 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2326 b hb) (b1990 b hb))
    (by norm_num [i2851, i2326, i1990, RationalInterval.mul]) (by norm_num [i2851, i2326, i1990, RationalInterval.mul])

def n2852 (b : ℝ) : ℝ := (n2437 b) * (n2025 b)
def i2852 : RationalInterval := ⟨(-5381296987428327227581209209 / 200000000000000000000000000000 : ℚ), (-5381262054608678075039465569 / 200000000000000000000000000000 : ℚ)⟩
theorem b2852 (b : ℝ) (hb : rootInterval.Contains b) : i2852.Contains (n2852 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2437 b hb) (b2025 b hb))
    (by norm_num [i2852, i2437, i2025, RationalInterval.mul]) (by norm_num [i2852, i2437, i2025, RationalInterval.mul])

def n2853 (b : ℝ) : ℝ := (n2851 b) + (n2852 b)
def i2853 : RationalInterval := ⟨(77640759151043023081080376629 / 500000000000000000000000000000 : ℚ), (155282200042563828710753807367 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2853 (b : ℝ) (hb : rootInterval.Contains b) : i2853.Contains (n2853 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2851 b hb) (b2852 b hb))
    (by norm_num [i2853, i2851, i2852, RationalInterval.add]) (by norm_num [i2853, i2851, i2852, RationalInterval.add])

def n2854 (b : ℝ) : ℝ := (n2510 b) * (n2064 b)
def i2854 : RationalInterval := ⟨(3888613574987232030004748513313 / 1000000000000000000000000000000 : ℚ), (3888628285063017001199059206573 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2854 (b : ℝ) (hb : rootInterval.Contains b) : i2854.Contains (n2854 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2510 b hb) (b2064 b hb))
    (by norm_num [i2854, i2510, i2064, RationalInterval.mul]) (by norm_num [i2854, i2510, i2064, RationalInterval.mul])

def n2855 (b : ℝ) : ℝ := (n2853 b) + (n2854 b)
def i2855 : RationalInterval := ⟨(4043895093289318076166909266571 / 1000000000000000000000000000000 : ℚ), (202195524255279041495490650697 / 50000000000000000000000000000 : ℚ)⟩
theorem b2855 (b : ℝ) (hb : rootInterval.Contains b) : i2855.Contains (n2855 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2853 b hb) (b2854 b hb))
    (by norm_num [i2855, i2853, i2854, RationalInterval.add]) (by norm_num [i2855, i2853, i2854, RationalInterval.add])

def n2856 (b : ℝ) : ℝ := (n2611 b) * (n2109 b)
def i2856 : RationalInterval := ⟨(-9151138117490201816019090970799 / 1000000000000000000000000000000 : ℚ), (-1830224633910273444428002766617 / 200000000000000000000000000000 : ℚ)⟩
theorem b2856 (b : ℝ) (hb : rootInterval.Contains b) : i2856.Contains (n2856 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2611 b hb) (b2109 b hb))
    (by norm_num [i2856, i2611, i2109, RationalInterval.mul]) (by norm_num [i2856, i2611, i2109, RationalInterval.mul])

def n2857 (b : ℝ) : ℝ := (n2855 b) + (n2856 b)
def i2857 : RationalInterval := ⟨(-1276810756050220934963045426057 / 250000000000000000000000000000 : ℚ), (-1021442536889157278446040163829 / 200000000000000000000000000000 : ℚ)⟩
theorem b2857 (b : ℝ) (hb : rootInterval.Contains b) : i2857.Contains (n2857 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2855 b hb) (b2856 b hb))
    (by norm_num [i2857, i2855, i2856, RationalInterval.add]) (by norm_num [i2857, i2855, i2856, RationalInterval.add])

def n2858 (b : ℝ) : ℝ := (n2681 b) * (n2154 b)
def i2858 : RationalInterval := ⟨(53819636020053920581156623539 / 7812500000000000000000000000 : ℚ), (6888922988449796623722109272497 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2858 (b : ℝ) (hb : rootInterval.Contains b) : i2858.Contains (n2858 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2681 b hb) (b2154 b hb))
    (by norm_num [i2858, i2681, i2154, RationalInterval.mul]) (by norm_num [i2858, i2681, i2154, RationalInterval.mul])

def n2859 (b : ℝ) : ℝ := (n2857 b) + (n2858 b)
def i2859 : RationalInterval := ⟨(445417596591504523633966527191 / 250000000000000000000000000000 : ℚ), (222713788000501278936488556669 / 125000000000000000000000000000 : ℚ)⟩
theorem b2859 (b : ℝ) (hb : rootInterval.Contains b) : i2859.Contains (n2859 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2857 b hb) (b2858 b hb))
    (by norm_num [i2859, i2857, i2858, RationalInterval.add]) (by norm_num [i2859, i2857, i2858, RationalInterval.add])

def n2860 (b : ℝ) : ℝ := (n2326 b) * (n1997 b)
def i2860 : RationalInterval := ⟨(-215000863138832114956732444823 / 250000000000000000000000000000 : ℚ), (-860002051131276559288824671849 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2860 (b : ℝ) (hb : rootInterval.Contains b) : i2860.Contains (n2860 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2326 b hb) (b1997 b hb))
    (by norm_num [i2860, i2326, i1997, RationalInterval.mul]) (by norm_num [i2860, i2326, i1997, RationalInterval.mul])

def n2861 (b : ℝ) : ℝ := (n2437 b) * (n2032 b)
def i2861 : RationalInterval := ⟨(155301369234451728671429749083 / 500000000000000000000000000000 : ℚ), (77650948213598193217671871631 / 250000000000000000000000000000 : ℚ)⟩
theorem b2861 (b : ℝ) (hb : rootInterval.Contains b) : i2861.Contains (n2861 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2437 b hb) (b2032 b hb))
    (by norm_num [i2861, i2437, i2032, RationalInterval.mul]) (by norm_num [i2861, i2437, i2032, RationalInterval.mul])

def n2862 (b : ℝ) : ℝ := (n2860 b) + (n2861 b)
def i2862 : RationalInterval := ⟨(-274700357043212501242035140563 / 500000000000000000000000000000 : ℚ), (-21975930331075351456725487413 / 40000000000000000000000000000 : ℚ)⟩
theorem b2862 (b : ℝ) (hb : rootInterval.Contains b) : i2862.Contains (n2862 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2860 b hb) (b2861 b hb))
    (by norm_num [i2862, i2860, i2861, RationalInterval.add]) (by norm_num [i2862, i2860, i2861, RationalInterval.add])

def n2863 (b : ℝ) : ℝ := (n2510 b) * (n2073 b)
def i2863 : RationalInterval := ⟨(-18288876114204541066359246476639 / 1000000000000000000000000000000 : ℚ), (-18288835221173174138242161741803 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2863 (b : ℝ) (hb : rootInterval.Contains b) : i2863.Contains (n2863 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2510 b hb) (b2073 b hb))
    (by norm_num [i2863, i2510, i2073, RationalInterval.mul]) (by norm_num [i2863, i2510, i2073, RationalInterval.mul])

def n2864 (b : ℝ) : ℝ := (n2862 b) + (n2863 b)
def i2864 : RationalInterval := ⟨(-3767655365658193213768663351553 / 200000000000000000000000000000 : ℚ), (-2354779184931257240582537365891 / 125000000000000000000000000000 : ℚ)⟩
theorem b2864 (b : ℝ) (hb : rootInterval.Contains b) : i2864.Contains (n2864 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2862 b hb) (b2863 b hb))
    (by norm_num [i2864, i2862, i2863, RationalInterval.add]) (by norm_num [i2864, i2862, i2863, RationalInterval.add])

def n2865 (b : ℝ) : ℝ := (n2611 b) * (n2118 b)
def i2865 : RationalInterval := ⟨(42942282423692600142394715139431 / 1000000000000000000000000000000 : ℚ), (4294233719014767352901670064997 / 100000000000000000000000000000 : ℚ)⟩
theorem b2865 (b : ℝ) (hb : rootInterval.Contains b) : i2865.Contains (n2865 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2611 b hb) (b2118 b hb))
    (by norm_num [i2865, i2611, i2118, RationalInterval.mul]) (by norm_num [i2865, i2611, i2118, RationalInterval.mul])

def n2866 (b : ℝ) : ℝ := (n2864 b) + (n2865 b)
def i2866 : RationalInterval := ⟨(12052002797700817036775699190833 / 500000000000000000000000000000 : ℚ), (12052051855348807802178200861421 / 500000000000000000000000000000 : ℚ)⟩
theorem b2866 (b : ℝ) (hb : rootInterval.Contains b) : i2866.Contains (n2866 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2864 b hb) (b2865 b hb))
    (by norm_num [i2866, i2864, i2865, RationalInterval.add]) (by norm_num [i2866, i2864, i2865, RationalInterval.add])

def n2867 (b : ℝ) : ℝ := (n2681 b) * (n2163 b)
def i2867 : RationalInterval := ⟨(-16035298832772315289305388455033 / 500000000000000000000000000000 : ℚ), (-32070564531968052364974024359471 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2867 (b : ℝ) (hb : rootInterval.Contains b) : i2867.Contains (n2867 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2681 b hb) (b2163 b hb))
    (by norm_num [i2867, i2681, i2163, RationalInterval.mul]) (by norm_num [i2867, i2681, i2163, RationalInterval.mul])

def n2868 (b : ℝ) : ℝ := (n2866 b) + (n2867 b)
def i2868 : RationalInterval := ⟨(-19916480175357491262648446321 / 2500000000000000000000000000 : ℚ), (-7966460821270436760617622636629 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2868 (b : ℝ) (hb : rootInterval.Contains b) : i2868.Contains (n2868 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2866 b hb) (b2867 b hb))
    (by norm_num [i2868, i2866, i2867, RationalInterval.add]) (by norm_num [i2868, i2866, i2867, RationalInterval.add])

def n2869 (b : ℝ) : ℝ := (n2326 b) * (n2004 b)
def i2869 : RationalInterval := ⟨(238381932091384488753290140407 / 500000000000000000000000000000 : ℚ), (5959557992402980955052591829 / 12500000000000000000000000000 : ℚ)⟩
theorem b2869 (b : ℝ) (hb : rootInterval.Contains b) : i2869.Contains (n2869 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2326 b hb) (b2004 b hb))
    (by norm_num [i2869, i2326, i2004, RationalInterval.mul]) (by norm_num [i2869, i2326, i2004, RationalInterval.mul])

def n2870 (b : ℝ) : ℝ := (n2437 b) * (n2039 b)
def i2870 : RationalInterval := ⟨(-174726624489531461056791399487 / 1000000000000000000000000000000 : ℚ), (-43681508198749760278770379689 / 250000000000000000000000000000 : ℚ)⟩
theorem b2870 (b : ℝ) (hb : rootInterval.Contains b) : i2870.Contains (n2870 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2437 b hb) (b2039 b hb))
    (by norm_num [i2870, i2437, i2039, RationalInterval.mul]) (by norm_num [i2870, i2437, i2039, RationalInterval.mul])

def n2871 (b : ℝ) : ℝ := (n2869 b) + (n2870 b)
def i2871 : RationalInterval := ⟨(302037239693237516449788881327 / 1000000000000000000000000000000 : ℚ), (75509651649309858822281456891 / 250000000000000000000000000000 : ℚ)⟩
theorem b2871 (b : ℝ) (hb : rootInterval.Contains b) : i2871.Contains (n2871 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2869 b hb) (b2870 b hb))
    (by norm_num [i2871, i2869, i2870, RationalInterval.add]) (by norm_num [i2871, i2869, i2870, RationalInterval.add])

def n2872 (b : ℝ) : ℝ := (n2510 b) * (n2082 b)
def i2872 : RationalInterval := ⟨(370667962072538248176221499439 / 40000000000000000000000000000 : ℚ), (4633360222868707971355388803557 / 500000000000000000000000000000 : ℚ)⟩
theorem b2872 (b : ℝ) (hb : rootInterval.Contains b) : i2872.Contains (n2872 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2510 b hb) (b2082 b hb))
    (by norm_num [i2872, i2510, i2082, RationalInterval.mul]) (by norm_num [i2872, i2510, i2082, RationalInterval.mul])

def n2873 (b : ℝ) : ℝ := (n2871 b) + (n2872 b)
def i2873 : RationalInterval := ⟨(4784368145753346860427663183651 / 500000000000000000000000000000 : ℚ), (4784379526167327688999951717339 / 500000000000000000000000000000 : ℚ)⟩
theorem b2873 (b : ℝ) (hb : rootInterval.Contains b) : i2873.Contains (n2873 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2871 b hb) (b2872 b hb))
    (by norm_num [i2873, i2871, i2872, RationalInterval.add]) (by norm_num [i2873, i2871, i2872, RationalInterval.add])

def n2874 (b : ℝ) : ℝ := (n2611 b) * (n2127 b)
def i2874 : RationalInterval := ⟨(-22959297564782551571591337598141 / 1000000000000000000000000000000 : ℚ), (-11479634059316723097131609046083 / 500000000000000000000000000000 : ℚ)⟩
theorem b2874 (b : ℝ) (hb : rootInterval.Contains b) : i2874.Contains (n2874 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2611 b hb) (b2127 b hb))
    (by norm_num [i2874, i2611, i2127, RationalInterval.mul]) (by norm_num [i2874, i2611, i2127, RationalInterval.mul])

def n2875 (b : ℝ) : ℝ := (n2873 b) + (n2874 b)
def i2875 : RationalInterval := ⟨(-13390561273275857850736011230839 / 1000000000000000000000000000000 : ℚ), (-836906816643674426016457166093 / 62500000000000000000000000000 : ℚ)⟩
theorem b2875 (b : ℝ) (hb : rootInterval.Contains b) : i2875.Contains (n2875 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2873 b hb) (b2874 b hb))
    (by norm_num [i2875, i2873, i2874, RationalInterval.add]) (by norm_num [i2875, i2873, i2874, RationalInterval.add])

def n2876 (b : ℝ) : ℝ := (n2681 b) * (n2172 b)
def i2876 : RationalInterval := ⟨(4350161457894262801773818246871 / 250000000000000000000000000000 : ℚ), (87003318660358012660622145987 / 5000000000000000000000000000 : ℚ)⟩
theorem b2876 (b : ℝ) (hb : rootInterval.Contains b) : i2876.Contains (n2876 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2681 b hb) (b2172 b hb))
    (by norm_num [i2876, i2681, i2172, RationalInterval.mul]) (by norm_num [i2876, i2681, i2172, RationalInterval.mul])

def n2877 (b : ℝ) : ℝ := (n2875 b) + (n2876 b)
def i2877 : RationalInterval := ⟨(802016911660238671271852351329 / 200000000000000000000000000000 : ℚ), (501269333221601464482639317489 / 125000000000000000000000000000 : ℚ)⟩
theorem b2877 (b : ℝ) (hb : rootInterval.Contains b) : i2877.Contains (n2877 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2875 b hb) (b2876 b hb))
    (by norm_num [i2877, i2875, i2876, RationalInterval.add]) (by norm_num [i2877, i2875, i2876, RationalInterval.add])

def n2878 (b : ℝ) : ℝ := (n2326 b) * (n2011 b)
def i2878 : RationalInterval := ⟨(157152753458427130027007893757 / 250000000000000000000000000000 : ℚ), (125722403775446069310312324671 / 200000000000000000000000000000 : ℚ)⟩
theorem b2878 (b : ℝ) (hb : rootInterval.Contains b) : i2878.Contains (n2878 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2326 b hb) (b2011 b hb))
    (by norm_num [i2878, i2326, i2011, RationalInterval.mul]) (by norm_num [i2878, i2326, i2011, RationalInterval.mul])

def n2879 (b : ℝ) : ℝ := (n2437 b) * (n2046 b)
def i2879 : RationalInterval := ⟨(-258662551131374221892605815547 / 1000000000000000000000000000000 : ℚ), (-64665422429824472118976593809 / 250000000000000000000000000000 : ℚ)⟩
theorem b2879 (b : ℝ) (hb : rootInterval.Contains b) : i2879.Contains (n2879 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2437 b hb) (b2046 b hb))
    (by norm_num [i2879, i2437, i2046, RationalInterval.mul]) (by norm_num [i2879, i2437, i2046, RationalInterval.mul])

