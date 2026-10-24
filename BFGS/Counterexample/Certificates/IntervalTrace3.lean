import BFGS.Counterexample.Certificates.IntervalTrace2

/-! Generated arithmetic proofs. Each bound is checked by the Lean kernel. -/
namespace BFGS.Counterexample.Trace
noncomputable section
open BFGS RationalInterval
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false

def n270 (b : ℝ) : ℝ := -(n269 b)
def i270 : RationalInterval := ⟨(27860704139260616301564707769 / 25000000000000000000000000000 : ℚ), (1114428167363675772722560949887 / 1000000000000000000000000000000 : ℚ)⟩
theorem b270 (b : ℝ) (hb : rootInterval.Contains b) : i270.Contains (n270 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b269 b hb))
    (by norm_num [i270, i269, RationalInterval.neg]) (by norm_num [i270, i269, RationalInterval.neg])

def n271 (b : ℝ) : ℝ := 1 / (n270 b)
def i271 : RationalInterval := ⟨(224330295411867947224101842887 / 250000000000000000000000000000 : ℚ), (448660591545685619111535313797 / 500000000000000000000000000000 : ℚ)⟩
theorem b271 (b : ℝ) (hb : rootInterval.Contains b) : i271.Contains (n271 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_inv_of_positive (b270 b hb) (by norm_num [i270]))
    (by norm_num [i271, i270, RationalInterval.inv]) (by norm_num [i271, i270, RationalInterval.inv])

def n272 (b : ℝ) : ℝ := (n161 b) * (n271 b)
def i272 : RationalInterval := ⟨(279050971470655456126052160319 / 1000000000000000000000000000000 : ℚ), (139525486658067645808533855091 / 500000000000000000000000000000 : ℚ)⟩
theorem b272 (b : ℝ) (hb : rootInterval.Contains b) : i272.Contains (n272 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b161 b hb) (b271 b hb))
    (by norm_num [i272, i161, i271, RationalInterval.mul]) (by norm_num [i272, i161, i271, RationalInterval.mul])

def n273 (b : ℝ) : ℝ := (n236 b) * (n271 b)
def i273 : RationalInterval := ⟨(1052004467330947044077714970583 / 1000000000000000000000000000000 : ℚ), (1052004471270993752731922832631 / 1000000000000000000000000000000 : ℚ)⟩
theorem b273 (b : ℝ) (hb : rootInterval.Contains b) : i273.Contains (n273 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b236 b hb) (b271 b hb))
    (by norm_num [i273, i236, i271, RationalInterval.mul]) (by norm_num [i273, i236, i271, RationalInterval.mul])

def n274 (b : ℝ) : ℝ := (n21 b) * (n241 b)
def i274 : RationalInterval := ⟨(-52193991079838792884582046853 / 1000000000000000000000000000000 : ℚ), (-40776555516461430982614773 / 781250000000000000000000000 : ℚ)⟩
theorem b274 (b : ℝ) (hb : rootInterval.Contains b) : i274.Contains (n274 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b21 b hb) (b241 b hb))
    (by norm_num [i274, i21, i241, RationalInterval.mul]) (by norm_num [i274, i21, i241, RationalInterval.mul])

def n275 (b : ℝ) : ℝ := (n274 b) + (n55 b)
def i275 : RationalInterval := ⟨(5823056441057200660041310961 / 200000000000000000000000000000 : ℚ), (5823056557140610505326819789 / 200000000000000000000000000000 : ℚ)⟩
theorem b275 (b : ℝ) (hb : rootInterval.Contains b) : i275.Contains (n275 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b274 b hb) (b55 b hb))
    (by norm_num [i275, i274, i55, RationalInterval.add]) (by norm_num [i275, i274, i55, RationalInterval.add])

def n276 (b : ℝ) : ℝ := (n210 b) * (n241 b)
def i276 : RationalInterval := ⟨(-15200780115914061140753054239 / 1000000000000000000000000000000 : ℚ), (-15200779908554508359063382599 / 1000000000000000000000000000000 : ℚ)⟩
theorem b276 (b : ℝ) (hb : rootInterval.Contains b) : i276.Contains (n276 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b210 b hb) (b241 b hb))
    (by norm_num [i276, i210, i241, RationalInterval.mul]) (by norm_num [i276, i210, i241, RationalInterval.mul])

def n277 (b : ℝ) : ℝ := (n276 b) + (n211 b)
def i277 : RationalInterval := ⟨(-1089462613925599541674512733767 / 1000000000000000000000000000000 : ℚ), (-544731301381370925868203568733 / 500000000000000000000000000000 : ℚ)⟩
theorem b277 (b : ℝ) (hb : rootInterval.Contains b) : i277.Contains (n277 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b276 b hb) (b211 b hb))
    (by norm_num [i277, i276, i211, RationalInterval.add]) (by norm_num [i277, i276, i211, RationalInterval.add])

def n278 (b : ℝ) : ℝ := (n212 b) * (n241 b)
def i278 : RationalInterval := ⟨(-53713091690484274026687983977 / 1000000000000000000000000000000 : ℚ), (-53713091142709367168867187743 / 1000000000000000000000000000000 : ℚ)⟩
theorem b278 (b : ℝ) (hb : rootInterval.Contains b) : i278.Contains (n278 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b212 b hb) (b241 b hb))
    (by norm_num [i278, i212, i241, RationalInterval.mul]) (by norm_num [i278, i212, i241, RationalInterval.mul])

def n279 (b : ℝ) : ℝ := (n278 b) + (n213 b)
def i279 : RationalInterval := ⟨(-962424376066661144760146577383 / 250000000000000000000000000000 : ℚ), (-1924848739038588863133513674911 / 500000000000000000000000000000 : ℚ)⟩
theorem b279 (b : ℝ) (hb : rootInterval.Contains b) : i279.Contains (n279 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b278 b hb) (b213 b hb))
    (by norm_num [i279, i278, i213, RationalInterval.add]) (by norm_num [i279, i278, i213, RationalInterval.add])

def n280 (b : ℝ) : ℝ := (n277 b) * (n241 b)
def i280 : RationalInterval := ⟨(-54473130696279977083725636689 / 1000000000000000000000000000000 : ℚ), (-54473130138137092586820356873 / 1000000000000000000000000000000 : ℚ)⟩
theorem b280 (b : ℝ) (hb : rootInterval.Contains b) : i280.Contains (n280 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b277 b hb) (b241 b hb))
    (by norm_num [i280, i277, i241, RationalInterval.mul]) (by norm_num [i280, i277, i241, RationalInterval.mul])

def n281 (b : ℝ) : ℝ := (n280 b) + (n279 b)
def i281 : RationalInterval := ⟨(-3904170634962924556124311946221 / 1000000000000000000000000000000 : ℚ), (-780834121643062963770769541339 / 200000000000000000000000000000 : ℚ)⟩
theorem b281 (b : ℝ) (hb : rootInterval.Contains b) : i281.Contains (n281 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b280 b hb) (b279 b hb))
    (by norm_num [i281, i280, i279, RationalInterval.add]) (by norm_num [i281, i280, i279, RationalInterval.add])

def n282 (b : ℝ) : ℝ := (n270 b) * (n281 b)
def i282 : RationalInterval := ⟨(-435091772579681039855177860821 / 100000000000000000000000000000 : ℚ), (-4350917688987362379256805642863 / 1000000000000000000000000000000 : ℚ)⟩
theorem b282 (b : ℝ) (hb : rootInterval.Contains b) : i282.Contains (n282 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b270 b hb) (b281 b hb))
    (by norm_num [i282, i270, i281, RationalInterval.mul]) (by norm_num [i282, i270, i281, RationalInterval.mul])

def n283 (b : ℝ) : ℝ := (n169 b) * (n241 b)
def i283 : RationalInterval := ⟨(41374526814052977122132701909 / 1000000000000000000000000000000 : ℚ), (10343631717305166050112340661 / 250000000000000000000000000000 : ℚ)⟩
theorem b283 (b : ℝ) (hb : rootInterval.Contains b) : i283.Contains (n283 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b169 b hb) (b241 b hb))
    (by norm_num [i283, i169, i241, RationalInterval.mul]) (by norm_num [i283, i169, i241, RationalInterval.mul])

def n284 (b : ℝ) : ℝ := -(n283 b)
def i284 : RationalInterval := ⟨(-10343631717305166050112340661 / 250000000000000000000000000000 : ℚ), (-41374526814052977122132701909 / 1000000000000000000000000000000 : ℚ)⟩
theorem b284 (b : ℝ) (hb : rootInterval.Contains b) : i284.Contains (n284 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b283 b hb))
    (by norm_num [i284, i283, RationalInterval.neg]) (by norm_num [i284, i283, RationalInterval.neg])

def n285 (b : ℝ) : ℝ := (n168 b) + (n284 b)
def i285 : RationalInterval := ⟨(-248497861058928475331395604463 / 1000000000000000000000000000000 : ℚ), (-24849785987159990719872810151 / 100000000000000000000000000000 : ℚ)⟩
theorem b285 (b : ℝ) (hb : rootInterval.Contains b) : i285.Contains (n285 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b168 b hb) (b284 b hb))
    (by norm_num [i285, i168, i284, RationalInterval.add]) (by norm_num [i285, i168, i284, RationalInterval.add])

def n286 (b : ℝ) : ℝ := -(n285 b)
def i286 : RationalInterval := ⟨(24849785987159990719872810151 / 100000000000000000000000000000 : ℚ), (248497861058928475331395604463 / 1000000000000000000000000000000 : ℚ)⟩
theorem b286 (b : ℝ) (hb : rootInterval.Contains b) : i286.Contains (n286 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b285 b hb))
    (by norm_num [i286, i285, RationalInterval.neg]) (by norm_num [i286, i285, RationalInterval.neg])

def n287 (b : ℝ) : ℝ := 1 / (n286 b)
def i287 : RationalInterval := ⟨(402417950697314548391314028453 / 100000000000000000000000000000 : ℚ), (4024179526200768990981077735383 / 1000000000000000000000000000000 : ℚ)⟩
theorem b287 (b : ℝ) (hb : rootInterval.Contains b) : i287.Contains (n287 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_inv_of_positive (b286 b hb) (by norm_num [i286]))
    (by norm_num [i287, i286, RationalInterval.inv]) (by norm_num [i287, i286, RationalInterval.inv])

def n288 (b : ℝ) : ℝ := (n169 b) * (n287 b)
def i288 : RationalInterval := ⟨(665994091663291589005248243327 / 200000000000000000000000000000 : ℚ), (166498523933361398463422407113 / 50000000000000000000000000000 : ℚ)⟩
theorem b288 (b : ℝ) (hb : rootInterval.Contains b) : i288.Contains (n288 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b169 b hb) (b287 b hb))
    (by norm_num [i288, i169, i287, RationalInterval.mul]) (by norm_num [i288, i169, i287, RationalInterval.mul])

def n289 (b : ℝ) : ℝ := (n239 b) * (n287 b)
def i289 : RationalInterval := ⟨(4395450857645449865174408428329 / 1000000000000000000000000000000 : ℚ), (2197725444912735239383607652787 / 500000000000000000000000000000 : ℚ)⟩
theorem b289 (b : ℝ) (hb : rootInterval.Contains b) : i289.Contains (n289 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b239 b hb) (b287 b hb))
    (by norm_num [i289, i239, i287, RationalInterval.mul]) (by norm_num [i289, i239, i287, RationalInterval.mul])

def n290 (b : ℝ) : ℝ := (n34 b) * (n241 b)
def i290 : RationalInterval := ⟨(-55150585917383268919778403931 / 1000000000000000000000000000000 : ℚ), (-55150585901292146476476646043 / 1000000000000000000000000000000 : ℚ)⟩
theorem b290 (b : ℝ) (hb : rootInterval.Contains b) : i290.Contains (n290 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b34 b hb) (b241 b hb))
    (by norm_num [i290, i34, i241, RationalInterval.mul]) (by norm_num [i290, i34, i241, RationalInterval.mul])

def n291 (b : ℝ) : ℝ := (n290 b) + (n56 b)
def i291 : RationalInterval := ⟨(494364617652014682117579892439 / 500000000000000000000000000000 : ℚ), (197745847139096742243032858201 / 200000000000000000000000000000 : ℚ)⟩
theorem b291 (b : ℝ) (hb : rootInterval.Contains b) : i291.Contains (n291 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b290 b hb) (b56 b hb))
    (by norm_num [i291, i290, i56, RationalInterval.add]) (by norm_num [i291, i290, i56, RationalInterval.add])

def n292 (b : ℝ) : ℝ := (n224 b) * (n241 b)
def i292 : RationalInterval := ⟨(2352605552940329803611141467 / 250000000000000000000000000000 : ℚ), (9410422266537580516633016941 / 1000000000000000000000000000000 : ℚ)⟩
theorem b292 (b : ℝ) (hb : rootInterval.Contains b) : i292.Contains (n292 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b224 b hb) (b241 b hb))
    (by norm_num [i292, i224, i241, RationalInterval.mul]) (by norm_num [i292, i224, i241, RationalInterval.mul])

def n293 (b : ℝ) : ℝ := (n292 b) + (n225 b)
def i293 : RationalInterval := ⟨(14129888364769090111765916663 / 250000000000000000000000000000 : ℚ), (14129888495688979117766838703 / 250000000000000000000000000000 : ℚ)⟩
theorem b293 (b : ℝ) (hb : rootInterval.Contains b) : i293.Contains (n293 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b292 b hb) (b225 b hb))
    (by norm_num [i293, i292, i225, RationalInterval.add]) (by norm_num [i293, i292, i225, RationalInterval.add])

def n294 (b : ℝ) : ℝ := (n226 b) * (n241 b)
def i294 : RationalInterval := ⟨(2355456562365752061630955039 / 1000000000000000000000000000000 : ℚ), (1177728292905458398860858447 / 500000000000000000000000000000 : ℚ)⟩
theorem b294 (b : ℝ) (hb : rootInterval.Contains b) : i294.Contains (n294 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b226 b hb) (b241 b hb))
    (by norm_num [i294, i226, i241, RationalInterval.mul]) (by norm_num [i294, i226, i241, RationalInterval.mul])

def n295 (b : ℝ) : ℝ := (n294 b) + (n227 b)
def i295 : RationalInterval := ⟨(3536752924081765278906616077 / 250000000000000000000000000000 : ℚ), (1768376485733951888974423609 / 125000000000000000000000000000 : ℚ)⟩
theorem b295 (b : ℝ) (hb : rootInterval.Contains b) : i295.Contains (n295 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b294 b hb) (b227 b hb))
    (by norm_num [i295, i294, i227, RationalInterval.add]) (by norm_num [i295, i294, i227, RationalInterval.add])

def n296 (b : ℝ) : ℝ := (n293 b) * (n241 b)
def i296 : RationalInterval := ⟨(706494418238454505588295833 / 250000000000000000000000000000 : ℚ), (2825977699137795823553367741 / 1000000000000000000000000000000 : ℚ)⟩
theorem b296 (b : ℝ) (hb : rootInterval.Contains b) : i296.Contains (n296 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b293 b hb) (b241 b hb))
    (by norm_num [i296, i293, i241, RationalInterval.mul]) (by norm_num [i296, i293, i241, RationalInterval.mul])

def n297 (b : ℝ) : ℝ := (n296 b) + (n295 b)
def i297 : RationalInterval := ⟨(424324734232021978449491191 / 25000000000000000000000000000 : ℚ), (16972989585009410935348756613 / 1000000000000000000000000000000 : ℚ)⟩
theorem b297 (b : ℝ) (hb : rootInterval.Contains b) : i297.Contains (n297 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b296 b hb) (b295 b hb))
    (by norm_num [i297, i296, i295, RationalInterval.add]) (by norm_num [i297, i296, i295, RationalInterval.add])

def n298 (b : ℝ) : ℝ := (n286 b) * (n297 b)
def i298 : RationalInterval := ⟨(4217751533889714794575920891 / 1000000000000000000000000000000 : ℚ), (2108875803825154340182218449 / 500000000000000000000000000000 : ℚ)⟩
theorem b298 (b : ℝ) (hb : rootInterval.Contains b) : i298.Contains (n298 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b286 b hb) (b297 b hb))
    (by norm_num [i298, i286, i297, RationalInterval.mul]) (by norm_num [i298, i286, i297, RationalInterval.mul])

def n299 (b : ℝ) : ℝ := (n170 b) * (n170 b)
def i299 : RationalInterval := ⟨(1086011151718444846032431699993 / 1000000000000000000000000000000 : ℚ), (67875697026567009093224837469 / 62500000000000000000000000000 : ℚ)⟩
theorem b299 (b : ℝ) (hb : rootInterval.Contains b) : i299.Contains (n299 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b170 b hb) (b170 b hb))
    (by norm_num [i299, i170, i170, RationalInterval.mul]) (by norm_num [i299, i170, i170, RationalInterval.mul])

def n300 (b : ℝ) : ℝ := (n171 b) * (n171 b)
def i300 : RationalInterval := ⟨(29153839174401310158197586233 / 15625000000000000000000000000 : ℚ), (1865845707583723240408464132531 / 1000000000000000000000000000000 : ℚ)⟩
theorem b300 (b : ℝ) (hb : rootInterval.Contains b) : i300.Contains (n300 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b171 b hb) (b171 b hb))
    (by norm_num [i300, i171, i171, RationalInterval.mul]) (by norm_num [i300, i171, i171, RationalInterval.mul])

def n301 (b : ℝ) : ℝ := (n299 b) + (n300 b)
def i301 : RationalInterval := ⟨(590371371776025739231415443781 / 200000000000000000000000000000 : ℚ), (590371372001759077180012306407 / 200000000000000000000000000000 : ℚ)⟩
theorem b301 (b : ℝ) (hb : rootInterval.Contains b) : i301.Contains (n301 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b299 b hb) (b300 b hb))
    (by norm_num [i301, i299, i300, RationalInterval.add]) (by norm_num [i301, i299, i300, RationalInterval.add])

def n302 (b : ℝ) : ℝ := -(n65 b)
def i302 : RationalInterval := ⟨(-28356207833 / 20000000000 : ℚ), (-35445259791 / 25000000000 : ℚ)⟩
theorem b302 (b : ℝ) (hb : rootInterval.Contains b) : i302.Contains (n302 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b65 b hb))
    (by norm_num [i302, i65, RationalInterval.neg]) (by norm_num [i302, i65, RationalInterval.neg])

def n303 (b : ℝ) : ℝ := -(n0 b)
def i303 : RationalInterval := ⟨(-18356207833 / 20000000000 : ℚ), (-22945259791 / 25000000000 : ℚ)⟩
theorem b303 (b : ℝ) (hb : rootInterval.Contains b) : i303.Contains (n303 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b0 b hb))
    (by norm_num [i303, i0, RationalInterval.neg]) (by norm_num [i303, i0, RationalInterval.neg])

def n304 (b : ℝ) : ℝ := (n90 b) * (n21 b)
def i304 : RationalInterval := ⟨(-58408052731896956947754656541 / 62500000000000000000000000000 : ℚ), (-116816105262889397288546096939 / 125000000000000000000000000000 : ℚ)⟩
theorem b304 (b : ℝ) (hb : rootInterval.Contains b) : i304.Contains (n304 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b90 b hb) (b21 b hb))
    (by norm_num [i304, i90, i21, RationalInterval.mul]) (by norm_num [i304, i90, i21, RationalInterval.mul])

def n305 (b : ℝ) : ℝ := (n91 b) * (n55 b)
def i305 : RationalInterval := ⟨(427731230281414927367743037 / 10000000000000000000000000000 : ℚ), (42773123441818478353122991901 / 1000000000000000000000000000000 : ℚ)⟩
theorem b305 (b : ℝ) (hb : rootInterval.Contains b) : i305.Contains (n305 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b91 b hb) (b55 b hb))
    (by norm_num [i305, i91, i55, RationalInterval.mul]) (by norm_num [i305, i91, i55, RationalInterval.mul])

def n306 (b : ℝ) : ℝ := (n304 b) + (n305 b)
def i306 : RationalInterval := ⟨(-222938930170552454606825050239 / 250000000000000000000000000000 : ℚ), (-891755718661296699955245783611 / 1000000000000000000000000000000 : ℚ)⟩
theorem b306 (b : ℝ) (hb : rootInterval.Contains b) : i306.Contains (n306 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b304 b hb) (b305 b hb))
    (by norm_num [i306, i304, i305, RationalInterval.add]) (by norm_num [i306, i304, i305, RationalInterval.add])

def n307 (b : ℝ) : ℝ := (n92 b) * (n21 b)
def i307 : RationalInterval := ⟨(-8580279024173035395492666481 / 15625000000000000000000000000 : ℚ), (-878620570458805022990225339 / 1600000000000000000000000000 : ℚ)⟩
theorem b307 (b : ℝ) (hb : rootInterval.Contains b) : i307.Contains (n307 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b92 b hb) (b21 b hb))
    (by norm_num [i307, i92, i21, RationalInterval.mul]) (by norm_num [i307, i92, i21, RationalInterval.mul])

def n308 (b : ℝ) : ℝ := (n93 b) * (n55 b)
def i308 : RationalInterval := ⟨(16314791784307506631338132763 / 500000000000000000000000000000 : ℚ), (32629583875438195368522847857 / 1000000000000000000000000000000 : ℚ)⟩
theorem b308 (b : ℝ) (hb : rootInterval.Contains b) : i308.Contains (n308 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b93 b hb) (b55 b hb))
    (by norm_num [i308, i93, i55, RationalInterval.mul]) (by norm_num [i308, i93, i55, RationalInterval.mul])

def n309 (b : ℝ) : ℝ := (n307 b) + (n308 b)
def i309 : RationalInterval := ⟨(-258254136989229626024427194629 / 500000000000000000000000000000 : ℚ), (-258254136330657472000183994509 / 500000000000000000000000000000 : ℚ)⟩
theorem b309 (b : ℝ) (hb : rootInterval.Contains b) : i309.Contains (n309 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b307 b hb) (b308 b hb))
    (by norm_num [i309, i307, i308, RationalInterval.add]) (by norm_num [i309, i307, i308, RationalInterval.add])

def n310 (b : ℝ) : ℝ := -(n306 b)
def i310 : RationalInterval := ⟨(891755718661296699955245783611 / 1000000000000000000000000000000 : ℚ), (222938930170552454606825050239 / 250000000000000000000000000000 : ℚ)⟩
theorem b310 (b : ℝ) (hb : rootInterval.Contains b) : i310.Contains (n310 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b306 b hb))
    (by norm_num [i310, i306, RationalInterval.neg]) (by norm_num [i310, i306, RationalInterval.neg])

def n311 (b : ℝ) : ℝ := -(n309 b)
def i311 : RationalInterval := ⟨(258254136330657472000183994509 / 500000000000000000000000000000 : ℚ), (258254136989229626024427194629 / 500000000000000000000000000000 : ℚ)⟩
theorem b311 (b : ℝ) (hb : rootInterval.Contains b) : i311.Contains (n311 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b309 b hb))
    (by norm_num [i311, i309, RationalInterval.neg]) (by norm_num [i311, i309, RationalInterval.neg])

def n312 (b : ℝ) : ℝ := (n118 b) * (n34 b)
def i312 : RationalInterval := ⟨(-2353131320018712550274146618497 / 1000000000000000000000000000000 : ℚ), (-58828282895799807373974258429 / 25000000000000000000000000000 : ℚ)⟩
theorem b312 (b : ℝ) (hb : rootInterval.Contains b) : i312.Contains (n312 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b118 b hb) (b34 b hb))
    (by norm_num [i312, i118, i34, RationalInterval.mul]) (by norm_num [i312, i118, i34, RationalInterval.mul])

def n313 (b : ℝ) : ℝ := (n119 b) * (n56 b)
def i313 : RationalInterval := ⟨(1103889393764985359329008226549 / 1000000000000000000000000000000 : ℚ), (220777879630351291342709418197 / 200000000000000000000000000000 : ℚ)⟩
theorem b313 (b : ℝ) (hb : rootInterval.Contains b) : i313.Contains (n313 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b119 b hb) (b56 b hb))
    (by norm_num [i313, i119, i56, RationalInterval.mul]) (by norm_num [i313, i119, i56, RationalInterval.mul])

def n314 (b : ℝ) : ℝ := (n312 b) + (n313 b)
def i314 : RationalInterval := ⟨(-312310481563431797736284597987 / 250000000000000000000000000000 : ℚ), (-49969676707209433529816929847 / 40000000000000000000000000000 : ℚ)⟩
theorem b314 (b : ℝ) (hb : rootInterval.Contains b) : i314.Contains (n314 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b312 b hb) (b313 b hb))
    (by norm_num [i314, i312, i313, RationalInterval.add]) (by norm_num [i314, i312, i313, RationalInterval.add])

def n315 (b : ℝ) : ℝ := (n120 b) * (n34 b)
def i315 : RationalInterval := ⟨(-291605153121443289269807690373 / 250000000000000000000000000000 : ℚ), (-72901288121655492966136988519 / 62500000000000000000000000000 : ℚ)⟩
theorem b315 (b : ℝ) (hb : rootInterval.Contains b) : i315.Contains (n315 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b120 b hb) (b34 b hb))
    (by norm_num [i315, i120, i34, RationalInterval.mul]) (by norm_num [i315, i120, i34, RationalInterval.mul])

def n316 (b : ℝ) : ℝ := (n121 b) * (n56 b)
def i316 : RationalInterval := ⟨(627951517797342275346339988583 / 1000000000000000000000000000000 : ℚ), (627951520748034972340751293349 / 1000000000000000000000000000000 : ℚ)⟩
theorem b316 (b : ℝ) (hb : rootInterval.Contains b) : i316.Contains (n316 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b121 b hb) (b56 b hb))
    (by norm_num [i316, i121, i56, RationalInterval.mul]) (by norm_num [i316, i121, i56, RationalInterval.mul])

def n317 (b : ℝ) : ℝ := (n315 b) + (n316 b)
def i317 : RationalInterval := ⟨(-538469094688430881732890772909 / 1000000000000000000000000000000 : ℚ), (-107693817839690583023488104591 / 200000000000000000000000000000 : ℚ)⟩
theorem b317 (b : ℝ) (hb : rootInterval.Contains b) : i317.Contains (n317 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b315 b hb) (b316 b hb))
    (by norm_num [i317, i315, i316, RationalInterval.add]) (by norm_num [i317, i315, i316, RationalInterval.add])

def n318 (b : ℝ) : ℝ := -(n314 b)
def i318 : RationalInterval := ⟨(49969676707209433529816929847 / 40000000000000000000000000000 : ℚ), (312310481563431797736284597987 / 250000000000000000000000000000 : ℚ)⟩
theorem b318 (b : ℝ) (hb : rootInterval.Contains b) : i318.Contains (n318 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b314 b hb))
    (by norm_num [i318, i314, RationalInterval.neg]) (by norm_num [i318, i314, RationalInterval.neg])

def n319 (b : ℝ) : ℝ := -(n317 b)
def i319 : RationalInterval := ⟨(107693817839690583023488104591 / 200000000000000000000000000000 : ℚ), (538469094688430881732890772909 / 1000000000000000000000000000000 : ℚ)⟩
theorem b319 (b : ℝ) (hb : rootInterval.Contains b) : i319.Contains (n319 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b317 b hb))
    (by norm_num [i319, i317, RationalInterval.neg]) (by norm_num [i319, i317, RationalInterval.neg])

def n320 (b : ℝ) : ℝ := (n55 b) + (n16 b)
def i320 : RationalInterval := ⟨(-459345363357437601907605699171 / 500000000000000000000000000000 : ℚ), (-183738145230645263163123798323 / 200000000000000000000000000000 : ℚ)⟩
theorem b320 (b : ℝ) (hb : rootInterval.Contains b) : i320.Contains (n320 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b55 b hb) (b16 b hb))
    (by norm_num [i320, i55, i16, RationalInterval.add]) (by norm_num [i320, i55, i16, RationalInterval.add])

def n321 (b : ℝ) : ℝ := (n302 b) * (n21 b)
def i321 : RationalInterval := ⟨(59200946326040969142697862491 / 40000000000000000000000000000 : ℚ), (11562684833544194587273828921 / 7812500000000000000000000000 : ℚ)⟩
theorem b321 (b : ℝ) (hb : rootInterval.Contains b) : i321.Contains (n321 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b302 b hb) (b21 b hb))
    (by norm_num [i321, i302, i21, RationalInterval.mul]) (by norm_num [i321, i302, i21, RationalInterval.mul])

def n322 (b : ℝ) : ℝ := (n303 b) * (n320 b)
def i322 : RationalInterval := ⟨(843183895166728635568287592723 / 1000000000000000000000000000000 : ℚ), (42159194784570136434725637387 / 50000000000000000000000000000 : ℚ)⟩
theorem b322 (b : ℝ) (hb : rootInterval.Contains b) : i322.Contains (n322 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b303 b hb) (b320 b hb))
    (by norm_num [i322, i303, i320, RationalInterval.mul]) (by norm_num [i322, i303, i320, RationalInterval.mul])

def n323 (b : ℝ) : ℝ := (n321 b) + (n322 b)
def i323 : RationalInterval := ⟨(1161603776658876432067867077499 / 500000000000000000000000000000 : ℚ), (580801888596264908966390712407 / 250000000000000000000000000000 : ℚ)⟩
theorem b323 (b : ℝ) (hb : rootInterval.Contains b) : i323.Contains (n323 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b321 b hb) (b322 b hb))
    (by norm_num [i323, i321, i322, RationalInterval.add]) (by norm_num [i323, i321, i322, RationalInterval.add])

def n324 (b : ℝ) : ℝ := -(n55 b)
def i324 : RationalInterval := ⟨(-16261854769354736836876201677 / 200000000000000000000000000000 : ℚ), (-40654636642562398092394300829 / 500000000000000000000000000000 : ℚ)⟩
theorem b324 (b : ℝ) (hb : rootInterval.Contains b) : i324.Contains (n324 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b55 b hb))
    (by norm_num [i324, i55, RationalInterval.neg]) (by norm_num [i324, i55, RationalInterval.neg])

def n325 (b : ℝ) : ℝ := (n34 b) + (n56 b)
def i325 : RationalInterval := ⟨(-29565948563126372620314944899 / 500000000000000000000000000000 : ℚ), (-59131896429067071837891983821 / 1000000000000000000000000000000 : ℚ)⟩
theorem b325 (b : ℝ) (hb : rootInterval.Contains b) : i325.Contains (n325 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b34 b hb) (b56 b hb))
    (by norm_num [i325, i34, i56, RationalInterval.add]) (by norm_num [i325, i34, i56, RationalInterval.add])

def n326 (b : ℝ) : ℝ := (n56 b) + (n324 b)
def i326 : RationalInterval := ⟨(120321318421829868621319647553 / 125000000000000000000000000000 : ℚ), (96257054831165106150685233539 / 100000000000000000000000000000 : ℚ)⟩
theorem b326 (b : ℝ) (hb : rootInterval.Contains b) : i326.Contains (n326 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b56 b hb) (b324 b hb))
    (by norm_num [i326, i56, i324, RationalInterval.add]) (by norm_num [i326, i56, i324, RationalInterval.add])

def n327 (b : ℝ) : ℝ := (n310 b) * (n325 b)
def i327 : RationalInterval := ⟨(-13182801884281952133949290127 / 250000000000000000000000000000 : ℚ), (-10546241359181614137518876527 / 200000000000000000000000000000 : ℚ)⟩
theorem b327 (b : ℝ) (hb : rootInterval.Contains b) : i327.Contains (n327 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b310 b hb) (b325 b hb))
    (by norm_num [i327, i310, i325, RationalInterval.mul]) (by norm_num [i327, i310, i325, RationalInterval.mul])

def n328 (b : ℝ) : ℝ := (n311 b) * (n326 b)
def i328 : RationalInterval := ⟨(497175650739131187790141587087 / 1000000000000000000000000000000 : ℚ), (497175652490950014302794834201 / 1000000000000000000000000000000 : ℚ)⟩
theorem b328 (b : ℝ) (hb : rootInterval.Contains b) : i328.Contains (n328 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b311 b hb) (b326 b hb))
    (by norm_num [i328, i311, i326, RationalInterval.mul]) (by norm_num [i328, i311, i326, RationalInterval.mul])

def n329 (b : ℝ) : ℝ := (n327 b) + (n328 b)
def i329 : RationalInterval := ⟨(444444443202003379254344426579 / 1000000000000000000000000000000 : ℚ), (222222222847520971807600225783 / 500000000000000000000000000000 : ℚ)⟩
theorem b329 (b : ℝ) (hb : rootInterval.Contains b) : i329.Contains (n329 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b327 b hb) (b328 b hb))
    (by norm_num [i329, i327, i328, RationalInterval.add]) (by norm_num [i329, i327, i328, RationalInterval.add])

def n330 (b : ℝ) : ℝ := -(n34 b)
def i330 : RationalInterval := ⟨(1103011718025842929529532920869 / 1000000000000000000000000000000 : ℚ), (1103011718347665378395568078607 / 1000000000000000000000000000000 : ℚ)⟩
theorem b330 (b : ℝ) (hb : rootInterval.Contains b) : i330.Contains (n330 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b34 b hb))
    (by norm_num [i330, i34, RationalInterval.neg]) (by norm_num [i330, i34, RationalInterval.neg])

def n331 (b : ℝ) : ℝ := -(n56 b)
def i331 : RationalInterval := ⟨(-130484977699596982211455117131 / 125000000000000000000000000000 : ℚ), (-1043879821221412633154938188809 / 1000000000000000000000000000000 : ℚ)⟩
theorem b331 (b : ℝ) (hb : rootInterval.Contains b) : i331.Contains (n331 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b56 b hb))
    (by norm_num [i331, i56, RationalInterval.neg]) (by norm_num [i331, i56, RationalInterval.neg])

def n332 (b : ℝ) : ℝ := (n330 b) + (n15 b)
def i332 : RationalInterval := ⟨(2103011718025842929529532920869 / 1000000000000000000000000000000 : ℚ), (2103011718347665378395568078607 / 1000000000000000000000000000000 : ℚ)⟩
theorem b332 (b : ℝ) (hb : rootInterval.Contains b) : i332.Contains (n332 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b330 b hb) (b15 b hb))
    (by norm_num [i332, i330, i15, RationalInterval.add]) (by norm_num [i332, i330, i15, RationalInterval.add])

def n333 (b : ℝ) : ℝ := (n318 b) * (n332 b)
def i333 : RationalInterval := ⟨(2627170391530611415677626547587 / 1000000000000000000000000000000 : ℚ), (2627170409962798290731459949631 / 1000000000000000000000000000000 : ℚ)⟩
theorem b333 (b : ℝ) (hb : rootInterval.Contains b) : i333.Contains (n333 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b318 b hb) (b332 b hb))
    (by norm_num [i333, i318, i332, RationalInterval.mul]) (by norm_num [i333, i318, i332, RationalInterval.mul])

def n334 (b : ℝ) : ℝ := (n319 b) * (n331 b)
def i334 : RationalInterval := ⟨(-56209702249873663541733194649 / 100000000000000000000000000000 : ℚ), (-562097016565737921421692751953 / 1000000000000000000000000000000 : ℚ)⟩
theorem b334 (b : ℝ) (hb : rootInterval.Contains b) : i334.Contains (n334 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b319 b hb) (b331 b hb))
    (by norm_num [i334, i319, i331, RationalInterval.mul]) (by norm_num [i334, i319, i331, RationalInterval.mul])

def n335 (b : ℝ) : ℝ := (n333 b) + (n334 b)
def i335 : RationalInterval := ⟨(2065073369031874780260294601097 / 1000000000000000000000000000000 : ℚ), (1032536696698530184654883598839 / 500000000000000000000000000000 : ℚ)⟩
theorem b335 (b : ℝ) (hb : rootInterval.Contains b) : i335.Contains (n335 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b333 b hb) (b334 b hb))
    (by norm_num [i335, i333, i334, RationalInterval.add]) (by norm_num [i335, i333, i334, RationalInterval.add])

def n336 (b : ℝ) : ℝ := ((3 / 100 : ℚ) : ℝ)
def i336 : RationalInterval := ⟨(3 / 100 : ℚ), (3 / 100 : ℚ)⟩
theorem b336 (b : ℝ) (hb : rootInterval.Contains b) : i336.Contains (n336 b) := by
  exact RationalInterval.contains_point (3 / 100 : ℚ)

def n337 (b : ℝ) : ℝ := ((-3 / 100 : ℚ) : ℝ)
def i337 : RationalInterval := ⟨(-3 / 100 : ℚ), (-3 / 100 : ℚ)⟩
theorem b337 (b : ℝ) (hb : rootInterval.Contains b) : i337.Contains (n337 b) := by
  exact RationalInterval.contains_point (-3 / 100 : ℚ)

def n338 (b : ℝ) : ℝ := (n136 b) + (n337 b)
def i338 : RationalInterval := ⟨(1288931338097404270889750892089 / 1000000000000000000000000000000 : ℚ), (644465669263247098446750366451 / 500000000000000000000000000000 : ℚ)⟩
theorem b338 (b : ℝ) (hb : rootInterval.Contains b) : i338.Contains (n338 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b136 b hb) (b337 b hb))
    (by norm_num [i338, i136, i337, RationalInterval.add]) (by norm_num [i338, i136, i337, RationalInterval.add])

def n339 (b : ℝ) : ℝ := (n338 b) + (n186 b)
def i339 : RationalInterval := ⟨(30069341431957252497373607809 / 500000000000000000000000000000 : ℚ), (60138683488523973481997203491 / 1000000000000000000000000000000 : ℚ)⟩
theorem b339 (b : ℝ) (hb : rootInterval.Contains b) : i339.Contains (n339 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b338 b hb) (b186 b hb))
    (by norm_num [i339, i338, i186, RationalInterval.add]) (by norm_num [i339, i338, i186, RationalInterval.add])

def n340 (b : ℝ) : ℝ := (n303 b) * (n336 b)
def i340 : RationalInterval := ⟨(-55068623499 / 2000000000000 : ℚ), (-68835779373 / 2500000000000 : ℚ)⟩
theorem b340 (b : ℝ) (hb : rootInterval.Contains b) : i340.Contains (n340 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b303 b hb) (b336 b hb))
    (by norm_num [i340, i303, i336, RationalInterval.mul]) (by norm_num [i340, i303, i336, RationalInterval.mul])

def n341 (b : ℝ) : ℝ := (n153 b) + (n340 b)
def i341 : RationalInterval := ⟨(1201258343288470223411503529411 / 1000000000000000000000000000000 : ℚ), (1201258343484289765895003676471 / 1000000000000000000000000000000 : ℚ)⟩
theorem b341 (b : ℝ) (hb : rootInterval.Contains b) : i341.Contains (n341 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b153 b hb) (b340 b hb))
    (by norm_num [i341, i153, i340, RationalInterval.add]) (by norm_num [i341, i153, i340, RationalInterval.add])

def n342 (b : ℝ) : ℝ := -(n236 b)
def i342 : RationalInterval := ⟨(-234476682618083614015308858231 / 200000000000000000000000000000 : ℚ), (-586191705293013617134882196581 / 500000000000000000000000000000 : ℚ)⟩
theorem b342 (b : ℝ) (hb : rootInterval.Contains b) : i342.Contains (n342 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b236 b hb))
    (by norm_num [i342, i236, RationalInterval.neg]) (by norm_num [i342, i236, RationalInterval.neg])

def n343 (b : ℝ) : ℝ := (n341 b) + (n342 b)
def i343 : RationalInterval := ⟨(1804683137378259583434952391 / 62500000000000000000000000000 : ℚ), (28874932898262531625239283309 / 1000000000000000000000000000000 : ℚ)⟩
theorem b343 (b : ℝ) (hb : rootInterval.Contains b) : i343.Contains (n343 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b341 b hb) (b342 b hb))
    (by norm_num [i343, i341, i342, RationalInterval.add]) (by norm_num [i343, i341, i342, RationalInterval.add])

def n344 (b : ℝ) : ℝ := (n21 b) * (n310 b)
def i344 : RationalInterval := ⟨(-232721450653412367051471446651 / 250000000000000000000000000000 : ℚ), (-930885800169326740576944630047 / 1000000000000000000000000000000 : ℚ)⟩
theorem b344 (b : ℝ) (hb : rootInterval.Contains b) : i344.Contains (n344 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b21 b hb) (b310 b hb))
    (by norm_num [i344, i21, i310, RationalInterval.mul]) (by norm_num [i344, i21, i310, RationalInterval.mul])

def n345 (b : ℝ) : ℝ := (n55 b) * (n311 b)
def i345 : RationalInterval := ⟨(41996912295846609291020274869 / 1000000000000000000000000000000 : ℚ), (41996912693038953512671704771 / 1000000000000000000000000000000 : ℚ)⟩
theorem b345 (b : ℝ) (hb : rootInterval.Contains b) : i345.Contains (n345 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b55 b hb) (b311 b hb))
    (by norm_num [i345, i55, i311, RationalInterval.mul]) (by norm_num [i345, i55, i311, RationalInterval.mul])

def n346 (b : ℝ) : ℝ := (n344 b) + (n345 b)
def i346 : RationalInterval := ⟨(-177777778063560571782973102347 / 200000000000000000000000000000 : ℚ), (-222222221869071946766068231319 / 250000000000000000000000000000 : ℚ)⟩
theorem b346 (b : ℝ) (hb : rootInterval.Contains b) : i346.Contains (n346 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b344 b hb) (b345 b hb))
    (by norm_num [i346, i344, i345, RationalInterval.add]) (by norm_num [i346, i344, i345, RationalInterval.add])

def n347 (b : ℝ) : ℝ := (n346 b) * (n336 b)
def i347 : RationalInterval := ⟨(-26666666709534085767445965353 / 1000000000000000000000000000000 : ℚ), (-13333333312144316805964093879 / 500000000000000000000000000000 : ℚ)⟩
theorem b347 (b : ℝ) (hb : rootInterval.Contains b) : i347.Contains (n347 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b346 b hb) (b336 b hb))
    (by norm_num [i347, i346, i336, RationalInterval.mul]) (by norm_num [i347, i346, i336, RationalInterval.mul])

def n348 (b : ℝ) : ℝ := (n236 b) + (n347 b)
def i348 : RationalInterval := ⟨(1145716743876493148502318427809 / 1000000000000000000000000000000 : ℚ), (1145716746466129436464616103397 / 1000000000000000000000000000000 : ℚ)⟩
theorem b348 (b : ℝ) (hb : rootInterval.Contains b) : i348.Contains (n348 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b236 b hb) (b347 b hb))
    (by norm_num [i348, i236, i347, RationalInterval.add]) (by norm_num [i348, i236, i347, RationalInterval.add])

def n349 (b : ℝ) : ℝ := -(n239 b)
def i349 : RationalInterval := ⟨(-1092260139292348885309804888967 / 1000000000000000000000000000000 : ℚ), (-1092260136514527005313700431481 / 1000000000000000000000000000000 : ℚ)⟩
theorem b349 (b : ℝ) (hb : rootInterval.Contains b) : i349.Contains (n349 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b239 b hb))
    (by norm_num [i349, i239, RationalInterval.neg]) (by norm_num [i349, i239, RationalInterval.neg])

def n350 (b : ℝ) : ℝ := (n348 b) + (n349 b)
def i350 : RationalInterval := ⟨(26728302292072131596256769421 / 500000000000000000000000000000 : ℚ), (13364152487900607787728917979 / 250000000000000000000000000000 : ℚ)⟩
theorem b350 (b : ℝ) (hb : rootInterval.Contains b) : i350.Contains (n350 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b348 b hb) (b349 b hb))
    (by norm_num [i350, i348, i349, RationalInterval.add]) (by norm_num [i350, i348, i349, RationalInterval.add])

def n351 (b : ℝ) : ℝ := (n34 b) * (n318 b)
def i351 : RationalInterval := ⟨(-1377928483709071099786321557683 / 1000000000000000000000000000000 : ℚ), (-344482118462593894358050825353 / 250000000000000000000000000000 : ℚ)⟩
theorem b351 (b : ℝ) (hb : rootInterval.Contains b) : i351.Contains (n351 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b34 b hb) (b318 b hb))
    (by norm_num [i351, i34, i318, RationalInterval.mul]) (by norm_num [i351, i34, i318, RationalInterval.mul])

def n352 (b : ℝ) : ℝ := (n56 b) * (n319 b)
def i352 : RationalInterval := ⟨(562097016565737921421692751953 / 1000000000000000000000000000000 : ℚ), (56209702249873663541733194649 / 100000000000000000000000000000 : ℚ)⟩
theorem b352 (b : ℝ) (hb : rootInterval.Contains b) : i352.Contains (n352 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b56 b hb) (b319 b hb))
    (by norm_num [i352, i56, i319, RationalInterval.mul]) (by norm_num [i352, i56, i319, RationalInterval.mul])

def n353 (b : ℝ) : ℝ := (n351 b) + (n352 b)
def i353 : RationalInterval := ⟨(-81583146714333317836462880573 / 100000000000000000000000000000 : ℚ), (-407915725675819471007435677461 / 500000000000000000000000000000 : ℚ)⟩
theorem b353 (b : ℝ) (hb : rootInterval.Contains b) : i353.Contains (n353 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b351 b hb) (b352 b hb))
    (by norm_num [i353, i351, i352, RationalInterval.add]) (by norm_num [i353, i351, i352, RationalInterval.add])

def n354 (b : ℝ) : ℝ := (n353 b) * (n336 b)
def i354 : RationalInterval := ⟨(-6118736003574998837734716043 / 250000000000000000000000000000 : ℚ), (-24474943540549168260446140647 / 1000000000000000000000000000000 : ℚ)⟩
theorem b354 (b : ℝ) (hb : rootInterval.Contains b) : i354.Contains (n354 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b353 b hb) (b336 b hb))
    (by norm_num [i354, i353, i336, RationalInterval.mul]) (by norm_num [i354, i353, i336, RationalInterval.mul])

def n355 (b : ℝ) : ℝ := (n239 b) + (n354 b)
def i355 : RationalInterval := ⟨(1067785192500227009962761567309 / 1000000000000000000000000000000 : ℚ), (6673657473448748231558492177 / 6250000000000000000000000000 : ℚ)⟩
theorem b355 (b : ℝ) (hb : rootInterval.Contains b) : i355.Contains (n355 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b239 b hb) (b354 b hb))
    (by norm_num [i355, i239, i354, RationalInterval.add]) (by norm_num [i355, i239, i354, RationalInterval.add])

def n356 (b : ℝ) : ℝ := -(n170 b)
def i356 : RationalInterval := ⟨(-521059294232689065439407696949 / 500000000000000000000000000000 : ℚ), (-1042118588126344115270914285107 / 1000000000000000000000000000000 : ℚ)⟩
theorem b356 (b : ℝ) (hb : rootInterval.Contains b) : i356.Contains (n356 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b170 b hb))
    (by norm_num [i356, i170, RationalInterval.neg]) (by norm_num [i356, i170, RationalInterval.neg])

def n357 (b : ℝ) : ℝ := (n355 b) + (n356 b)
def i357 : RationalInterval := ⟨(25666604034848879083946173411 / 1000000000000000000000000000000 : ℚ), (25666607625455601778444463213 / 1000000000000000000000000000000 : ℚ)⟩
theorem b357 (b : ℝ) (hb : rootInterval.Contains b) : i357.Contains (n357 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b355 b hb) (b356 b hb))
    (by norm_num [i357, i355, i356, RationalInterval.add]) (by norm_num [i357, i355, i356, RationalInterval.add])

def n358 (b : ℝ) : ℝ := ((3 / 5 : ℚ) : ℝ)
def i358 : RationalInterval := ⟨(3 / 5 : ℚ), (3 / 5 : ℚ)⟩
theorem b358 (b : ℝ) (hb : rootInterval.Contains b) : i358.Contains (n358 b) := by
  exact RationalInterval.contains_point (3 / 5 : ℚ)

def n359 (b : ℝ) : ℝ := ((1 / 10 : ℚ) : ℝ)
def i359 : RationalInterval := ⟨(1 / 10 : ℚ), (1 / 10 : ℚ)⟩
theorem b359 (b : ℝ) (hb : rootInterval.Contains b) : i359.Contains (n359 b) := by
  exact RationalInterval.contains_point (1 / 10 : ℚ)

