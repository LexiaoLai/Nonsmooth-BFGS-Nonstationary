import BFGS.Counterexample.Certificates.IntervalTrace0

/-! Generated arithmetic proofs. Each bound is checked by the Lean kernel. -/
namespace BFGS.Counterexample.Trace
noncomputable section
open BFGS RationalInterval
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false

def n90 (b : ℝ) : ℝ := (n79 b) * (n89 b)
def i90 : RationalInterval := ⟨(11190570302068523357123277409 / 12500000000000000000000000000 : ℚ), (895245625383240677885755943207 / 1000000000000000000000000000000 : ℚ)⟩
theorem b90 (b : ℝ) (hb : rootInterval.Contains b) : i90.Contains (n90 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b79 b hb) (b89 b hb))
    (by norm_num [i90, i79, i89, RationalInterval.mul]) (by norm_num [i90, i79, i89, RationalInterval.mul])

def n91 (b : ℝ) : ℝ := (n82 b) * (n89 b)
def i91 : RationalInterval := ⟨(526054671256872039829979695539 / 1000000000000000000000000000000 : ℚ), (526054672710813993618886112347 / 1000000000000000000000000000000 : ℚ)⟩
theorem b91 (b : ℝ) (hb : rootInterval.Contains b) : i91.Contains (n91 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b82 b hb) (b89 b hb))
    (by norm_num [i91, i82, i89, RationalInterval.mul]) (by norm_num [i91, i82, i89, RationalInterval.mul])

def n92 (b : ℝ) : ℝ := (n85 b) * (n89 b)
def i92 : RationalInterval := ⟨(526054671594497647969858444361 / 1000000000000000000000000000000 : ℚ), (263027336186594192730029784573 / 500000000000000000000000000000 : ℚ)⟩
theorem b92 (b : ℝ) (hb : rootInterval.Contains b) : i92.Contains (n92 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b85 b hb) (b89 b hb))
    (by norm_num [i92, i85, i89, RationalInterval.mul]) (by norm_num [i92, i85, i89, RationalInterval.mul])

def n93 (b : ℝ) : ℝ := (n88 b) * (n89 b)
def i93 : RationalInterval := ⟨(200651058915468526619382751933 / 500000000000000000000000000000 : ℚ), (200651059416225021061071703383 / 500000000000000000000000000000 : ℚ)⟩
theorem b93 (b : ℝ) (hb : rootInterval.Contains b) : i93.Contains (n93 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b88 b hb) (b89 b hb))
    (by norm_num [i93, i88, i89, RationalInterval.mul]) (by norm_num [i93, i88, i89, RationalInterval.mul])

def n94 (b : ℝ) : ℝ := (n21 b) * (n63 b)
def i94 : RationalInterval := ⟨(-315487935036304095607836379867 / 125000000000000000000000000000 : ℚ), (-630975869843109215430596187771 / 250000000000000000000000000000 : ℚ)⟩
theorem b94 (b : ℝ) (hb : rootInterval.Contains b) : i94.Contains (n94 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b21 b hb) (b63 b hb))
    (by norm_num [i94, i21, i63, RationalInterval.mul]) (by norm_num [i94, i21, i63, RationalInterval.mul])

def n95 (b : ℝ) : ℝ := (n55 b) * (n65 b)
def i95 : RationalInterval := ⟨(115281132600346576665030305127 / 1000000000000000000000000000000 : ℚ), (14410141674683912407796331039 / 125000000000000000000000000000 : ℚ)⟩
theorem b95 (b : ℝ) (hb : rootInterval.Contains b) : i95.Contains (n95 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b55 b hb) (b65 b hb))
    (by norm_num [i95, i55, i65, RationalInterval.mul]) (by norm_num [i95, i55, i65, RationalInterval.mul])

def n96 (b : ℝ) : ℝ := (n94 b) + (n95 b)
def i96 : RationalInterval := ⟨(-2408622347690086188197660733809 / 1000000000000000000000000000000 : ℚ), (-602155586493741390615003525693 / 250000000000000000000000000000 : ℚ)⟩
theorem b96 (b : ℝ) (hb : rootInterval.Contains b) : i96.Contains (n96 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b94 b hb) (b95 b hb))
    (by norm_num [i96, i94, i95, RationalInterval.add]) (by norm_num [i96, i94, i95, RationalInterval.add])

def n97 (b : ℝ) : ℝ := (n21 b) * (n65 b)
def i97 : RationalInterval := ⟨(-11562684833544194587273828921 / 7812500000000000000000000000 : ℚ), (-59200946326040969142697862491 / 40000000000000000000000000000 : ℚ)⟩
theorem b97 (b : ℝ) (hb : rootInterval.Contains b) : i97.Contains (n97 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b21 b hb) (b65 b hb))
    (by norm_num [i97, i21, i65, RationalInterval.mul]) (by norm_num [i97, i21, i65, RationalInterval.mul])

def n98 (b : ℝ) : ℝ := (n55 b) * (n0 b)
def i98 : RationalInterval := ⟨(37313247978892089286318002149 / 500000000000000000000000000000 : ℚ), (74626496474084457170180144119 / 1000000000000000000000000000000 : ℚ)⟩
theorem b98 (b : ℝ) (hb : rootInterval.Contains b) : i98.Contains (n98 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b55 b hb) (b0 b hb))
    (by norm_num [i98, i55, i0, RationalInterval.mul]) (by norm_num [i98, i55, i0, RationalInterval.mul])

def n99 (b : ℝ) : ℝ := (n97 b) + (n98 b)
def i99 : RationalInterval := ⟨(-140539716273587272859841409759 / 100000000000000000000000000000 : ℚ), (-351349290419234942849316604539 / 250000000000000000000000000000 : ℚ)⟩
theorem b99 (b : ℝ) (hb : rootInterval.Contains b) : i99.Contains (n99 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b97 b hb) (b98 b hb))
    (by norm_num [i99, i97, i98, RationalInterval.add]) (by norm_num [i99, i97, i98, RationalInterval.add])

def n100 (b : ℝ) : ℝ := (n34 b) * (n63 b)
def i100 : RationalInterval := ⟨(-1333436597366354159700866952381 / 500000000000000000000000000000 : ℚ), (-83339787310736641908966403511 / 31250000000000000000000000000 : ℚ)⟩
theorem b100 (b : ℝ) (hb : rootInterval.Contains b) : i100.Contains (n100 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b34 b hb) (b63 b hb))
    (by norm_num [i100, i34, i63, RationalInterval.mul]) (by norm_num [i100, i34, i63, RationalInterval.mul])

def n101 (b : ℝ) : ℝ := (n56 b) * (n65 b)
def i101 : RationalInterval := ⟨(59200946326040969142697862491 / 40000000000000000000000000000 : ℚ), (11562684833544194587273828921 / 7812500000000000000000000000 : ℚ)⟩
theorem b101 (b : ℝ) (hb : rootInterval.Contains b) : i101.Contains (n101 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b56 b hb) (b65 b hb))
    (by norm_num [i101, i56, i65, RationalInterval.mul]) (by norm_num [i101, i56, i65, RationalInterval.mul])

def n102 (b : ℝ) : ℝ := (n100 b) + (n101 b)
def i102 : RationalInterval := ⟨(-1186849536581684090834287342487 / 1000000000000000000000000000000 : ℚ), (-37089047976559863559871087827 / 31250000000000000000000000000 : ℚ)⟩
theorem b102 (b : ℝ) (hb : rootInterval.Contains b) : i102.Contains (n102 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b100 b hb) (b101 b hb))
    (by norm_num [i102, i100, i101, RationalInterval.add]) (by norm_num [i102, i100, i101, RationalInterval.add])

def n103 (b : ℝ) : ℝ := (n34 b) * (n65 b)
def i103 : RationalInterval := ⟨(-312772295277008588201233165231 / 200000000000000000000000000000 : ℚ), (-1563861475917729611557391991483 / 1000000000000000000000000000000 : ℚ)⟩
theorem b103 (b : ℝ) (hb : rootInterval.Contains b) : i103.Contains (n103 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b34 b hb) (b65 b hb))
    (by norm_num [i103, i34, i65, RationalInterval.mul]) (by norm_num [i103, i34, i65, RationalInterval.mul])

def n104 (b : ℝ) : ℝ := (n56 b) * (n0 b)
def i104 : RationalInterval := ⟨(95808374754031791198997746787 / 100000000000000000000000000000 : ℚ), (239520936973817244581307408341 / 250000000000000000000000000000 : ℚ)⟩
theorem b104 (b : ℝ) (hb : rootInterval.Contains b) : i104.Contains (n104 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b56 b hb) (b0 b hb))
    (by norm_num [i104, i56, i0, RationalInterval.mul]) (by norm_num [i104, i56, i0, RationalInterval.mul])

def n105 (b : ℝ) : ℝ := (n103 b) + (n104 b)
def i105 : RationalInterval := ⟨(-121155545768945005803237671657 / 200000000000000000000000000000 : ℚ), (-605777728022460633232162358119 / 1000000000000000000000000000000 : ℚ)⟩
theorem b105 (b : ℝ) (hb : rootInterval.Contains b) : i105.Contains (n105 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b103 b hb) (b104 b hb))
    (by norm_num [i105, i103, i104, RationalInterval.add]) (by norm_num [i105, i103, i104, RationalInterval.add])

def n106 (b : ℝ) : ℝ := (n96 b) * (n21 b)
def i106 : RationalInterval := ⟨(2514312263906246537720065502337 / 1000000000000000000000000000000 : ℚ), (314289033325091825126043921543 / 125000000000000000000000000000 : ℚ)⟩
theorem b106 (b : ℝ) (hb : rootInterval.Contains b) : i106.Contains (n106 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b96 b hb) (b21 b hb))
    (by norm_num [i106, i96, i21, RationalInterval.mul]) (by norm_num [i106, i96, i21, RationalInterval.mul])

def n107 (b : ℝ) : ℝ := (n99 b) * (n55 b)
def i107 : RationalInterval := ⟨(-57135911384184917907497187313 / 500000000000000000000000000000 : ℚ), (-114271821892929012958915773151 / 1000000000000000000000000000000 : ℚ)⟩
theorem b107 (b : ℝ) (hb : rootInterval.Contains b) : i107.Contains (n107 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b99 b hb) (b55 b hb))
    (by norm_num [i107, i99, i55, RationalInterval.mul]) (by norm_num [i107, i99, i55, RationalInterval.mul])

def n108 (b : ℝ) : ℝ := (n106 b) + (n107 b)
def i108 : RationalInterval := ⟨(2400040441137876701905071127711 / 1000000000000000000000000000000 : ℚ), (2400040444707805588049435599193 / 1000000000000000000000000000000 : ℚ)⟩
theorem b108 (b : ℝ) (hb : rootInterval.Contains b) : i108.Contains (n108 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b106 b hb) (b107 b hb))
    (by norm_num [i108, i106, i107, RationalInterval.add]) (by norm_num [i108, i106, i107, RationalInterval.add])

def n109 (b : ℝ) : ℝ := (n96 b) * (n34 b)
def i109 : RationalInterval := ⟨(531347734381856601518029151749 / 200000000000000000000000000000 : ℚ), (1328369337288114948966834222609 / 500000000000000000000000000000 : ℚ)⟩
theorem b109 (b : ℝ) (hb : rootInterval.Contains b) : i109.Contains (n109 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b96 b hb) (b34 b hb))
    (by norm_num [i109, i96, i34, RationalInterval.mul]) (by norm_num [i109, i96, i34, RationalInterval.mul])

def n110 (b : ℝ) : ℝ := (n99 b) * (n56 b)
def i110 : RationalInterval := ⟨(-91691608719333611962324575743 / 62500000000000000000000000000 : ℚ), (-1467065737876404634589327009429 / 1000000000000000000000000000000 : ℚ)⟩
theorem b110 (b : ℝ) (hb : rootInterval.Contains b) : i110.Contains (n110 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b99 b hb) (b56 b hb))
    (by norm_num [i110, i99, i56, RationalInterval.mul]) (by norm_num [i110, i99, i56, RationalInterval.mul])

def n111 (b : ℝ) : ℝ := (n109 b) + (n110 b)
def i111 : RationalInterval := ⟨(1189672932399945216192952546857 / 1000000000000000000000000000000 : ℚ), (1189672936699825263344341435789 / 1000000000000000000000000000000 : ℚ)⟩
theorem b111 (b : ℝ) (hb : rootInterval.Contains b) : i111.Contains (n111 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b109 b hb) (b110 b hb))
    (by norm_num [i111, i109, i110, RationalInterval.add]) (by norm_num [i111, i109, i110, RationalInterval.add])

def n112 (b : ℝ) : ℝ := (n102 b) * (n21 b)
def i112 : RationalInterval := ⟨(1238928280673398602955603377119 / 1000000000000000000000000000000 : ℚ), (619464141254552245381552355583 / 500000000000000000000000000000 : ℚ)⟩
theorem b112 (b : ℝ) (hb : rootInterval.Contains b) : i112.Contains (n112 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b102 b hb) (b21 b hb))
    (by norm_num [i112, i102, i21, RationalInterval.mul]) (by norm_num [i112, i102, i21, RationalInterval.mul])

def n113 (b : ℝ) : ℝ := (n105 b) * (n55 b)
def i113 : RationalInterval := ⟨(-12313836811228090311226241483 / 250000000000000000000000000000 : ℚ), (-49255346837820252994915152301 / 1000000000000000000000000000000 : ℚ)⟩
theorem b113 (b : ℝ) (hb : rootInterval.Contains b) : i113.Contains (n113 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b105 b hb) (b55 b hb))
    (by norm_num [i113, i105, i55, RationalInterval.mul]) (by norm_num [i113, i105, i55, RationalInterval.mul])

def n114 (b : ℝ) : ℝ := (n112 b) + (n113 b)
def i114 : RationalInterval := ⟨(1189672933428486241710698411187 / 1000000000000000000000000000000 : ℚ), (237934587134256847553637911773 / 200000000000000000000000000000 : ℚ)⟩
theorem b114 (b : ℝ) (hb : rootInterval.Contains b) : i114.Contains (n114 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b112 b hb) (b113 b hb))
    (by norm_num [i114, i112, i113, RationalInterval.add]) (by norm_num [i114, i112, i113, RationalInterval.add])

def n115 (b : ℝ) : ℝ := (n102 b) * (n34 b)
def i115 : RationalInterval := ⟨(1309108944914182671622230610179 / 1000000000000000000000000000000 : ℚ), (16363861834563671369983389413 / 12500000000000000000000000000 : ℚ)⟩
theorem b115 (b : ℝ) (hb : rootInterval.Contains b) : i115.Contains (n115 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b102 b hb) (b34 b hb))
    (by norm_num [i115, i102, i34, RationalInterval.mul]) (by norm_num [i115, i102, i34, RationalInterval.mul])

def n116 (b : ℝ) : ℝ := (n105 b) * (n56 b)
def i116 : RationalInterval := ⟨(-632359147513731623785443584691 / 1000000000000000000000000000000 : ℚ), (-632359146427999731666005289779 / 1000000000000000000000000000000 : ℚ)⟩
theorem b116 (b : ℝ) (hb : rootInterval.Contains b) : i116.Contains (n116 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b105 b hb) (b56 b hb))
    (by norm_num [i116, i105, i56, RationalInterval.mul]) (by norm_num [i116, i105, i56, RationalInterval.mul])

def n117 (b : ℝ) : ℝ := (n115 b) + (n116 b)
def i117 : RationalInterval := ⟨(42296862337528190489799189093 / 62500000000000000000000000000 : ℚ), (676749800337093977932665863261 / 1000000000000000000000000000000 : ℚ)⟩
theorem b117 (b : ℝ) (hb : rootInterval.Contains b) : i117.Contains (n117 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b115 b hb) (b116 b hb))
    (by norm_num [i117, i115, i116, RationalInterval.add]) (by norm_num [i117, i115, i116, RationalInterval.add])

def n118 (b : ℝ) : ℝ := (n108 b) * (n89 b)
def i118 : RationalInterval := ⟨(26667116012643074465611901419 / 12500000000000000000000000000 : ℚ), (2133369284184716078266164977061 / 1000000000000000000000000000000 : ℚ)⟩
theorem b118 (b : ℝ) (hb : rootInterval.Contains b) : i118.Contains (n118 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b108 b hb) (b89 b hb))
    (by norm_num [i118, i108, i89, RationalInterval.mul]) (by norm_num [i118, i108, i89, RationalInterval.mul])

def n119 (b : ℝ) : ℝ := (n111 b) * (n89 b)
def i119 : RationalInterval := ⟨(1057487051022173525504846708317 / 1000000000000000000000000000000 : ℚ), (264371763711072280743186985731 / 250000000000000000000000000000 : ℚ)⟩
theorem b119 (b : ℝ) (hb : rootInterval.Contains b) : i119.Contains (n119 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b111 b hb) (b89 b hb))
    (by norm_num [i119, i111, i89, RationalInterval.mul]) (by norm_num [i119, i111, i89, RationalInterval.mul])

def n120 (b : ℝ) : ℝ := (n114 b) * (n89 b)
def i120 : RationalInterval := ⟨(1057487051936432214853954143277 / 1000000000000000000000000000000 : ℚ), (42299482157201217342868962093 / 40000000000000000000000000000 : ℚ)⟩
theorem b120 (b : ℝ) (hb : rootInterval.Contains b) : i120.Contains (n120 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b114 b hb) (b89 b hb))
    (by norm_num [i120, i114, i89, RationalInterval.mul]) (by norm_num [i120, i114, i89, RationalInterval.mul])

def n121 (b : ℝ) : ℝ := (n117 b) * (n89 b)
def i121 : RationalInterval := ⟨(4699651370836465609977687677 / 7812500000000000000000000000 : ℚ), (37597211129838554329592547959 / 62500000000000000000000000000 : ℚ)⟩
theorem b121 (b : ℝ) (hb : rootInterval.Contains b) : i121.Contains (n121 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b117 b hb) (b89 b hb))
    (by norm_num [i121, i117, i89, RationalInterval.mul]) (by norm_num [i121, i117, i89, RationalInterval.mul])

def n122 (b : ℝ) : ℝ := ((64 / 81 : ℚ) : ℝ)
def i122 : RationalInterval := ⟨(64 / 81 : ℚ), (64 / 81 : ℚ)⟩
theorem b122 (b : ℝ) (hb : rootInterval.Contains b) : i122.Contains (n122 b) := by
  exact RationalInterval.contains_point (64 / 81 : ℚ)

def n123 (b : ℝ) : ℝ := (n61 b) * (n122 b)
def i123 : RationalInterval := ⟨(35007663991111111111111111111 / 125000000000000000000000000000 : ℚ), (280061311930864197530864197531 / 1000000000000000000000000000000 : ℚ)⟩
theorem b123 (b : ℝ) (hb : rootInterval.Contains b) : i123.Contains (n123 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b61 b hb) (b122 b hb))
    (by norm_num [i123, i61, i122, RationalInterval.mul]) (by norm_num [i123, i61, i122, RationalInterval.mul])

def n124 (b : ℝ) : ℝ := ((8978 : ℚ) : ℝ)
def i124 : RationalInterval := ⟨(8978 : ℚ), (8978 : ℚ)⟩
theorem b124 (b : ℝ) (hb : rootInterval.Contains b) : i124.Contains (n124 b) := by
  exact RationalInterval.contains_point (8978 : ℚ)

def n125 (b : ℝ) : ℝ := (n0 b) * (n124 b)
def i125 : RationalInterval := ⟨(103001271201799 / 12500000000 : ℚ), (82401016962337 / 10000000000 : ℚ)⟩
theorem b125 (b : ℝ) (hb : rootInterval.Contains b) : i125.Contains (n125 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b0 b hb) (b124 b hb))
    (by norm_num [i125, i0, i124, RationalInterval.mul]) (by norm_num [i125, i0, i124, RationalInterval.mul])

def n126 (b : ℝ) : ℝ := (n125 b) * (n0 b)
def i126 : RationalInterval := ⟨(2363390926528524841564009 / 312500000000000000000 : ℚ), (1512570193011216305385721 / 200000000000000000000 : ℚ)⟩
theorem b126 (b : ℝ) (hb : rootInterval.Contains b) : i126.Contains (n126 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b125 b hb) (b0 b hb))
    (by norm_num [i126, i125, i0, RationalInterval.mul]) (by norm_num [i126, i125, i0, RationalInterval.mul])

def n127 (b : ℝ) : ℝ := ((6527 : ℚ) : ℝ)
def i127 : RationalInterval := ⟨(6527 : ℚ), (6527 : ℚ)⟩
theorem b127 (b : ℝ) (hb : rootInterval.Contains b) : i127.Contains (n127 b) := by
  exact RationalInterval.contains_point (6527 : ℚ)

def n128 (b : ℝ) : ℝ := (n0 b) * (n127 b)
def i128 : RationalInterval := ⟨(149763710655857 / 25000000000 : ℚ), (119810968525991 / 20000000000 : ℚ)⟩
theorem b128 (b : ℝ) (hb : rootInterval.Contains b) : i128.Contains (n128 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b0 b hb) (b127 b hb))
    (by norm_num [i128, i0, i127, RationalInterval.mul]) (by norm_num [i128, i0, i127, RationalInterval.mul])

def n129 (b : ℝ) : ℝ := -(n128 b)
def i129 : RationalInterval := ⟨(-119810968525991 / 20000000000 : ℚ), (-149763710655857 / 25000000000 : ℚ)⟩
theorem b129 (b : ℝ) (hb : rootInterval.Contains b) : i129.Contains (n129 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b128 b hb))
    (by norm_num [i129, i128, RationalInterval.neg]) (by norm_num [i129, i128, RationalInterval.neg])

def n130 (b : ℝ) : ℝ := (n126 b) + (n129 b)
def i130 : RationalInterval := ⟨(491344543309915466564009 / 312500000000000000000 : ℚ), (314460507764360305385721 / 200000000000000000000 : ℚ)⟩
theorem b130 (b : ℝ) (hb : rootInterval.Contains b) : i130.Contains (n130 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b126 b hb) (b129 b hb))
    (by norm_num [i130, i126, i129, RationalInterval.add]) (by norm_num [i130, i126, i129, RationalInterval.add])

def n131 (b : ℝ) : ℝ := (n130 b) + (n49 b)
def i131 : RationalInterval := ⟨(-228655456690084533435991 / 312500000000000000000 : ℚ), (-146339492235639694614279 / 200000000000000000000 : ℚ)⟩
theorem b131 (b : ℝ) (hb : rootInterval.Contains b) : i131.Contains (n131 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b130 b hb) (b49 b hb))
    (by norm_num [i131, i130, i49, RationalInterval.add]) (by norm_num [i131, i130, i49, RationalInterval.add])

def n132 (b : ℝ) : ℝ := (n131 b) * (n11 b)
def i132 : RationalInterval := ⟨(1317055430120757251528511 / 200000000000000000000 : ℚ), (2057899110210760800923919 / 312500000000000000000 : ℚ)⟩
theorem b132 (b : ℝ) (hb : rootInterval.Contains b) : i132.Contains (n132 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b131 b hb) (b11 b hb))
    (by norm_num [i132, i131, i11, RationalInterval.mul]) (by norm_num [i132, i131, i11, RationalInterval.mul])

def n133 (b : ℝ) : ℝ := ((5440 : ℚ) : ℝ)
def i133 : RationalInterval := ⟨(5440 : ℚ), (5440 : ℚ)⟩
theorem b133 (b : ℝ) (hb : rootInterval.Contains b) : i133.Contains (n133 b) := by
  exact RationalInterval.contains_point (5440 : ℚ)

def n134 (b : ℝ) : ℝ := (n0 b) * (n133 b)
def i134 : RationalInterval := ⟨(390069416447 / 78125000 : ℚ), (312055533161 / 62500000 : ℚ)⟩
theorem b134 (b : ℝ) (hb : rootInterval.Contains b) : i134.Contains (n134 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b0 b hb) (b133 b hb))
    (by norm_num [i134, i0, i133, RationalInterval.mul]) (by norm_num [i134, i0, i133, RationalInterval.mul])

def n135 (b : ℝ) : ℝ := 1 / (n134 b)
def i135 : RationalInterval := ⟨(200284863937195873742483727 / 1000000000000000000000000000000 : ℚ), (100142431969689038398101429 / 500000000000000000000000000000 : ℚ)⟩
theorem b135 (b : ℝ) (hb : rootInterval.Contains b) : i135.Contains (n135 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_inv_of_positive (b134 b hb) (by norm_num [i134]))
    (by norm_num [i135, i134, RationalInterval.inv]) (by norm_num [i135, i134, RationalInterval.inv])

def n136 (b : ℝ) : ℝ := (n132 b) * (n135 b)
def i136 : RationalInterval := ⟨(1318931338097404270889750892089 / 1000000000000000000000000000000 : ℚ), (659465669263247098446750366451 / 500000000000000000000000000000 : ℚ)⟩
theorem b136 (b : ℝ) (hb : rootInterval.Contains b) : i136.Contains (n136 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b132 b hb) (b135 b hb))
    (by norm_num [i136, i132, i135, RationalInterval.mul]) (by norm_num [i136, i132, i135, RationalInterval.mul])

def n137 (b : ℝ) : ℝ := ((1764 : ℚ) : ℝ)
def i137 : RationalInterval := ⟨(1764 : ℚ), (1764 : ℚ)⟩
theorem b137 (b : ℝ) (hb : rootInterval.Contains b) : i137.Contains (n137 b) := by
  exact RationalInterval.contains_point (1764 : ℚ)

def n138 (b : ℝ) : ℝ := (n0 b) * (n137 b)
def i138 : RationalInterval := ⟨(10118859567831 / 6250000000 : ℚ), (8095087654353 / 5000000000 : ℚ)⟩
theorem b138 (b : ℝ) (hb : rootInterval.Contains b) : i138.Contains (n138 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b0 b hb) (b137 b hb))
    (by norm_num [i138, i0, i137, RationalInterval.mul]) (by norm_num [i138, i0, i137, RationalInterval.mul])

def n139 (b : ℝ) : ℝ := (n138 b) * (n0 b)
def i139 : RationalInterval := ⟨(232179861572528281383321 / 156250000000000000000 : ℚ), (148595111409656135147049 / 100000000000000000000 : ℚ)⟩
theorem b139 (b : ℝ) (hb : rootInterval.Contains b) : i139.Contains (n139 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b138 b hb) (b0 b hb))
    (by norm_num [i139, i138, i0, RationalInterval.mul]) (by norm_num [i139, i138, i0, RationalInterval.mul])

def n140 (b : ℝ) : ℝ := ((2671 : ℚ) : ℝ)
def i140 : RationalInterval := ⟨(2671 : ℚ), (2671 : ℚ)⟩
theorem b140 (b : ℝ) (hb : rootInterval.Contains b) : i140.Contains (n140 b) := by
  exact RationalInterval.contains_point (2671 : ℚ)

def n141 (b : ℝ) : ℝ := (n0 b) * (n140 b)
def i141 : RationalInterval := ⟨(61286788901761 / 25000000000 : ℚ), (49029431121943 / 20000000000 : ℚ)⟩
theorem b141 (b : ℝ) (hb : rootInterval.Contains b) : i141.Contains (n141 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b0 b hb) (b140 b hb))
    (by norm_num [i141, i0, i140, RationalInterval.mul]) (by norm_num [i141, i0, i140, RationalInterval.mul])

def n142 (b : ℝ) : ℝ := -(n141 b)
def i142 : RationalInterval := ⟨(-49029431121943 / 20000000000 : ℚ), (-61286788901761 / 25000000000 : ℚ)⟩
theorem b142 (b : ℝ) (hb : rootInterval.Contains b) : i142.Contains (n142 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b141 b hb))
    (by norm_num [i142, i141, RationalInterval.neg]) (by norm_num [i142, i141, RationalInterval.neg])

def n143 (b : ℝ) : ℝ := (n139 b) + (n142 b)
def i143 : RationalInterval := ⟨(-150862569067651406116679 / 156250000000000000000 : ℚ), (-96552044197387864852951 / 100000000000000000000 : ℚ)⟩
theorem b143 (b : ℝ) (hb : rootInterval.Contains b) : i143.Contains (n143 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b139 b hb) (b142 b hb))
    (by norm_num [i143, i139, i142, RationalInterval.add]) (by norm_num [i143, i139, i142, RationalInterval.add])

def n144 (b : ℝ) : ℝ := ((1488 : ℚ) : ℝ)
def i144 : RationalInterval := ⟨(1488 : ℚ), (1488 : ℚ)⟩
theorem b144 (b : ℝ) (hb : rootInterval.Contains b) : i144.Contains (n144 b) := by
  exact RationalInterval.contains_point (1488 : ℚ)

def n145 (b : ℝ) : ℝ := (n143 b) + (n144 b)
def i145 : RationalInterval := ⟨(81637430932348593883321 / 156250000000000000000 : ℚ), (52247955802612135147049 / 100000000000000000000 : ℚ)⟩
theorem b145 (b : ℝ) (hb : rootInterval.Contains b) : i145.Contains (n145 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b143 b hb) (b144 b hb))
    (by norm_num [i145, i143, i144, RationalInterval.add]) (by norm_num [i145, i143, i144, RationalInterval.add])

def n146 (b : ℝ) : ℝ := ((9 : ℚ) : ℝ)
def i146 : RationalInterval := ⟨(9 : ℚ), (9 : ℚ)⟩
theorem b146 (b : ℝ) (hb : rootInterval.Contains b) : i146.Contains (n146 b) := by
  exact RationalInterval.contains_point (9 : ℚ)

def n147 (b : ℝ) : ℝ := (n145 b) * (n146 b)
def i147 : RationalInterval := ⟨(734736878391137344949889 / 156250000000000000000 : ℚ), (470231602223509216323441 / 100000000000000000000 : ℚ)⟩
theorem b147 (b : ℝ) (hb : rootInterval.Contains b) : i147.Contains (n147 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b145 b hb) (b146 b hb))
    (by norm_num [i147, i145, i146, RationalInterval.mul]) (by norm_num [i147, i145, i146, RationalInterval.mul])

def n148 (b : ℝ) : ℝ := ((2720 : ℚ) : ℝ)
def i148 : RationalInterval := ⟨(2720 : ℚ), (2720 : ℚ)⟩
theorem b148 (b : ℝ) (hb : rootInterval.Contains b) : i148.Contains (n148 b) := by
  exact RationalInterval.contains_point (2720 : ℚ)

def n149 (b : ℝ) : ℝ := ((1 / 2720 : ℚ) : ℝ)
def i149 : RationalInterval := ⟨(1 / 2720 : ℚ), (1 / 2720 : ℚ)⟩
theorem b149 (b : ℝ) (hb : rootInterval.Contains b) : i149.Contains (n149 b) := by
  exact RationalInterval.contains_point (1 / 2720 : ℚ)

def n150 (b : ℝ) : ℝ := (n147 b) * (n149 b)
def i150 : RationalInterval := ⟨(1728792655037970223411503529411 / 1000000000000000000000000000000 : ℚ), (1728792655233489765895003676471 / 1000000000000000000000000000000 : ℚ)⟩
theorem b150 (b : ℝ) (hb : rootInterval.Contains b) : i150.Contains (n150 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b147 b hb) (b149 b hb))
    (by norm_num [i150, i147, i149, RationalInterval.mul]) (by norm_num [i150, i147, i149, RationalInterval.mul])

def n151 (b : ℝ) : ℝ := (n136 b) + (n16 b)
def i151 : RationalInterval := ⟨(318931338097404270889750892089 / 1000000000000000000000000000000 : ℚ), (159465669263247098446750366451 / 500000000000000000000000000000 : ℚ)⟩
theorem b151 (b : ℝ) (hb : rootInterval.Contains b) : i151.Contains (n151 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b136 b hb) (b16 b hb))
    (by norm_num [i151, i136, i16, RationalInterval.add]) (by norm_num [i151, i136, i16, RationalInterval.add])

def n152 (b : ℝ) : ℝ := ((-1 / 2 : ℚ) : ℝ)
def i152 : RationalInterval := ⟨(-1 / 2 : ℚ), (-1 / 2 : ℚ)⟩
theorem b152 (b : ℝ) (hb : rootInterval.Contains b) : i152.Contains (n152 b) := by
  exact RationalInterval.contains_point (-1 / 2 : ℚ)

def n153 (b : ℝ) : ℝ := (n150 b) + (n152 b)
def i153 : RationalInterval := ⟨(1228792655037970223411503529411 / 1000000000000000000000000000000 : ℚ), (1228792655233489765895003676471 / 1000000000000000000000000000000 : ℚ)⟩
theorem b153 (b : ℝ) (hb : rootInterval.Contains b) : i153.Contains (n153 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b150 b hb) (b152 b hb))
    (by norm_num [i153, i150, i152, RationalInterval.add]) (by norm_num [i153, i150, i152, RationalInterval.add])

def n154 (b : ℝ) : ℝ := (n21 b) * (n136 b)
def i154 : RationalInterval := ⟨(-1376805810359433546796258899563 / 1000000000000000000000000000000 : ℚ), (-1376805809416436911379740994739 / 1000000000000000000000000000000 : ℚ)⟩
theorem b154 (b : ℝ) (hb : rootInterval.Contains b) : i154.Contains (n154 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b21 b hb) (b136 b hb))
    (by norm_num [i154, i21, i136, RationalInterval.mul]) (by norm_num [i154, i21, i136, RationalInterval.mul])

def n155 (b : ℝ) : ℝ := (n55 b) * (n150 b)
def i155 : RationalInterval := ⟨(70283437220899399837348870649 / 500000000000000000000000000000 : ℚ), (14056687542867082398082348557 / 100000000000000000000000000000 : ℚ)⟩
theorem b155 (b : ℝ) (hb : rootInterval.Contains b) : i155.Contains (n155 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b55 b hb) (b150 b hb))
    (by norm_num [i155, i55, i150, RationalInterval.mul]) (by norm_num [i155, i55, i150, RationalInterval.mul])

def n156 (b : ℝ) : ℝ := (n154 b) + (n155 b)
def i156 : RationalInterval := ⟨(-247247787183526949424312231653 / 200000000000000000000000000000 : ℚ), (-1236238933987766087398917509169 / 1000000000000000000000000000000 : ℚ)⟩
theorem b156 (b : ℝ) (hb : rootInterval.Contains b) : i156.Contains (n156 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b154 b hb) (b155 b hb))
    (by norm_num [i156, i154, i155, RationalInterval.add]) (by norm_num [i156, i154, i155, RationalInterval.add])

def n157 (b : ℝ) : ℝ := (n34 b) * (n136 b)
def i157 : RationalInterval := ⟨(-727398361045347357759558604903 / 500000000000000000000000000000 : ℚ), (-72739836059647089289969264881 / 50000000000000000000000000000 : ℚ)⟩
theorem b157 (b : ℝ) (hb : rootInterval.Contains b) : i157.Contains (n157 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b34 b hb) (b136 b hb))
    (by norm_num [i157, i34, i136, RationalInterval.mul]) (by norm_num [i157, i34, i136, RationalInterval.mul])

def n158 (b : ℝ) : ℝ := (n56 b) * (n150 b)
def i158 : RationalInterval := ⟨(1804651767669927638949004018561 / 1000000000000000000000000000000 : ℚ), (45116294213073793240644587619 / 25000000000000000000000000000 : ℚ)⟩
theorem b158 (b : ℝ) (hb : rootInterval.Contains b) : i158.Contains (n158 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b56 b hb) (b150 b hb))
    (by norm_num [i158, i56, i150, RationalInterval.mul]) (by norm_num [i158, i56, i150, RationalInterval.mul])

def n159 (b : ℝ) : ℝ := (n157 b) + (n158 b)
def i159 : RationalInterval := ⟨(69971009115846584685977361751 / 200000000000000000000000000000 : ℚ), (17492752366500497191319910357 / 50000000000000000000000000000 : ℚ)⟩
theorem b159 (b : ℝ) (hb : rootInterval.Contains b) : i159.Contains (n159 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b157 b hb) (b158 b hb))
    (by norm_num [i159, i157, i158, RationalInterval.add]) (by norm_num [i159, i157, i158, RationalInterval.add])

def n160 (b : ℝ) : ℝ := (n156 b) * (n89 b)
def i160 : RationalInterval := ⟨(-1098879054149008664108054362903 / 1000000000000000000000000000000 : ℚ), (-549439526216784927732852226297 / 500000000000000000000000000000 : ℚ)⟩
theorem b160 (b : ℝ) (hb : rootInterval.Contains b) : i160.Contains (n160 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b156 b hb) (b89 b hb))
    (by norm_num [i160, i156, i89, RationalInterval.mul]) (by norm_num [i160, i156, i89, RationalInterval.mul])

def n161 (b : ℝ) : ℝ := (n159 b) * (n89 b)
def i161 : RationalInterval := ⟨(310982262737095931937677163337 / 1000000000000000000000000000000 : ℚ), (1943639151833388576813323373 / 6250000000000000000000000000 : ℚ)⟩
theorem b161 (b : ℝ) (hb : rootInterval.Contains b) : i161.Contains (n161 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b159 b hb) (b89 b hb))
    (by norm_num [i161, i159, i89, RationalInterval.mul]) (by norm_num [i161, i159, i89, RationalInterval.mul])

def n162 (b : ℝ) : ℝ := (n21 b) * (n151 b)
def i162 : RationalInterval := ⟨(-66585197752531537820923592503 / 200000000000000000000000000000 : ℚ), (-33292598819502427822480280593 / 100000000000000000000000000000 : ℚ)⟩
theorem b162 (b : ℝ) (hb : rootInterval.Contains b) : i162.Contains (n162 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b21 b hb) (b151 b hb))
    (by norm_num [i162, i21, i151, RationalInterval.mul]) (by norm_num [i162, i21, i151, RationalInterval.mul])

def n163 (b : ℝ) : ℝ := (n55 b) * (n153 b)
def i163 : RationalInterval := ⟨(99912237799236401582303440469 / 1000000000000000000000000000000 : ℚ), (49956119252641990944316490689 / 500000000000000000000000000000 : ℚ)⟩
theorem b163 (b : ℝ) (hb : rootInterval.Contains b) : i163.Contains (n163 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b55 b hb) (b153 b hb))
    (by norm_num [i163, i55, i153, RationalInterval.mul]) (by norm_num [i163, i55, i153, RationalInterval.mul])

def n164 (b : ℝ) : ℝ := (n162 b) + (n163 b)
def i164 : RationalInterval := ⟨(-116506875481710643761157261023 / 500000000000000000000000000000 : ℚ), (-29126718711217537042021228069 / 125000000000000000000000000000 : ℚ)⟩
theorem b164 (b : ℝ) (hb : rootInterval.Contains b) : i164.Contains (n164 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b162 b hb) (b163 b hb))
    (by norm_num [i164, i162, i163, RationalInterval.add]) (by norm_num [i164, i162, i163, RationalInterval.add])

def n165 (b : ℝ) : ℝ := (n34 b) * (n151 b)
def i165 : RationalInterval := ⟨(-351785003743029337123549131199 / 1000000000000000000000000000000 : ℚ), (-351785003167098856269852376751 / 1000000000000000000000000000000 : ℚ)⟩
theorem b165 (b : ℝ) (hb : rootInterval.Contains b) : i165.Contains (n165 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b34 b hb) (b151 b hb))
    (by norm_num [i165, i34, i151, RationalInterval.mul]) (by norm_num [i165, i34, i151, RationalInterval.mul])

def n166 (b : ℝ) : ℝ := (n56 b) * (n153 b)
def i166 : RationalInterval := ⟨(320677964264805330592883731039 / 250000000000000000000000000000 : ℚ), (320677964431140950194990759059 / 250000000000000000000000000000 : ℚ)⟩
theorem b166 (b : ℝ) (hb : rootInterval.Contains b) : i166.Contains (n166 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b56 b hb) (b153 b hb))
    (by norm_num [i166, i56, i153, RationalInterval.mul]) (by norm_num [i166, i56, i153, RationalInterval.mul])

def n167 (b : ℝ) : ℝ := (n165 b) + (n166 b)
def i167 : RationalInterval := ⟨(930926853316191985247985792957 / 1000000000000000000000000000000 : ℚ), (186185370911492988902022131897 / 200000000000000000000000000000 : ℚ)⟩
theorem b167 (b : ℝ) (hb : rootInterval.Contains b) : i167.Contains (n167 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b165 b hb) (b166 b hb))
    (by norm_num [i167, i165, i166, RationalInterval.add]) (by norm_num [i167, i165, i166, RationalInterval.add])

def n168 (b : ℝ) : ℝ := (n164 b) * (n89 b)
def i168 : RationalInterval := ⟨(-207123334189707811130946241819 / 1000000000000000000000000000000 : ℚ), (-207123333057546930076595399601 / 1000000000000000000000000000000 : ℚ)⟩
theorem b168 (b : ℝ) (hb : rootInterval.Contains b) : i168.Contains (n168 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b164 b hb) (b89 b hb))
    (by norm_num [i168, i164, i89, RationalInterval.mul]) (by norm_num [i168, i164, i89, RationalInterval.mul])

def n169 (b : ℝ) : ℝ := (n167 b) * (n89 b)
def i169 : RationalInterval := ⟨(103436317035132442805331754773 / 125000000000000000000000000000 : ℚ), (206872634346103321002246813219 / 250000000000000000000000000000 : ℚ)⟩
theorem b169 (b : ℝ) (hb : rootInterval.Contains b) : i169.Contains (n169 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b167 b hb) (b89 b hb))
    (by norm_num [i169, i167, i89, RationalInterval.mul]) (by norm_num [i169, i167, i89, RationalInterval.mul])

def n170 (b : ℝ) : ℝ := (n136 b) * (n122 b)
def i170 : RationalInterval := ⟨(1042118588126344115270914285107 / 1000000000000000000000000000000 : ℚ), (521059294232689065439407696949 / 500000000000000000000000000000 : ℚ)⟩
theorem b170 (b : ℝ) (hb : rootInterval.Contains b) : i170.Contains (n170 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b136 b hb) (b122 b hb))
    (by norm_num [i170, i136, i122, RationalInterval.mul]) (by norm_num [i170, i136, i122, RationalInterval.mul])

def n171 (b : ℝ) : ℝ := (n150 b) * (n122 b)
def i171 : RationalInterval := ⟨(1365959628671976472818965751633 / 1000000000000000000000000000000 : ℚ), (1365959628826461049596052287583 / 1000000000000000000000000000000 : ℚ)⟩
theorem b171 (b : ℝ) (hb : rootInterval.Contains b) : i171.Contains (n171 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b150 b hb) (b122 b hb))
    (by norm_num [i171, i150, i122, RationalInterval.mul]) (by norm_num [i171, i150, i122, RationalInterval.mul])

def n172 (b : ℝ) : ℝ := -(n150 b)
def i172 : RationalInterval := ⟨(-1728792655233489765895003676471 / 1000000000000000000000000000000 : ℚ), (-1728792655037970223411503529411 / 1000000000000000000000000000000 : ℚ)⟩
theorem b172 (b : ℝ) (hb : rootInterval.Contains b) : i172.Contains (n172 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b150 b hb))
    (by norm_num [i172, i150, RationalInterval.neg]) (by norm_num [i172, i150, RationalInterval.neg])

def n173 (b : ℝ) : ℝ := (n172 b) * (n172 b)
def i173 : RationalInterval := ⟨(298872404411323431168647442617 / 100000000000000000000000000000 : ℚ), (149436202239462990482421059247 / 50000000000000000000000000000 : ℚ)⟩
theorem b173 (b : ℝ) (hb : rootInterval.Contains b) : i173.Contains (n173 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b172 b hb) (b172 b hb))
    (by norm_num [i173, i172, i172, RationalInterval.mul]) (by norm_num [i173, i172, i172, RationalInterval.mul])

def n174 (b : ℝ) : ℝ := (n172 b) * (n136 b)
def i174 : RationalInterval := ⟨(-2280158810801878659953742857579 / 1000000000000000000000000000000 : ℚ), (-2280158809802194295651823393587 / 1000000000000000000000000000000 : ℚ)⟩
theorem b174 (b : ℝ) (hb : rootInterval.Contains b) : i174.Contains (n174 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b172 b hb) (b136 b hb))
    (by norm_num [i174, i172, i136, RationalInterval.mul]) (by norm_num [i174, i172, i136, RationalInterval.mul])

def n175 (b : ℝ) : ℝ := (n136 b) * (n172 b)
def i175 : RationalInterval := ⟨(-2280158810801878659953742857579 / 1000000000000000000000000000000 : ℚ), (-2280158809802194295651823393587 / 1000000000000000000000000000000 : ℚ)⟩
theorem b175 (b : ℝ) (hb : rootInterval.Contains b) : i175.Contains (n175 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b136 b hb) (b172 b hb))
    (by norm_num [i175, i136, i172, RationalInterval.mul]) (by norm_num [i175, i136, i172, RationalInterval.mul])

def n176 (b : ℝ) : ℝ := (n136 b) * (n136 b)
def i176 : RationalInterval := ⟨(869789937307704667336277390583 / 500000000000000000000000000000 : ℚ), (54361871117102801106036152177 / 31250000000000000000000000000 : ℚ)⟩
theorem b176 (b : ℝ) (hb : rootInterval.Contains b) : i176.Contains (n176 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b136 b hb) (b136 b hb))
    (by norm_num [i176, i136, i136, RationalInterval.mul]) (by norm_num [i176, i136, i136, RationalInterval.mul])

def n177 (b : ℝ) : ℝ := (n150 b) * (n150 b)
def i177 : RationalInterval := ⟨(298872404411323431168647442617 / 100000000000000000000000000000 : ℚ), (149436202239462990482421059247 / 50000000000000000000000000000 : ℚ)⟩
theorem b177 (b : ℝ) (hb : rootInterval.Contains b) : i177.Contains (n177 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b150 b hb) (b150 b hb))
    (by norm_num [i177, i150, i150, RationalInterval.mul]) (by norm_num [i177, i150, i150, RationalInterval.mul])

def n178 (b : ℝ) : ℝ := (n176 b) + (n177 b)
def i178 : RationalInterval := ⟨(591037989841080455794878650917 / 125000000000000000000000000000 : ℚ), (1182075980134137361260394513651 / 250000000000000000000000000000 : ℚ)⟩
theorem b178 (b : ℝ) (hb : rootInterval.Contains b) : i178.Contains (n178 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b176 b hb) (b177 b hb))
    (by norm_num [i178, i176, i177, RationalInterval.add]) (by norm_num [i178, i176, i177, RationalInterval.add])

def n179 (b : ℝ) : ℝ := ((19 / 10 : ℚ) : ℝ)
def i179 : RationalInterval := ⟨(19 / 10 : ℚ), (19 / 10 : ℚ)⟩
theorem b179 (b : ℝ) (hb : rootInterval.Contains b) : i179.Contains (n179 b) := by
  exact RationalInterval.contains_point (19 / 10 : ℚ)

