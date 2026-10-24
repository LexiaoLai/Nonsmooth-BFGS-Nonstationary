import BFGS.Counterexample.Certificates.IntervalTrace1

/-! Generated arithmetic proofs. Each bound is checked by the Lean kernel. -/
namespace BFGS.Counterexample.Trace
noncomputable section
open BFGS RationalInterval
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false

def n180 (b : ℝ) : ℝ := 1 / (n178 b)
def i180 : RationalInterval := ⟨(26436540903617610233765386383 / 125000000000000000000000000000 : ℚ), (21149232730980670846379066147 / 100000000000000000000000000000 : ℚ)⟩
theorem b180 (b : ℝ) (hb : rootInterval.Contains b) : i180.Contains (n180 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_inv_of_positive (b178 b hb) (by norm_num [i178]))
    (by norm_num [i180, i178, RationalInterval.inv]) (by norm_num [i180, i178, RationalInterval.inv])

def n181 (b : ℝ) : ℝ := (n179 b) * (n180 b)
def i181 : RationalInterval := ⟨(401835421734987675553233873021 / 1000000000000000000000000000000 : ℚ), (401835421888632746081202256793 / 1000000000000000000000000000000 : ℚ)⟩
theorem b181 (b : ℝ) (hb : rootInterval.Contains b) : i181.Contains (n181 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b179 b hb) (b180 b hb))
    (by norm_num [i181, i179, i180, RationalInterval.mul]) (by norm_num [i181, i179, i180, RationalInterval.mul])

def n182 (b : ℝ) : ℝ := (n181 b) * (n173 b)
def i182 : RationalInterval := ⟨(600487593357869709680513286419 / 500000000000000000000000000000 : ℚ), (15012189843082414088605640777 / 12500000000000000000000000000 : ℚ)⟩
theorem b182 (b : ℝ) (hb : rootInterval.Contains b) : i182.Contains (n182 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b181 b hb) (b173 b hb))
    (by norm_num [i182, i181, i173, RationalInterval.mul]) (by norm_num [i182, i181, i173, RationalInterval.mul])

def n183 (b : ℝ) : ℝ := (n181 b) * (n174 b)
def i183 : RationalInterval := ⟨(-916248577711656044457550038539 / 1000000000000000000000000000000 : ℚ), (-14316384014993942109778000117 / 15625000000000000000000000000 : ℚ)⟩
theorem b183 (b : ℝ) (hb : rootInterval.Contains b) : i183.Contains (n183 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b181 b hb) (b174 b hb))
    (by norm_num [i183, i181, i174, RationalInterval.mul]) (by norm_num [i183, i181, i174, RationalInterval.mul])

def n184 (b : ℝ) : ℝ := (n181 b) * (n175 b)
def i184 : RationalInterval := ⟨(-916248577711656044457550038539 / 1000000000000000000000000000000 : ℚ), (-14316384014993942109778000117 / 15625000000000000000000000000 : ℚ)⟩
theorem b184 (b : ℝ) (hb : rootInterval.Contains b) : i184.Contains (n184 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b181 b hb) (b175 b hb))
    (by norm_num [i184, i181, i175, RationalInterval.mul]) (by norm_num [i184, i181, i175, RationalInterval.mul])

def n185 (b : ℝ) : ℝ := (n181 b) * (n176 b)
def i185 : RationalInterval := ⟨(349512406278889995784120842581 / 500000000000000000000000000000 : ℚ), (34951240663994373113002814689 / 50000000000000000000000000000 : ℚ)⟩
theorem b185 (b : ℝ) (hb : rootInterval.Contains b) : i185.Contains (n185 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b181 b hb) (b176 b hb))
    (by norm_num [i185, i181, i176, RationalInterval.mul]) (by norm_num [i185, i181, i176, RationalInterval.mul])

def n186 (b : ℝ) : ℝ := -(n153 b)
def i186 : RationalInterval := ⟨(-1228792655233489765895003676471 / 1000000000000000000000000000000 : ℚ), (-1228792655037970223411503529411 / 1000000000000000000000000000000 : ℚ)⟩
theorem b186 (b : ℝ) (hb : rootInterval.Contains b) : i186.Contains (n186 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b153 b hb))
    (by norm_num [i186, i153, RationalInterval.neg]) (by norm_num [i186, i153, RationalInterval.neg])

def n187 (b : ℝ) : ℝ := (n186 b) * (n186 b)
def i187 : RationalInterval := ⟨(1509931389075264088274970896759 / 1000000000000000000000000000000 : ℚ), (1509931389555770043753417508469 / 1000000000000000000000000000000 : ℚ)⟩
theorem b187 (b : ℝ) (hb : rootInterval.Contains b) : i187.Contains (n187 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b186 b hb) (b186 b hb))
    (by norm_num [i187, i186, i186, RationalInterval.mul]) (by norm_num [i187, i186, i186, RationalInterval.mul])

def n188 (b : ℝ) : ℝ := (n186 b) * (n151 b)
def i188 : RationalInterval := ⟨(-391900486305141795611988814657 / 1000000000000000000000000000000 : ℚ), (-97975121428880484198861104533 / 250000000000000000000000000000 : ℚ)⟩
theorem b188 (b : ℝ) (hb : rootInterval.Contains b) : i188.Contains (n188 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b186 b hb) (b151 b hb))
    (by norm_num [i188, i186, i151, RationalInterval.mul]) (by norm_num [i188, i186, i151, RationalInterval.mul])

def n189 (b : ℝ) : ℝ := (n151 b) * (n186 b)
def i189 : RationalInterval := ⟨(-391900486305141795611988814657 / 1000000000000000000000000000000 : ℚ), (-97975121428880484198861104533 / 250000000000000000000000000000 : ℚ)⟩
theorem b189 (b : ℝ) (hb : rootInterval.Contains b) : i189.Contains (n189 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b151 b hb) (b186 b hb))
    (by norm_num [i189, i151, i186, RationalInterval.mul]) (by norm_num [i189, i151, i186, RationalInterval.mul])

def n190 (b : ℝ) : ℝ := (n151 b) * (n151 b)
def i190 : RationalInterval := ⟨(25429299605150198223263249247 / 250000000000000000000000000000 : ℚ), (5085859934715062080307770193 / 50000000000000000000000000000 : ℚ)⟩
theorem b190 (b : ℝ) (hb : rootInterval.Contains b) : i190.Contains (n190 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b151 b hb) (b151 b hb))
    (by norm_num [i190, i151, i151, RationalInterval.mul]) (by norm_num [i190, i151, i151, RationalInterval.mul])

def n191 (b : ℝ) : ℝ := (n153 b) * (n153 b)
def i191 : RationalInterval := ⟨(1509931389075264088274970896759 / 1000000000000000000000000000000 : ℚ), (1509931389555770043753417508469 / 1000000000000000000000000000000 : ℚ)⟩
theorem b191 (b : ℝ) (hb : rootInterval.Contains b) : i191.Contains (n191 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b153 b hb) (b153 b hb))
    (by norm_num [i191, i153, i153, RationalInterval.mul]) (by norm_num [i191, i153, i153, RationalInterval.mul])

def n192 (b : ℝ) : ℝ := (n190 b) + (n191 b)
def i192 : RationalInterval := ⟨(1611648587495864881168023893747 / 1000000000000000000000000000000 : ℚ), (1611648588250071285359572912329 / 1000000000000000000000000000000 : ℚ)⟩
theorem b192 (b : ℝ) (hb : rootInterval.Contains b) : i192.Contains (n192 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b190 b hb) (b191 b hb))
    (by norm_num [i192, i190, i191, RationalInterval.add]) (by norm_num [i192, i190, i191, RationalInterval.add])

def n193 (b : ℝ) : ℝ := ((8 / 5 : ℚ) : ℝ)
def i193 : RationalInterval := ⟨(8 / 5 : ℚ), (8 / 5 : ℚ)⟩
theorem b193 (b : ℝ) (hb : rootInterval.Contains b) : i193.Contains (n193 b) := by
  exact RationalInterval.contains_point (8 / 5 : ℚ)

def n194 (b : ℝ) : ℝ := 1 / (n192 b)
def i194 : RationalInterval := ⟨(310241329062249364294880068647 / 500000000000000000000000000000 : ℚ), (155120664603716808942030905841 / 250000000000000000000000000000 : ℚ)⟩
theorem b194 (b : ℝ) (hb : rootInterval.Contains b) : i194.Contains (n194 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_inv_of_positive (b192 b hb) (by norm_num [i192]))
    (by norm_num [i194, i192, RationalInterval.inv]) (by norm_num [i194, i192, RationalInterval.inv])

def n195 (b : ℝ) : ℝ := (n193 b) * (n194 b)
def i195 : RationalInterval := ⟨(99277225299919796574361621967 / 100000000000000000000000000000 : ℚ), (992772253463787577228997797383 / 1000000000000000000000000000000 : ℚ)⟩
theorem b195 (b : ℝ) (hb : rootInterval.Contains b) : i195.Contains (n195 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b193 b hb) (b194 b hb))
    (by norm_num [i195, i193, i194, RationalInterval.mul]) (by norm_num [i195, i193, i194, RationalInterval.mul])

def n196 (b : ℝ) : ℝ := (n195 b) * (n187 b)
def i196 : RationalInterval := ⟨(1499017987006458498787906232757 / 1000000000000000000000000000000 : ℚ), (749508994092494958215536766851 / 500000000000000000000000000000 : ℚ)⟩
theorem b196 (b : ℝ) (hb : rootInterval.Contains b) : i196.Contains (n196 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b195 b hb) (b187 b hb))
    (by norm_num [i196, i195, i187, RationalInterval.mul]) (by norm_num [i196, i195, i187, RationalInterval.mul])

def n197 (b : ℝ) : ℝ := (n195 b) * (n188 b)
def i197 : RationalInterval := ⟨(-97266982230677460743126848381 / 250000000000000000000000000000 : ℚ), (-389067928155278712648699664163 / 1000000000000000000000000000000 : ℚ)⟩
theorem b197 (b : ℝ) (hb : rootInterval.Contains b) : i197.Contains (n197 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b195 b hb) (b188 b hb))
    (by norm_num [i197, i195, i188, RationalInterval.mul]) (by norm_num [i197, i195, i188, RationalInterval.mul])

def n198 (b : ℝ) : ℝ := (n195 b) * (n189 b)
def i198 : RationalInterval := ⟨(-97266982230677460743126848381 / 250000000000000000000000000000 : ℚ), (-389067928155278712648699664163 / 1000000000000000000000000000000 : ℚ)⟩
theorem b198 (b : ℝ) (hb : rootInterval.Contains b) : i198.Contains (n198 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b195 b hb) (b189 b hb))
    (by norm_num [i198, i195, i189, RationalInterval.mul]) (by norm_num [i198, i195, i189, RationalInterval.mul])

def n199 (b : ℝ) : ℝ := (n195 b) * (n190 b)
def i199 : RationalInterval := ⟨(25245503061196577524106475969 / 250000000000000000000000000000 : ℚ), (6311375785235329689686924373 / 62500000000000000000000000000 : ℚ)⟩
theorem b199 (b : ℝ) (hb : rootInterval.Contains b) : i199.Contains (n199 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b195 b hb) (b190 b hb))
    (by norm_num [i199, i195, i190, RationalInterval.mul]) (by norm_num [i199, i195, i190, RationalInterval.mul])

def n200 (b : ℝ) : ℝ := -(n161 b)
def i200 : RationalInterval := ⟨(-1943639151833388576813323373 / 6250000000000000000000000000 : ℚ), (-310982262737095931937677163337 / 1000000000000000000000000000000 : ℚ)⟩
theorem b200 (b : ℝ) (hb : rootInterval.Contains b) : i200.Contains (n200 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b161 b hb))
    (by norm_num [i200, i161, RationalInterval.neg]) (by norm_num [i200, i161, RationalInterval.neg])

def n201 (b : ℝ) : ℝ := (n200 b) * (n200 b)
def i201 : RationalInterval := ⟨(96709967737084164993264187439 / 1000000000000000000000000000000 : ℚ), (24177492176253530454244024143 / 250000000000000000000000000000 : ℚ)⟩
theorem b201 (b : ℝ) (hb : rootInterval.Contains b) : i201.Contains (n201 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b200 b hb) (b200 b hb))
    (by norm_num [i201, i200, i200, RationalInterval.mul]) (by norm_num [i201, i200, i200, RationalInterval.mul])

def n202 (b : ℝ) : ℝ := (n200 b) * (n160 b)
def i202 : RationalInterval := ⟨(68346378840037487525610323019 / 200000000000000000000000000000 : ℚ), (170865948221892438274066895633 / 500000000000000000000000000000 : ℚ)⟩
theorem b202 (b : ℝ) (hb : rootInterval.Contains b) : i202.Contains (n202 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b200 b hb) (b160 b hb))
    (by norm_num [i202, i200, i160, RationalInterval.mul]) (by norm_num [i202, i200, i160, RationalInterval.mul])

def n203 (b : ℝ) : ℝ := (n160 b) * (n200 b)
def i203 : RationalInterval := ⟨(68346378840037487525610323019 / 200000000000000000000000000000 : ℚ), (170865948221892438274066895633 / 500000000000000000000000000000 : ℚ)⟩
theorem b203 (b : ℝ) (hb : rootInterval.Contains b) : i203.Contains (n203 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b160 b hb) (b200 b hb))
    (by norm_num [i203, i160, i200, RationalInterval.mul]) (by norm_num [i203, i160, i200, RationalInterval.mul])

def n204 (b : ℝ) : ℝ := (n160 b) * (n160 b)
def i204 : RationalInterval := ⟨(48301406875092014707513738973 / 40000000000000000000000000000 : ℚ), (241507035129483983145585729231 / 200000000000000000000000000000 : ℚ)⟩
theorem b204 (b : ℝ) (hb : rootInterval.Contains b) : i204.Contains (n204 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b160 b hb) (b160 b hb))
    (by norm_num [i204, i160, i160, RationalInterval.mul]) (by norm_num [i204, i160, i160, RationalInterval.mul])

def n205 (b : ℝ) : ℝ := (n161 b) * (n161 b)
def i205 : RationalInterval := ⟨(96709967737084164993264187439 / 1000000000000000000000000000000 : ℚ), (24177492176253530454244024143 / 250000000000000000000000000000 : ℚ)⟩
theorem b205 (b : ℝ) (hb : rootInterval.Contains b) : i205.Contains (n205 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b161 b hb) (b161 b hb))
    (by norm_num [i205, i161, i161, RationalInterval.mul]) (by norm_num [i205, i161, i161, RationalInterval.mul])

def n206 (b : ℝ) : ℝ := (n204 b) + (n205 b)
def i206 : RationalInterval := ⟨(326061284903596133170276915441 / 250000000000000000000000000000 : ℚ), (1304245144352434037544904742727 / 1000000000000000000000000000000 : ℚ)⟩
theorem b206 (b : ℝ) (hb : rootInterval.Contains b) : i206.Contains (n206 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b204 b hb) (b205 b hb))
    (by norm_num [i206, i204, i205, RationalInterval.add]) (by norm_num [i206, i204, i205, RationalInterval.add])

def n207 (b : ℝ) : ℝ := ((-41 / 10 : ℚ) : ℝ)
def i207 : RationalInterval := ⟨(-41 / 10 : ℚ), (-41 / 10 : ℚ)⟩
theorem b207 (b : ℝ) (hb : rootInterval.Contains b) : i207.Contains (n207 b) := by
  exact RationalInterval.contains_point (-41 / 10 : ℚ)

def n208 (b : ℝ) : ℝ := 1 / (n206 b)
def i208 : RationalInterval := ⟨(383363512730003807751318927459 / 500000000000000000000000000000 : ℚ), (23960219632667698720130522059 / 31250000000000000000000000000 : ℚ)⟩
theorem b208 (b : ℝ) (hb : rootInterval.Contains b) : i208.Contains (n208 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_inv_of_positive (b206 b hb) (by norm_num [i206]))
    (by norm_num [i208, i206, RationalInterval.inv]) (by norm_num [i208, i206, RationalInterval.inv])

def n209 (b : ℝ) : ℝ := (n207 b) * (n208 b)
def i209 : RationalInterval := ⟨(-3143580815806002072081124494141 / 1000000000000000000000000000000 : ℚ), (-3143580804386031223560815205163 / 1000000000000000000000000000000 : ℚ)⟩
theorem b209 (b : ℝ) (hb : rootInterval.Contains b) : i209.Contains (n209 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b207 b hb) (b208 b hb))
    (by norm_num [i209, i207, i208, RationalInterval.mul]) (by norm_num [i209, i207, i208, RationalInterval.mul])

def n210 (b : ℝ) : ℝ := (n209 b) * (n201 b)
def i210 : RationalInterval := ⟨(-304015602318281222815061084761 / 1000000000000000000000000000000 : ℚ), (-304015598171090167181267651997 / 1000000000000000000000000000000 : ℚ)⟩
theorem b210 (b : ℝ) (hb : rootInterval.Contains b) : i210.Contains (n210 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b209 b hb) (b201 b hb))
    (by norm_num [i210, i209, i201, RationalInterval.mul]) (by norm_num [i210, i209, i201, RationalInterval.mul])

def n211 (b : ℝ) : ℝ := (n209 b) * (n202 b)
def i211 : RationalInterval := ⟨(-134282729226210685066719959941 / 125000000000000000000000000000 : ℚ), (-1074261822854187343377343754867 / 1000000000000000000000000000000 : ℚ)⟩
theorem b211 (b : ℝ) (hb : rootInterval.Contains b) : i211.Contains (n211 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b209 b hb) (b202 b hb))
    (by norm_num [i211, i209, i202, RationalInterval.mul]) (by norm_num [i211, i209, i202, RationalInterval.mul])

def n212 (b : ℝ) : ℝ := (n209 b) * (n203 b)
def i212 : RationalInterval := ⟨(-134282729226210685066719959941 / 125000000000000000000000000000 : ℚ), (-1074261822854187343377343754867 / 1000000000000000000000000000000 : ℚ)⟩
theorem b212 (b : ℝ) (hb : rootInterval.Contains b) : i212.Contains (n212 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b209 b hb) (b203 b hb))
    (by norm_num [i212, i209, i203, RationalInterval.mul]) (by norm_num [i212, i209, i203, RationalInterval.mul])

def n213 (b : ℝ) : ℝ := (n209 b) * (n204 b)
def i213 : RationalInterval := ⟨(-759196882515232061002779665111 / 200000000000000000000000000000 : ℚ), (-3795984386934468359098160162079 / 1000000000000000000000000000000 : ℚ)⟩
theorem b213 (b : ℝ) (hb : rootInterval.Contains b) : i213.Contains (n213 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b209 b hb) (b204 b hb))
    (by norm_num [i213, i209, i204, RationalInterval.mul]) (by norm_num [i213, i209, i204, RationalInterval.mul])

def n214 (b : ℝ) : ℝ := -(n169 b)
def i214 : RationalInterval := ⟨(-206872634346103321002246813219 / 250000000000000000000000000000 : ℚ), (-103436317035132442805331754773 / 125000000000000000000000000000 : ℚ)⟩
theorem b214 (b : ℝ) (hb : rootInterval.Contains b) : i214.Contains (n214 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b169 b hb))
    (by norm_num [i214, i169, RationalInterval.neg]) (by norm_num [i214, i169, RationalInterval.neg])

def n215 (b : ℝ) : ℝ := (n214 b) * (n214 b)
def i215 : RationalInterval := ⟨(171185146908678879731641886259 / 250000000000000000000000000000 : ℚ), (34237029473037253938841716117 / 50000000000000000000000000000 : ℚ)⟩
theorem b215 (b : ℝ) (hb : rootInterval.Contains b) : i215.Contains (n215 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b214 b hb) (b214 b hb))
    (by norm_num [i215, i214, i214, RationalInterval.mul]) (by norm_num [i215, i214, i214, RationalInterval.mul])

def n216 (b : ℝ) : ℝ := (n214 b) * (n168 b)
def i216 : RationalInterval := ⟨(171392597948110017232588027861 / 1000000000000000000000000000000 : ℚ), (8569629955674636879829890571 / 50000000000000000000000000000 : ℚ)⟩
theorem b216 (b : ℝ) (hb : rootInterval.Contains b) : i216.Contains (n216 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b214 b hb) (b168 b hb))
    (by norm_num [i216, i214, i168, RationalInterval.mul]) (by norm_num [i216, i214, i168, RationalInterval.mul])

def n217 (b : ℝ) : ℝ := (n168 b) * (n214 b)
def i217 : RationalInterval := ⟨(171392597948110017232588027861 / 1000000000000000000000000000000 : ℚ), (8569629955674636879829890571 / 50000000000000000000000000000 : ℚ)⟩
theorem b217 (b : ℝ) (hb : rootInterval.Contains b) : i217.Contains (n217 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b168 b hb) (b214 b hb))
    (by norm_num [i217, i168, i214, RationalInterval.mul]) (by norm_num [i217, i168, i214, RationalInterval.mul])

def n218 (b : ℝ) : ℝ := (n168 b) * (n168 b)
def i218 : RationalInterval := ⟨(10725018774216878231519104519 / 250000000000000000000000000000 : ℚ), (8580015113172276938111369193 / 200000000000000000000000000000 : ℚ)⟩
theorem b218 (b : ℝ) (hb : rootInterval.Contains b) : i218.Contains (n218 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b168 b hb) (b168 b hb))
    (by norm_num [i218, i168, i168, RationalInterval.mul]) (by norm_num [i218, i168, i168, RationalInterval.mul])

def n219 (b : ℝ) : ℝ := (n169 b) * (n169 b)
def i219 : RationalInterval := ⟨(171185146908678879731641886259 / 250000000000000000000000000000 : ℚ), (34237029473037253938841716117 / 50000000000000000000000000000 : ℚ)⟩
theorem b219 (b : ℝ) (hb : rootInterval.Contains b) : i219.Contains (n219 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b169 b hb) (b169 b hb))
    (by norm_num [i219, i169, i169, RationalInterval.mul]) (by norm_num [i219, i169, i169, RationalInterval.mul])

def n220 (b : ℝ) : ℝ := (n218 b) + (n219 b)
def i220 : RationalInterval := ⟨(90955082841447878981580495389 / 125000000000000000000000000000 : ℚ), (145528133005321292693478233661 / 200000000000000000000000000000 : ℚ)⟩
theorem b220 (b : ℝ) (hb : rootInterval.Contains b) : i220.Contains (n220 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b218 b hb) (b219 b hb))
    (by norm_num [i220, i218, i219, RationalInterval.add]) (by norm_num [i220, i218, i219, RationalInterval.add])

def n221 (b : ℝ) : ℝ := ((1 / 5 : ℚ) : ℝ)
def i221 : RationalInterval := ⟨(1 / 5 : ℚ), (1 / 5 : ℚ)⟩
theorem b221 (b : ℝ) (hb : rootInterval.Contains b) : i221.Contains (n221 b) := by
  exact RationalInterval.contains_point (1 / 5 : ℚ)

def n222 (b : ℝ) : ℝ := 1 / (n220 b)
def i222 : RationalInterval := ⟨(137430471943652930899518749913 / 100000000000000000000000000000 : ℚ), (1374304723771170973254483079957 / 1000000000000000000000000000000 : ℚ)⟩
theorem b222 (b : ℝ) (hb : rootInterval.Contains b) : i222.Contains (n222 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_inv_of_positive (b220 b hb) (by norm_num [i220]))
    (by norm_num [i222, i220, RationalInterval.inv]) (by norm_num [i222, i220, RationalInterval.inv])

def n223 (b : ℝ) : ℝ := (n221 b) * (n222 b)
def i223 : RationalInterval := ⟨(137430471943652930899518749913 / 500000000000000000000000000000 : ℚ), (34357618094279274331362076999 / 125000000000000000000000000000 : ℚ)⟩
theorem b223 (b : ℝ) (hb : rootInterval.Contains b) : i223.Contains (n223 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b221 b hb) (b222 b hb))
    (by norm_num [i223, i221, i222, RationalInterval.mul]) (by norm_num [i223, i221, i222, RationalInterval.mul])

def n224 (b : ℝ) : ℝ := (n223 b) * (n215 b)
def i224 : RationalInterval := ⟨(94104222117613192144445658683 / 500000000000000000000000000000 : ℚ), (94104222665375805166330169407 / 500000000000000000000000000000 : ℚ)⟩
theorem b224 (b : ℝ) (hb : rootInterval.Contains b) : i224.Contains (n224 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b223 b hb) (b215 b hb))
    (by norm_num [i224, i223, i215, RationalInterval.mul]) (by norm_num [i224, i223, i215, RationalInterval.mul])

def n225 (b : ℝ) : ℝ := (n223 b) * (n216 b)
def i225 : RationalInterval := ⟨(2944320702957190077038693799 / 62500000000000000000000000000 : ℚ), (47109131716218335954434337871 / 1000000000000000000000000000000 : ℚ)⟩
theorem b225 (b : ℝ) (hb : rootInterval.Contains b) : i225.Contains (n225 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b223 b hb) (b216 b hb))
    (by norm_num [i225, i223, i216, RationalInterval.mul]) (by norm_num [i225, i223, i216, RationalInterval.mul])

def n226 (b : ℝ) : ℝ := (n223 b) * (n217 b)
def i226 : RationalInterval := ⟨(2944320702957190077038693799 / 62500000000000000000000000000 : ℚ), (47109131716218335954434337871 / 1000000000000000000000000000000 : ℚ)⟩
theorem b226 (b : ℝ) (hb : rootInterval.Contains b) : i226.Contains (n226 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b223 b hb) (b217 b hb))
    (by norm_num [i226, i223, i217, RationalInterval.mul]) (by norm_num [i226, i223, i217, RationalInterval.mul])

def n227 (b : ℝ) : ℝ := (n223 b) * (n218 b)
def i227 : RationalInterval := ⟨(11791555133961309053995509269 / 1000000000000000000000000000000 : ℚ), (5895777650030349157036835989 / 500000000000000000000000000000 : ℚ)⟩
theorem b227 (b : ℝ) (hb : rootInterval.Contains b) : i227.Contains (n227 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b223 b hb) (b218 b hb))
    (by norm_num [i227, i223, i218, RationalInterval.mul]) (by norm_num [i227, i223, i218, RationalInterval.mul])

def n228 (b : ℝ) : ℝ := ((81 / 64 : ℚ) : ℝ)
def i228 : RationalInterval := ⟨(81 / 64 : ℚ), (81 / 64 : ℚ)⟩
theorem b228 (b : ℝ) (hb : rootInterval.Contains b) : i228.Contains (n228 b) := by
  exact RationalInterval.contains_point (81 / 64 : ℚ)

def n229 (b : ℝ) : ℝ := (n182 b) * (n228 b)
def i229 : RationalInterval := ⟨(189998027585888462828599907031 / 125000000000000000000000000000 : ℚ), (47499506925377950827228785271 / 31250000000000000000000000000 : ℚ)⟩
theorem b229 (b : ℝ) (hb : rootInterval.Contains b) : i229.Contains (n229 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b182 b hb) (b228 b hb))
    (by norm_num [i229, i182, i228, RationalInterval.mul]) (by norm_num [i229, i182, i228, RationalInterval.mul])

def n230 (b : ℝ) : ℝ := (n183 b) * (n228 b)
def i230 : RationalInterval := ⟨(-579813553083157340633293383763 / 500000000000000000000000000000 : ℚ), (-1159627105214509310892018009477 / 1000000000000000000000000000000 : ℚ)⟩
theorem b230 (b : ℝ) (hb : rootInterval.Contains b) : i230.Contains (n230 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b183 b hb) (b228 b hb))
    (by norm_num [i230, i183, i228, RationalInterval.mul]) (by norm_num [i230, i183, i228, RationalInterval.mul])

def n231 (b : ℝ) : ℝ := (n184 b) * (n228 b)
def i231 : RationalInterval := ⟨(-579813553083157340633293383763 / 500000000000000000000000000000 : ℚ), (-1159627105214509310892018009477 / 1000000000000000000000000000000 : ℚ)⟩
theorem b231 (b : ℝ) (hb : rootInterval.Contains b) : i231.Contains (n231 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b184 b hb) (b228 b hb))
    (by norm_num [i231, i184, i228, RationalInterval.mul]) (by norm_num [i231, i184, i228, RationalInterval.mul])

def n232 (b : ℝ) : ℝ := (n185 b) * (n228 b)
def i232 : RationalInterval := ⟨(884703278393440301828555882783 / 1000000000000000000000000000000 : ℚ), (863968046198591376389534909 / 976562500000000000000000000 : ℚ)⟩
theorem b232 (b : ℝ) (hb : rootInterval.Contains b) : i232.Contains (n232 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b185 b hb) (b228 b hb))
    (by norm_num [i232, i185, i228, RationalInterval.mul]) (by norm_num [i232, i185, i228, RationalInterval.mul])

def n233 (b : ℝ) : ℝ := ((32 / 81 : ℚ) : ℝ)
def i233 : RationalInterval := ⟨(32 / 81 : ℚ), (32 / 81 : ℚ)⟩
theorem b233 (b : ℝ) (hb : rootInterval.Contains b) : i233.Contains (n233 b) := by
  exact RationalInterval.contains_point (32 / 81 : ℚ)

def n234 (b : ℝ) : ℝ := (n21 b) * (n160 b)
def i234 : RationalInterval := ⟨(229419533759662043926531105001 / 200000000000000000000000000000 : ℚ), (35846802218796905051741209467 / 31250000000000000000000000000 : ℚ)⟩
theorem b234 (b : ℝ) (hb : rootInterval.Contains b) : i234.Contains (n234 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b21 b hb) (b160 b hb))
    (by norm_num [i234, i21, i160, RationalInterval.mul]) (by norm_num [i234, i21, i160, RationalInterval.mul])

def n235 (b : ℝ) : ℝ := (n55 b) * (n161 b)
def i235 : RationalInterval := ⟨(25285741787717014637108868157 / 1000000000000000000000000000000 : ℚ), (25285742088917108420825588211 / 1000000000000000000000000000000 : ℚ)⟩
theorem b235 (b : ℝ) (hb : rootInterval.Contains b) : i235.Contains (n235 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b55 b hb) (b161 b hb))
    (by norm_num [i235, i55, i161, RationalInterval.mul]) (by norm_num [i235, i55, i161, RationalInterval.mul])

def n236 (b : ℝ) : ℝ := (n234 b) + (n235 b)
def i236 : RationalInterval := ⟨(586191705293013617134882196581 / 500000000000000000000000000000 : ℚ), (234476682618083614015308858231 / 200000000000000000000000000000 : ℚ)⟩
theorem b236 (b : ℝ) (hb : rootInterval.Contains b) : i236.Contains (n236 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b234 b hb) (b235 b hb))
    (by norm_num [i236, i234, i235, RationalInterval.add]) (by norm_num [i236, i234, i235, RationalInterval.add])

def n237 (b : ℝ) : ℝ := (n34 b) * (n168 b)
def i237 : RationalInterval := ⟨(228459463439043705909539525067 / 1000000000000000000000000000000 : ℚ), (228459464754487363029181006361 / 1000000000000000000000000000000 : ℚ)⟩
theorem b237 (b : ℝ) (hb : rootInterval.Contains b) : i237.Contains (n237 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b34 b hb) (b168 b hb))
    (by norm_num [i237, i34, i168, RationalInterval.mul]) (by norm_num [i237, i34, i168, RationalInterval.mul])

def n238 (b : ℝ) : ℝ := (n56 b) * (n169 b)
def i238 : RationalInterval := ⟨(431900336537741649702080453207 / 500000000000000000000000000000 : ℚ), (431900337268930761140311941303 / 500000000000000000000000000000 : ℚ)⟩
theorem b238 (b : ℝ) (hb : rootInterval.Contains b) : i238.Contains (n238 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b56 b hb) (b169 b hb))
    (by norm_num [i238, i56, i169, RationalInterval.mul]) (by norm_num [i238, i56, i169, RationalInterval.mul])

def n239 (b : ℝ) : ℝ := (n237 b) + (n238 b)
def i239 : RationalInterval := ⟨(1092260136514527005313700431481 / 1000000000000000000000000000000 : ℚ), (1092260139292348885309804888967 / 1000000000000000000000000000000 : ℚ)⟩
theorem b239 (b : ℝ) (hb : rootInterval.Contains b) : i239.Contains (n239 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b237 b hb) (b238 b hb))
    (by norm_num [i239, i237, i238, RationalInterval.add]) (by norm_num [i239, i237, i238, RationalInterval.add])

def n240 (b : ℝ) : ℝ := ((20 : ℚ) : ℝ)
def i240 : RationalInterval := ⟨(20 : ℚ), (20 : ℚ)⟩
theorem b240 (b : ℝ) (hb : rootInterval.Contains b) : i240.Contains (n240 b) := by
  exact RationalInterval.contains_point (20 : ℚ)

def n241 (b : ℝ) : ℝ := ((1 / 20 : ℚ) : ℝ)
def i241 : RationalInterval := ⟨(1 / 20 : ℚ), (1 / 20 : ℚ)⟩
theorem b241 (b : ℝ) (hb : rootInterval.Contains b) : i241.Contains (n241 b) := by
  exact RationalInterval.contains_point (1 / 20 : ℚ)

def n242 (b : ℝ) : ℝ := (n150 b) * (n241 b)
def i242 : RationalInterval := ⟨(8643963275189851117057517647 / 100000000000000000000000000000 : ℚ), (5402477047604655518421886489 / 62500000000000000000000000000 : ℚ)⟩
theorem b242 (b : ℝ) (hb : rootInterval.Contains b) : i242.Contains (n242 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b150 b hb) (b241 b hb))
    (by norm_num [i242, i150, i241, RationalInterval.mul]) (by norm_num [i242, i150, i241, RationalInterval.mul])

def n243 (b : ℝ) : ℝ := -(n242 b)
def i243 : RationalInterval := ⟨(-5402477047604655518421886489 / 62500000000000000000000000000 : ℚ), (-8643963275189851117057517647 / 100000000000000000000000000000 : ℚ)⟩
theorem b243 (b : ℝ) (hb : rootInterval.Contains b) : i243.Contains (n243 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b242 b hb))
    (by norm_num [i243, i242, RationalInterval.neg]) (by norm_num [i243, i242, RationalInterval.neg])

def n244 (b : ℝ) : ℝ := (n136 b) + (n243 b)
def i244 : RationalInterval := ⟨(246498341067145956519000141653 / 200000000000000000000000000000 : ℚ), (77030731610912230357682847277 / 62500000000000000000000000000 : ℚ)⟩
theorem b244 (b : ℝ) (hb : rootInterval.Contains b) : i244.Contains (n244 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b136 b hb) (b243 b hb))
    (by norm_num [i244, i136, i243, RationalInterval.add]) (by norm_num [i244, i136, i243, RationalInterval.add])

def n245 (b : ℝ) : ℝ := 1 / (n244 b)
def i245 : RationalInterval := ⟨(202841121630818718003111126249 / 250000000000000000000000000000 : ℚ), (405682243406092853678573266021 / 500000000000000000000000000000 : ℚ)⟩
theorem b245 (b : ℝ) (hb : rootInterval.Contains b) : i245.Contains (n245 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_inv_of_positive (b244 b hb) (by norm_num [i244]))
    (by norm_num [i245, i244, RationalInterval.inv]) (by norm_num [i245, i244, RationalInterval.inv])

def n246 (b : ℝ) : ℝ := (n150 b) * (n245 b)
def i246 : RationalInterval := ⟨(280536192972018355220525544051 / 200000000000000000000000000000 : ℚ), (350670241379549079864077856239 / 250000000000000000000000000000 : ℚ)⟩
theorem b246 (b : ℝ) (hb : rootInterval.Contains b) : i246.Contains (n246 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b150 b hb) (b245 b hb))
    (by norm_num [i246, i150, i245, RationalInterval.mul]) (by norm_num [i246, i150, i245, RationalInterval.mul])

def n247 (b : ℝ) : ℝ := (n136 b) * (n245 b)
def i247 : RationalInterval := ⟨(267533511973714065330197221559 / 250000000000000000000000000000 : ℚ), (66883378039003633973820424999 / 62500000000000000000000000000 : ℚ)⟩
theorem b247 (b : ℝ) (hb : rootInterval.Contains b) : i247.Contains (n247 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b136 b hb) (b245 b hb))
    (by norm_num [i247, i136, i245, RationalInterval.mul]) (by norm_num [i247, i136, i245, RationalInterval.mul])

def n248 (b : ℝ) : ℝ := (n182 b) * (n241 b)
def i248 : RationalInterval := ⟨(60048759335786970968051328641 / 1000000000000000000000000000000 : ℚ), (15012189843082414088605640777 / 250000000000000000000000000000 : ℚ)⟩
theorem b248 (b : ℝ) (hb : rootInterval.Contains b) : i248.Contains (n248 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b182 b hb) (b241 b hb))
    (by norm_num [i248, i182, i241, RationalInterval.mul]) (by norm_num [i248, i182, i241, RationalInterval.mul])

def n249 (b : ℝ) : ℝ := (n248 b) + (n183 b)
def i249 : RationalInterval := ⟨(-428099909187934536744749354949 / 500000000000000000000000000000 : ℚ), (-42809990879364131933568472219 / 50000000000000000000000000000 : ℚ)⟩
theorem b249 (b : ℝ) (hb : rootInterval.Contains b) : i249.Contains (n249 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b248 b hb) (b183 b hb))
    (by norm_num [i249, i248, i183, RationalInterval.add]) (by norm_num [i249, i248, i183, RationalInterval.add])

def n250 (b : ℝ) : ℝ := (n184 b) * (n241 b)
def i250 : RationalInterval := ⟨(-45812428885582802222877501927 / 1000000000000000000000000000000 : ℚ), (-22906214423990307375644800187 / 500000000000000000000000000000 : ℚ)⟩
theorem b250 (b : ℝ) (hb : rootInterval.Contains b) : i250.Contains (n250 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b184 b hb) (b241 b hb))
    (by norm_num [i250, i184, i241, RationalInterval.mul]) (by norm_num [i250, i184, i241, RationalInterval.mul])

def n251 (b : ℝ) : ℝ := (n250 b) + (n185 b)
def i251 : RationalInterval := ⟨(130642476734439437869072836647 / 200000000000000000000000000000 : ℚ), (326606192215953423754383346703 / 500000000000000000000000000000 : ℚ)⟩
theorem b251 (b : ℝ) (hb : rootInterval.Contains b) : i251.Contains (n251 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b250 b hb) (b185 b hb))
    (by norm_num [i251, i250, i185, RationalInterval.add]) (by norm_num [i251, i250, i185, RationalInterval.add])

def n252 (b : ℝ) : ℝ := (n249 b) * (n241 b)
def i252 : RationalInterval := ⟨(-8561998183758690734894987099 / 200000000000000000000000000000 : ℚ), (-42809990879364131933568472219 / 1000000000000000000000000000000 : ℚ)⟩
theorem b252 (b : ℝ) (hb : rootInterval.Contains b) : i252.Contains (n252 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b249 b hb) (b241 b hb))
    (by norm_num [i252, i249, i241, RationalInterval.mul]) (by norm_num [i252, i249, i241, RationalInterval.mul])

def n253 (b : ℝ) : ℝ := (n252 b) + (n251 b)
def i253 : RationalInterval := ⟨(30520119637670186783544462387 / 50000000000000000000000000000 : ℚ), (610402393552542715575198221187 / 1000000000000000000000000000000 : ℚ)⟩
theorem b253 (b : ℝ) (hb : rootInterval.Contains b) : i253.Contains (n253 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b252 b hb) (b251 b hb))
    (by norm_num [i253, i252, i251, RationalInterval.add]) (by norm_num [i253, i252, i251, RationalInterval.add])

def n254 (b : ℝ) : ℝ := (n244 b) * (n253 b)
def i254 : RationalInterval := ⟨(376157942992826238672476039881 / 500000000000000000000000000000 : ℚ), (752315887238469439205353009613 / 1000000000000000000000000000000 : ℚ)⟩
theorem b254 (b : ℝ) (hb : rootInterval.Contains b) : i254.Contains (n254 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b244 b hb) (b253 b hb))
    (by norm_num [i254, i244, i253, RationalInterval.mul]) (by norm_num [i254, i244, i253, RationalInterval.mul])

def n255 (b : ℝ) : ℝ := (n153 b) * (n241 b)
def i255 : RationalInterval := ⟨(6143963275189851117057517647 / 100000000000000000000000000000 : ℚ), (3839977047604655518421886489 / 62500000000000000000000000000 : ℚ)⟩
theorem b255 (b : ℝ) (hb : rootInterval.Contains b) : i255.Contains (n255 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b153 b hb) (b241 b hb))
    (by norm_num [i255, i153, i241, RationalInterval.mul]) (by norm_num [i255, i153, i241, RationalInterval.mul])

def n256 (b : ℝ) : ℝ := -(n255 b)
def i256 : RationalInterval := ⟨(-3839977047604655518421886489 / 62500000000000000000000000000 : ℚ), (-6143963275189851117057517647 / 100000000000000000000000000000 : ℚ)⟩
theorem b256 (b : ℝ) (hb : rootInterval.Contains b) : i256.Contains (n256 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b255 b hb))
    (by norm_num [i256, i255, RationalInterval.neg]) (by norm_num [i256, i255, RationalInterval.neg])

def n257 (b : ℝ) : ℝ := (n151 b) + (n256 b)
def i257 : RationalInterval := ⟨(51498341067145956519000141653 / 200000000000000000000000000000 : ℚ), (16093231610912230357682847277 / 62500000000000000000000000000 : ℚ)⟩
theorem b257 (b : ℝ) (hb : rootInterval.Contains b) : i257.Contains (n257 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b151 b hb) (b256 b hb))
    (by norm_num [i257, i151, i256, RationalInterval.add]) (by norm_num [i257, i151, i256, RationalInterval.add])

def n258 (b : ℝ) : ℝ := 1 / (n257 b)
def i258 : RationalInterval := ⟨(31068961914459015839637089053 / 8000000000000000000000000000 : ℚ), (970905061481643669990774943343 / 250000000000000000000000000000 : ℚ)⟩
theorem b258 (b : ℝ) (hb : rootInterval.Contains b) : i258.Contains (n258 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_inv_of_positive (b257 b hb) (by norm_num [i257]))
    (by norm_num [i258, i257, RationalInterval.inv]) (by norm_num [i258, i257, RationalInterval.inv])

def n259 (b : ℝ) : ℝ := (n153 b) * (n258 b)
def i259 : RationalInterval := ⟨(4772164025017709048416277016579 / 1000000000000000000000000000000 : ℚ), (4772164033910654218094125199953 / 1000000000000000000000000000000 : ℚ)⟩
theorem b259 (b : ℝ) (hb : rootInterval.Contains b) : i259.Contains (n259 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b153 b hb) (b258 b hb))
    (by norm_num [i259, i153, i258, RationalInterval.mul]) (by norm_num [i259, i153, i258, RationalInterval.mul])

def n260 (b : ℝ) : ℝ := (n196 b) * (n241 b)
def i260 : RationalInterval := ⟨(74950899350322924939395311637 / 1000000000000000000000000000000 : ℚ), (37475449704624747910776838343 / 500000000000000000000000000000 : ℚ)⟩
theorem b260 (b : ℝ) (hb : rootInterval.Contains b) : i260.Contains (n260 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b196 b hb) (b241 b hb))
    (by norm_num [i260, i196, i241, RationalInterval.mul]) (by norm_num [i260, i196, i241, RationalInterval.mul])

def n261 (b : ℝ) : ℝ := (n260 b) + (n197 b)
def i261 : RationalInterval := ⟨(-314117029572386918033112081887 / 1000000000000000000000000000000 : ℚ), (-314117028746029216827145987477 / 1000000000000000000000000000000 : ℚ)⟩
theorem b261 (b : ℝ) (hb : rootInterval.Contains b) : i261.Contains (n261 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b260 b hb) (b197 b hb))
    (by norm_num [i261, i260, i197, RationalInterval.add]) (by norm_num [i261, i260, i197, RationalInterval.add])

def n262 (b : ℝ) : ℝ := (n198 b) * (n241 b)
def i262 : RationalInterval := ⟨(-19453396446135492148625369677 / 1000000000000000000000000000000 : ℚ), (-2431674550970491954054372901 / 125000000000000000000000000000 : ℚ)⟩
theorem b262 (b : ℝ) (hb : rootInterval.Contains b) : i262.Contains (n262 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b198 b hb) (b241 b hb))
    (by norm_num [i262, i198, i241, RationalInterval.mul]) (by norm_num [i262, i198, i241, RationalInterval.mul])

def n263 (b : ℝ) : ℝ := (n262 b) + (n199 b)
def i263 : RationalInterval := ⟨(81528615798650817947800534199 / 1000000000000000000000000000000 : ℚ), (2038215403900033485063895169 / 25000000000000000000000000000 : ℚ)⟩
theorem b263 (b : ℝ) (hb : rootInterval.Contains b) : i263.Contains (n263 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b262 b hb) (b199 b hb))
    (by norm_num [i263, i262, i199, RationalInterval.add]) (by norm_num [i263, i262, i199, RationalInterval.add])

def n264 (b : ℝ) : ℝ := (n261 b) * (n241 b)
def i264 : RationalInterval := ⟨(-3141170295723869180331120819 / 200000000000000000000000000000 : ℚ), (-15705851437301460841357299373 / 1000000000000000000000000000000 : ℚ)⟩
theorem b264 (b : ℝ) (hb : rootInterval.Contains b) : i264.Contains (n264 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b261 b hb) (b241 b hb))
    (by norm_num [i264, i261, i241, RationalInterval.mul]) (by norm_num [i264, i261, i241, RationalInterval.mul])

def n265 (b : ℝ) : ℝ := (n264 b) + (n263 b)
def i265 : RationalInterval := ⟨(8227845540003934005768116263 / 125000000000000000000000000000 : ℚ), (65822764718699878561198507387 / 1000000000000000000000000000000 : ℚ)⟩
theorem b265 (b : ℝ) (hb : rootInterval.Contains b) : i265.Contains (n265 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b264 b hb) (b263 b hb))
    (by norm_num [i265, i264, i263, RationalInterval.add]) (by norm_num [i265, i264, i263, RationalInterval.add])

def n266 (b : ℝ) : ℝ := (n257 b) * (n265 b)
def i266 : RationalInterval := ⟨(16948815834676731745787832463 / 1000000000000000000000000000000 : ℚ), (3389763193243581337495214813 / 200000000000000000000000000000 : ℚ)⟩
theorem b266 (b : ℝ) (hb : rootInterval.Contains b) : i266.Contains (n266 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b257 b hb) (b265 b hb))
    (by norm_num [i266, i257, i265, RationalInterval.mul]) (by norm_num [i266, i257, i265, RationalInterval.mul])

def n267 (b : ℝ) : ℝ := (n161 b) * (n241 b)
def i267 : RationalInterval := ⟨(7774556568427398298441929083 / 500000000000000000000000000000 : ℚ), (1943639151833388576813323373 / 125000000000000000000000000000 : ℚ)⟩
theorem b267 (b : ℝ) (hb : rootInterval.Contains b) : i267.Contains (n267 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b161 b hb) (b241 b hb))
    (by norm_num [i267, i161, i241, RationalInterval.mul]) (by norm_num [i267, i161, i241, RationalInterval.mul])

def n268 (b : ℝ) : ℝ := -(n267 b)
def i268 : RationalInterval := ⟨(-1943639151833388576813323373 / 125000000000000000000000000000 : ℚ), (-7774556568427398298441929083 / 500000000000000000000000000000 : ℚ)⟩
theorem b268 (b : ℝ) (hb : rootInterval.Contains b) : i268.Contains (n268 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b267 b hb))
    (by norm_num [i268, i267, RationalInterval.neg]) (by norm_num [i268, i267, RationalInterval.neg])

def n269 (b : ℝ) : ℝ := (n160 b) + (n268 b)
def i269 : RationalInterval := ⟨(-1114428167363675772722560949887 / 1000000000000000000000000000000 : ℚ), (-27860704139260616301564707769 / 25000000000000000000000000000 : ℚ)⟩
theorem b269 (b : ℝ) (hb : rootInterval.Contains b) : i269.Contains (n269 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b160 b hb) (b268 b hb))
    (by norm_num [i269, i160, i268, RationalInterval.add]) (by norm_num [i269, i160, i268, RationalInterval.add])

