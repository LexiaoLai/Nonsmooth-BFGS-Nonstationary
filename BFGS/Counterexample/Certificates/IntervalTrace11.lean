import BFGS.Counterexample.Certificates.IntervalTrace10

/-! Generated arithmetic proofs. Each bound is checked by the Lean kernel. -/
namespace BFGS.Counterexample.Trace
noncomputable section
open BFGS RationalInterval
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false

def n990 (b : ℝ) : ℝ := (n910 b) * (n931 b)
def i990 : RationalInterval := ⟨(1353204691320640789594029732377 / 200000000000000000000000000000 : ℚ), (3383011734405939142750133375229 / 500000000000000000000000000000 : ℚ)⟩
theorem b990 (b : ℝ) (hb : rootInterval.Contains b) : i990.Contains (n990 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b910 b hb) (b931 b hb))
    (by norm_num [i990, i910, i931, RationalInterval.mul]) (by norm_num [i990, i910, i931, RationalInterval.mul])

def n991 (b : ℝ) : ℝ := (n910 b) * (n934 b)
def i991 : RationalInterval := ⟨(2053985771888932759155375587583 / 500000000000000000000000000000 : ℚ), (2053985775613634449761994361001 / 500000000000000000000000000000 : ℚ)⟩
theorem b991 (b : ℝ) (hb : rootInterval.Contains b) : i991.Contains (n991 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b910 b hb) (b934 b hb))
    (by norm_num [i991, i910, i934, RationalInterval.mul]) (by norm_num [i991, i910, i934, RationalInterval.mul])

def n992 (b : ℝ) : ℝ := (n302 b) * (n956 b)
def i992 : RationalInterval := ⟨(-22283917698616593758212187897189 / 1000000000000000000000000000000 : ℚ), (-11141958710157069003124733088293 / 500000000000000000000000000000 : ℚ)⟩
theorem b992 (b : ℝ) (hb : rootInterval.Contains b) : i992.Contains (n992 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b302 b hb) (b956 b hb))
    (by norm_num [i992, i302, i956, RationalInterval.mul]) (by norm_num [i992, i302, i956, RationalInterval.mul])

def n993 (b : ℝ) : ℝ := (n302 b) * (n959 b)
def i993 : RationalInterval := ⟨(-14210038767771496228543644212169 / 1000000000000000000000000000000 : ℚ), (-14210038594441322186135619964241 / 1000000000000000000000000000000 : ℚ)⟩
theorem b993 (b : ℝ) (hb : rootInterval.Contains b) : i993.Contains (n993 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b302 b hb) (b959 b hb))
    (by norm_num [i993, i302, i959, RationalInterval.mul]) (by norm_num [i993, i302, i959, RationalInterval.mul])

def n994 (b : ℝ) : ℝ := (n303 b) * (n956 b)
def i994 : RationalInterval := ⟨(-3606337517152387874518241047363 / 250000000000000000000000000000 : ℚ), (-14425349888396828350491939069699 / 1000000000000000000000000000000 : ℚ)⟩
theorem b994 (b : ℝ) (hb : rootInterval.Contains b) : i994.Contains (n994 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b303 b hb) (b956 b hb))
    (by norm_num [i994, i303, i956, RationalInterval.mul]) (by norm_num [i994, i303, i956, RationalInterval.mul])

def n995 (b : ℝ) : ℝ := (n303 b) * (n959 b)
def i995 : RationalInterval := ⟨(-9198776736028897867491617494867 / 1000000000000000000000000000000 : ℚ), (-9198776623789385109275410767953 / 1000000000000000000000000000000 : ℚ)⟩
theorem b995 (b : ℝ) (hb : rootInterval.Contains b) : i995.Contains (n995 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b303 b hb) (b959 b hb))
    (by norm_num [i995, i303, i959, RationalInterval.mul]) (by norm_num [i995, i303, i959, RationalInterval.mul])

def n996 (b : ℝ) : ℝ := (n988 b) + (n992 b)
def i996 : RationalInterval := ⟨(-5263186936225043002934227950583 / 500000000000000000000000000000 : ℚ), (-105263735737128519541635525349 / 10000000000000000000000000000 : ℚ)⟩
theorem b996 (b : ℝ) (hb : rootInterval.Contains b) : i996.Contains (n996 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b988 b hb) (b992 b hb))
    (by norm_num [i996, i988, i992, RationalInterval.add]) (by norm_num [i996, i988, i992, RationalInterval.add])

def n997 (b : ℝ) : ℝ := (n989 b) + (n993 b)
def i997 : RationalInterval := ⟨(-56571840717076162095162913909 / 8000000000000000000000000000 : ℚ), (-28285919615332936860521356703 / 4000000000000000000000000000 : ℚ)⟩
theorem b997 (b : ℝ) (hb : rootInterval.Contains b) : i997.Contains (n997 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b989 b hb) (b993 b hb))
    (by norm_num [i997, i989, i993, RationalInterval.add]) (by norm_num [i997, i989, i993, RationalInterval.add])

def n998 (b : ℝ) : ℝ := (n990 b) + (n994 b)
def i998 : RationalInterval := ⟨(-7659326612006347550102815527567 / 1000000000000000000000000000000 : ℚ), (-7659326419584950064991672319241 / 1000000000000000000000000000000 : ℚ)⟩
theorem b998 (b : ℝ) (hb : rootInterval.Contains b) : i998.Contains (n998 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b990 b hb) (b994 b hb))
    (by norm_num [i998, i990, i994, RationalInterval.add]) (by norm_num [i998, i990, i994, RationalInterval.add])

def n999 (b : ℝ) : ℝ := (n991 b) + (n995 b)
def i999 : RationalInterval := ⟨(-5090805192251032349180866319701 / 1000000000000000000000000000000 : ℚ), (-5090805072562116209751422045951 / 1000000000000000000000000000000 : ℚ)⟩
theorem b999 (b : ℝ) (hb : rootInterval.Contains b) : i999.Contains (n999 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b991 b hb) (b995 b hb))
    (by norm_num [i999, i991, i995, RationalInterval.add]) (by norm_num [i999, i991, i995, RationalInterval.add])

def n1000 (b : ℝ) : ℝ := (n984 b) + (n996 b)
def i1000 : RationalInterval := ⟨(-5263186936225043002934227950583 / 250000000000000000000000000000 : ℚ), (-105263735737128519541635525349 / 5000000000000000000000000000 : ℚ)⟩
theorem b1000 (b : ℝ) (hb : rootInterval.Contains b) : i1000.Contains (n1000 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b984 b hb) (b996 b hb))
    (by norm_num [i1000, i984, i996, RationalInterval.add]) (by norm_num [i1000, i984, i996, RationalInterval.add])

def n1001 (b : ℝ) : ℝ := (n985 b) + (n997 b)
def i1001 : RationalInterval := ⟨(-920675418852554238249886235387 / 62500000000000000000000000000 : ℚ), (-14730806323418184280122011494991 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1001 (b : ℝ) (hb : rootInterval.Contains b) : i1001.Contains (n1001 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b985 b hb) (b997 b hb))
    (by norm_num [i1001, i985, i997, RationalInterval.add]) (by norm_num [i1001, i985, i997, RationalInterval.add])

def n1002 (b : ℝ) : ℝ := (n986 b) + (n998 b)
def i1002 : RationalInterval := ⟨(-920675418852554238249886235387 / 62500000000000000000000000000 : ℚ), (-14730806323418184280122011494991 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1002 (b : ℝ) (hb : rootInterval.Contains b) : i1002.Contains (n1002 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b986 b hb) (b998 b hb))
    (by norm_num [i1002, i986, i998, RationalInterval.add]) (by norm_num [i1002, i986, i998, RationalInterval.add])

def n1003 (b : ℝ) : ℝ := (n987 b) + (n999 b)
def i1003 : RationalInterval := ⟨(-5090805192251032349180866319701 / 500000000000000000000000000000 : ℚ), (-5090805072562116209751422045951 / 500000000000000000000000000000 : ℚ)⟩
theorem b1003 (b : ℝ) (hb : rootInterval.Contains b) : i1003.Contains (n1003 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b987 b hb) (b999 b hb))
    (by norm_num [i1003, i987, i999, RationalInterval.add]) (by norm_num [i1003, i987, i999, RationalInterval.add])

def n1004 (b : ℝ) : ℝ := 1 / (n323 b)
def i1004 : RationalInterval := ⟨(430439371683557797297575234177 / 1000000000000000000000000000000 : ℚ), (430439371881306317683071222813 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1004 (b : ℝ) (hb : rootInterval.Contains b) : i1004.Contains (n1004 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_inv_of_positive (b323 b hb) (by norm_num [i323]))
    (by norm_num [i1004, i323, RationalInterval.inv]) (by norm_num [i1004, i323, RationalInterval.inv])

def n1005 (b : ℝ) : ℝ := (n16 b) * (n1004 b)
def i1005 : RationalInterval := ⟨(-430439371881306317683071222813 / 1000000000000000000000000000000 : ℚ), (-430439371683557797297575234177 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1005 (b : ℝ) (hb : rootInterval.Contains b) : i1005.Contains (n1005 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b16 b hb) (b1004 b hb))
    (by norm_num [i1005, i16, i1004, RationalInterval.mul]) (by norm_num [i1005, i16, i1004, RationalInterval.mul])

def n1006 (b : ℝ) : ℝ := (n1005 b) * (n1000 b)
def i1006 : RationalInterval := ⟨(906193125435073372668968531571 / 100000000000000000000000000000 : ℚ), (2265482878922604522673098301923 / 250000000000000000000000000000 : ℚ)⟩
theorem b1006 (b : ℝ) (hb : rootInterval.Contains b) : i1006.Contains (n1006 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1005 b hb) (b1000 b hb))
    (by norm_num [i1006, i1005, i1000, RationalInterval.mul]) (by norm_num [i1006, i1005, i1000, RationalInterval.mul])

def n1007 (b : ℝ) : ℝ := (n1005 b) * (n1001 b)
def i1007 : RationalInterval := ⟨(3170359509122151667175366564363 / 500000000000000000000000000000 : ℚ), (6340719183959232819614863966493 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1007 (b : ℝ) (hb : rootInterval.Contains b) : i1007.Contains (n1007 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1005 b hb) (b1001 b hb))
    (by norm_num [i1007, i1005, i1001, RationalInterval.mul]) (by norm_num [i1007, i1005, i1001, RationalInterval.mul])

def n1008 (b : ℝ) : ℝ := (n1005 b) * (n1002 b)
def i1008 : RationalInterval := ⟨(3170359509122151667175366564363 / 500000000000000000000000000000 : ℚ), (6340719183959232819614863966493 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1008 (b : ℝ) (hb : rootInterval.Contains b) : i1008.Contains (n1008 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1005 b hb) (b1002 b hb))
    (by norm_num [i1008, i1005, i1002, RationalInterval.mul]) (by norm_num [i1008, i1005, i1002, RationalInterval.mul])

def n1009 (b : ℝ) : ℝ := (n1005 b) * (n1003 b)
def i1009 : RationalInterval := ⟨(2191282936797106161626188985427 / 500000000000000000000000000000 : ℚ), (4382565978645254433013362501531 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1009 (b : ℝ) (hb : rootInterval.Contains b) : i1009.Contains (n1009 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1005 b hb) (b1003 b hb))
    (by norm_num [i1009, i1005, i1003, RationalInterval.mul]) (by norm_num [i1009, i1005, i1003, RationalInterval.mul])

def n1010 (b : ℝ) : ℝ := (n323 b) * (n323 b)
def i1010 : RationalInterval := ⟨(5397293335792659516996007694849 / 1000000000000000000000000000000 : ℚ), (21083177112311757131699221893 / 3906250000000000000000000000 : ℚ)⟩
theorem b1010 (b : ℝ) (hb : rootInterval.Contains b) : i1010.Contains (n1010 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b323 b hb) (b323 b hb))
    (by norm_num [i1010, i323, i323, RationalInterval.mul]) (by norm_num [i1010, i323, i323, RationalInterval.mul])

def n1011 (b : ℝ) : ℝ := 1 / (n1010 b)
def i1011 : RationalInterval := ⟨(37055610539067203617815765899 / 200000000000000000000000000000 : ℚ), (9263902643278675793017776729 / 50000000000000000000000000000 : ℚ)⟩
theorem b1011 (b : ℝ) (hb : rootInterval.Contains b) : i1011.Contains (n1011 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_inv_of_positive (b1010 b hb) (by norm_num [i1010]))
    (by norm_num [i1011, i1010, RationalInterval.inv]) (by norm_num [i1011, i1010, RationalInterval.inv])

def n1012 (b : ℝ) : ℝ := (n928 b) * (n1011 b)
def i1012 : RationalInterval := ⟨(-120211136212987065769929590319 / 125000000000000000000000000000 : ℚ), (-480844532306167113052345591531 / 500000000000000000000000000000 : ℚ)⟩
theorem b1012 (b : ℝ) (hb : rootInterval.Contains b) : i1012.Contains (n1012 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b928 b hb) (b1011 b hb))
    (by norm_num [i1012, i928, i1011, RationalInterval.mul]) (by norm_num [i1012, i928, i1011, RationalInterval.mul])

def n1013 (b : ℝ) : ℝ := (n1012 b) * (n946 b)
def i1013 : RationalInterval := ⟨(-10434626864130929253969629954899 / 1000000000000000000000000000000 : ℚ), (-5217313293553051778576546357499 / 500000000000000000000000000000 : ℚ)⟩
theorem b1013 (b : ℝ) (hb : rootInterval.Contains b) : i1013.Contains (n1013 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1012 b hb) (b946 b hb))
    (by norm_num [i1013, i1012, i946, RationalInterval.mul]) (by norm_num [i1013, i1012, i946, RationalInterval.mul])

def n1014 (b : ℝ) : ℝ := (n1012 b) * (n947 b)
def i1014 : RationalInterval := ⟨(-3272535430691862249769718072277 / 500000000000000000000000000000 : ℚ), (-818133835947466969688532524089 / 125000000000000000000000000000 : ℚ)⟩
theorem b1014 (b : ℝ) (hb : rootInterval.Contains b) : i1014.Contains (n1014 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1012 b hb) (b947 b hb))
    (by norm_num [i1014, i1012, i947, RationalInterval.mul]) (by norm_num [i1014, i1012, i947, RationalInterval.mul])

def n1015 (b : ℝ) : ℝ := (n1012 b) * (n948 b)
def i1015 : RationalInterval := ⟨(-3272535430691862249769718072277 / 500000000000000000000000000000 : ℚ), (-818133835947466969688532524089 / 125000000000000000000000000000 : ℚ)⟩
theorem b1015 (b : ℝ) (hb : rootInterval.Contains b) : i1015.Contains (n1015 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1012 b hb) (b948 b hb))
    (by norm_num [i1015, i1012, i948, RationalInterval.mul]) (by norm_num [i1015, i1012, i948, RationalInterval.mul])

def n1016 (b : ℝ) : ℝ := (n1012 b) * (n949 b)
def i1016 : RationalInterval := ⟨(-512643764796888597438428469613 / 125000000000000000000000000000 : ℚ), (-4101150009442640107806634455563 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1016 (b : ℝ) (hb : rootInterval.Contains b) : i1016.Contains (n1016 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1012 b hb) (b949 b hb))
    (by norm_num [i1016, i1012, i949, RationalInterval.mul]) (by norm_num [i1016, i1012, i949, RationalInterval.mul])

def n1017 (b : ℝ) : ℝ := (n1006 b) + (n1013 b)
def i1017 : RationalInterval := ⟨(-1372695609780195527279944639189 / 1000000000000000000000000000000 : ℚ), (-686347535707842733230349753653 / 500000000000000000000000000000 : ℚ)⟩
theorem b1017 (b : ℝ) (hb : rootInterval.Contains b) : i1017.Contains (n1017 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1006 b hb) (b1013 b hb))
    (by norm_num [i1017, i1006, i1013, RationalInterval.add]) (by norm_num [i1017, i1006, i1013, RationalInterval.add])

def n1018 (b : ℝ) : ℝ := (n1007 b) + (n1014 b)
def i1018 : RationalInterval := ⟨(-51087960784855291297175753957 / 250000000000000000000000000000 : ℚ), (-204351503620502937893396226219 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1018 (b : ℝ) (hb : rootInterval.Contains b) : i1018.Contains (n1018 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1007 b hb) (b1014 b hb))
    (by norm_num [i1018, i1007, i1014, RationalInterval.add]) (by norm_num [i1018, i1007, i1014, RationalInterval.add])

def n1019 (b : ℝ) : ℝ := (n1008 b) + (n1015 b)
def i1019 : RationalInterval := ⟨(-51087960784855291297175753957 / 250000000000000000000000000000 : ℚ), (-204351503620502937893396226219 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1019 (b : ℝ) (hb : rootInterval.Contains b) : i1019.Contains (n1019 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1008 b hb) (b1015 b hb))
    (by norm_num [i1019, i1008, i1015, RationalInterval.add]) (by norm_num [i1019, i1008, i1015, RationalInterval.add])

def n1020 (b : ℝ) : ℝ := (n1009 b) + (n1016 b)
def i1020 : RationalInterval := ⟨(5628315104382070874899004279 / 20000000000000000000000000000 : ℚ), (17588498075163395325420502873 / 62500000000000000000000000000 : ℚ)⟩
theorem b1020 (b : ℝ) (hb : rootInterval.Contains b) : i1020.Contains (n1020 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1009 b hb) (b1016 b hb))
    (by norm_num [i1020, i1009, i1016, RationalInterval.add]) (by norm_num [i1020, i1009, i1016, RationalInterval.add])

def n1021 (b : ℝ) : ℝ := (n928 b) + (n963 b)
def i1021 : RationalInterval := ⟨(-28209659324118112208024508640687 / 500000000000000000000000000000 : ℚ), (-56419317860452048872940695379841 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1021 (b : ℝ) (hb : rootInterval.Contains b) : i1021.Contains (n1021 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b928 b hb) (b963 b hb))
    (by norm_num [i1021, i928, i963, RationalInterval.add]) (by norm_num [i1021, i928, i963, RationalInterval.add])

def n1022 (b : ℝ) : ℝ := (n1021 b) * (n1011 b)
def i1022 : RationalInterval := ⟨(-10453261503147548900439949832779 / 1000000000000000000000000000000 : ℚ), (-10453261347583747278976021690669 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1022 (b : ℝ) (hb : rootInterval.Contains b) : i1022.Contains (n1022 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1021 b hb) (b1011 b hb))
    (by norm_num [i1022, i1021, i1011, RationalInterval.mul]) (by norm_num [i1022, i1021, i1011, RationalInterval.mul])

def n1023 (b : ℝ) : ℝ := (n323 b) + (n937 b)
def i1023 : RationalInterval := ⟨(8451852709538019023237048820363 / 1000000000000000000000000000000 : ℚ), (8451852716126100767320741827333 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1023 (b : ℝ) (hb : rootInterval.Contains b) : i1023.Contains (n1023 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b323 b hb) (b937 b hb))
    (by norm_num [i1023, i323, i937, RationalInterval.add]) (by norm_num [i1023, i323, i937, RationalInterval.add])

def n1024 (b : ℝ) : ℝ := (n1023 b) * (n13 b)
def i1024 : RationalInterval := ⟨(8451852709538019023237048820363 / 500000000000000000000000000000 : ℚ), (8451852716126100767320741827333 / 500000000000000000000000000000 : ℚ)⟩
theorem b1024 (b : ℝ) (hb : rootInterval.Contains b) : i1024.Contains (n1024 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1023 b hb) (b13 b hb))
    (by norm_num [i1024, i1023, i13, RationalInterval.mul]) (by norm_num [i1024, i1023, i13, RationalInterval.mul])

def n1025 (b : ℝ) : ℝ := (n1024 b) * (n928 b)
def i1025 : RationalInterval := ⟨(-87738989256109434033956119747301 / 1000000000000000000000000000000 : ℚ), (-87738986979124771414368658353303 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1025 (b : ℝ) (hb : rootInterval.Contains b) : i1025.Contains (n1025 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1024 b hb) (b928 b hb))
    (by norm_num [i1025, i1024, i928, RationalInterval.mul]) (by norm_num [i1025, i1024, i928, RationalInterval.mul])

def n1026 (b : ℝ) : ℝ := (n1010 b) * (n323 b)
def i1026 : RationalInterval := ⟨(12539032645185077247871285269431 / 1000000000000000000000000000000 : ℚ), (78368954140417377717012702761 / 6250000000000000000000000000 : ℚ)⟩
theorem b1026 (b : ℝ) (hb : rootInterval.Contains b) : i1026.Contains (n1026 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1010 b hb) (b323 b hb))
    (by norm_num [i1026, i1010, i323, RationalInterval.mul]) (by norm_num [i1026, i1010, i323, RationalInterval.mul])

def n1027 (b : ℝ) : ℝ := 1 / (n1026 b)
def i1027 : RationalInterval := ⟨(15950193717786709569583134791 / 200000000000000000000000000000 : ℚ), (19937742174712232559909489407 / 250000000000000000000000000000 : ℚ)⟩
theorem b1027 (b : ℝ) (hb : rootInterval.Contains b) : i1027.Contains (n1027 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_inv_of_positive (b1026 b hb) (by norm_num [i1026]))
    (by norm_num [i1027, i1026, RationalInterval.inv]) (by norm_num [i1027, i1026, RationalInterval.inv])

def n1028 (b : ℝ) : ℝ := (n1025 b) * (n1027 b)
def i1028 : RationalInterval := ⟨(-6997269385832626060079311546587 / 1000000000000000000000000000000 : ℚ), (-6997269194597029199272658473699 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1028 (b : ℝ) (hb : rootInterval.Contains b) : i1028.Contains (n1028 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1025 b hb) (b1027 b hb))
    (by norm_num [i1028, i1025, i1027, RationalInterval.mul]) (by norm_num [i1028, i1025, i1027, RationalInterval.mul])

def n1029 (b : ℝ) : ℝ := -(n1028 b)
def i1029 : RationalInterval := ⟨(6997269194597029199272658473699 / 1000000000000000000000000000000 : ℚ), (6997269385832626060079311546587 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1029 (b : ℝ) (hb : rootInterval.Contains b) : i1029.Contains (n1029 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b1028 b hb))
    (by norm_num [i1029, i1028, RationalInterval.neg]) (by norm_num [i1029, i1028, RationalInterval.neg])

def n1030 (b : ℝ) : ℝ := (n1022 b) + (n1029 b)
def i1030 : RationalInterval := ⟨(-86399807713762992529182283977 / 25000000000000000000000000000 : ℚ), (-1727995980875560609448355072041 / 500000000000000000000000000000 : ℚ)⟩
theorem b1030 (b : ℝ) (hb : rootInterval.Contains b) : i1030.Contains (n1030 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1022 b hb) (b1029 b hb))
    (by norm_num [i1030, i1022, i1029, RationalInterval.add]) (by norm_num [i1030, i1022, i1029, RationalInterval.add])

def n1031 (b : ℝ) : ℝ := (n1030 b) * (n950 b)
def i1031 : RationalInterval := ⟨(-69471884146076066564925196513 / 10000000000000000000000000000 : ℚ), (-3473593858689102919725629211797 / 500000000000000000000000000000 : ℚ)⟩
theorem b1031 (b : ℝ) (hb : rootInterval.Contains b) : i1031.Contains (n1031 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1030 b hb) (b950 b hb))
    (by norm_num [i1031, i1030, i950, RationalInterval.mul]) (by norm_num [i1031, i1030, i950, RationalInterval.mul])

def n1032 (b : ℝ) : ℝ := (n1030 b) * (n951 b)
def i1032 : RationalInterval := ⟨(-4497217510344906665831000489307 / 1000000000000000000000000000000 : ℚ), (-89944341179613626033294580691 / 20000000000000000000000000000 : ℚ)⟩
theorem b1032 (b : ℝ) (hb : rootInterval.Contains b) : i1032.Contains (n1032 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1030 b hb) (b951 b hb))
    (by norm_num [i1032, i1030, i951, RationalInterval.mul]) (by norm_num [i1032, i1030, i951, RationalInterval.mul])

def n1033 (b : ℝ) : ℝ := (n1030 b) * (n952 b)
def i1033 : RationalInterval := ⟨(-4497217510344906665831000489307 / 1000000000000000000000000000000 : ℚ), (-89944341179613626033294580691 / 20000000000000000000000000000 : ℚ)⟩
theorem b1033 (b : ℝ) (hb : rootInterval.Contains b) : i1033.Contains (n1033 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1030 b hb) (b952 b hb))
    (by norm_num [i1033, i1030, i952, RationalInterval.mul]) (by norm_num [i1033, i1030, i952, RationalInterval.mul])

def n1034 (b : ℝ) : ℝ := (n1030 b) * (n953 b)
def i1034 : RationalInterval := ⟨(-2911244683219836600461304167083 / 1000000000000000000000000000000 : ℚ), (-1455622195510468534301188590763 / 500000000000000000000000000000 : ℚ)⟩
theorem b1034 (b : ℝ) (hb : rootInterval.Contains b) : i1034.Contains (n1034 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1030 b hb) (b953 b hb))
    (by norm_num [i1034, i1030, i953, RationalInterval.mul]) (by norm_num [i1034, i1030, i953, RationalInterval.mul])

def n1035 (b : ℝ) : ℝ := (n1017 b) + (n1031 b)
def i1035 : RationalInterval := ⟨(-8319884024387802183772464290489 / 1000000000000000000000000000000 : ℚ), (-83198827887938913059119579309 / 10000000000000000000000000000 : ℚ)⟩
theorem b1035 (b : ℝ) (hb : rootInterval.Contains b) : i1035.Contains (n1035 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1017 b hb) (b1031 b hb))
    (by norm_num [i1035, i1017, i1031, RationalInterval.add]) (by norm_num [i1035, i1017, i1031, RationalInterval.add])

def n1036 (b : ℝ) : ℝ := (n1018 b) + (n1032 b)
def i1036 : RationalInterval := ⟨(-940313870696865566203940701027 / 200000000000000000000000000000 : ℚ), (-4701568562601184239558125260769 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1036 (b : ℝ) (hb : rootInterval.Contains b) : i1036.Contains (n1036 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1018 b hb) (b1032 b hb))
    (by norm_num [i1036, i1018, i1032, RationalInterval.add]) (by norm_num [i1036, i1018, i1032, RationalInterval.add])

def n1037 (b : ℝ) : ℝ := (n1019 b) + (n1033 b)
def i1037 : RationalInterval := ⟨(-940313870696865566203940701027 / 200000000000000000000000000000 : ℚ), (-4701568562601184239558125260769 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1037 (b : ℝ) (hb : rootInterval.Contains b) : i1037.Contains (n1037 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1019 b hb) (b1033 b hb))
    (by norm_num [i1037, i1019, i1033, RationalInterval.add]) (by norm_num [i1037, i1019, i1033, RationalInterval.add])

def n1038 (b : ℝ) : ℝ := (n1020 b) + (n1034 b)
def i1038 : RationalInterval := ⟨(-2629828928000733056716353953133 / 1000000000000000000000000000000 : ℚ), (-1314914210909161371697824567779 / 500000000000000000000000000000 : ℚ)⟩
theorem b1038 (b : ℝ) (hb : rootInterval.Contains b) : i1038.Contains (n1038 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1020 b hb) (b1034 b hb))
    (by norm_num [i1038, i1020, i1034, RationalInterval.add]) (by norm_num [i1038, i1020, i1034, RationalInterval.add])

def n1039 (b : ℝ) : ℝ := (n1023 b) * (n1011 b)
def i1039 : RationalInterval := ⟨(1565942811691003593089861053321 / 1000000000000000000000000000000 : ℚ), (97871425896903300472253549447 / 62500000000000000000000000000 : ℚ)⟩
theorem b1039 (b : ℝ) (hb : rootInterval.Contains b) : i1039.Contains (n1039 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1023 b hb) (b1011 b hb))
    (by norm_num [i1039, i1023, i1011, RationalInterval.mul]) (by norm_num [i1039, i1023, i1011, RationalInterval.mul])

def n1040 (b : ℝ) : ℝ := (n1039 b) * (n972 b)
def i1040 : RationalInterval := ⟨(13644152694691177662692998498797 / 1000000000000000000000000000000 : ℚ), (682207636776375450156507632401 / 50000000000000000000000000000 : ℚ)⟩
theorem b1040 (b : ℝ) (hb : rootInterval.Contains b) : i1040.Contains (n1040 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1039 b hb) (b972 b hb))
    (by norm_num [i1040, i1039, i972, RationalInterval.mul]) (by norm_num [i1040, i1039, i972, RationalInterval.mul])

def n1041 (b : ℝ) : ℝ := (n1039 b) * (n973 b)
def i1041 : RationalInterval := ⟨(8342074909590556170933728013053 / 1000000000000000000000000000000 : ℚ), (4171037467417816869124685333563 / 500000000000000000000000000000 : ℚ)⟩
theorem b1041 (b : ℝ) (hb : rootInterval.Contains b) : i1041.Contains (n1041 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1039 b hb) (b973 b hb))
    (by norm_num [i1041, i1039, i973, RationalInterval.mul]) (by norm_num [i1041, i1039, i973, RationalInterval.mul])

def n1042 (b : ℝ) : ℝ := (n1039 b) * (n974 b)
def i1042 : RationalInterval := ⟨(8342074909590556170933728013053 / 1000000000000000000000000000000 : ℚ), (4171037467417816869124685333563 / 500000000000000000000000000000 : ℚ)⟩
theorem b1042 (b : ℝ) (hb : rootInterval.Contains b) : i1042.Contains (n1042 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1039 b hb) (b974 b hb))
    (by norm_num [i1042, i1039, i974, RationalInterval.mul]) (by norm_num [i1042, i1039, i974, RationalInterval.mul])

def n1043 (b : ℝ) : ℝ := (n1039 b) * (n975 b)
def i1043 : RationalInterval := ⟨(20330978010240818784029379917 / 4000000000000000000000000000 : ℚ), (1016548903625925387241406322709 / 200000000000000000000000000000 : ℚ)⟩
theorem b1043 (b : ℝ) (hb : rootInterval.Contains b) : i1043.Contains (n1043 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1039 b hb) (b975 b hb))
    (by norm_num [i1043, i1039, i975, RationalInterval.mul]) (by norm_num [i1043, i1039, i975, RationalInterval.mul])

def n1044 (b : ℝ) : ℝ := (n1035 b) + (n1040 b)
def i1044 : RationalInterval := ⟨(1331067167575843869730133552077 / 250000000000000000000000000000 : ℚ), (16638343583542555303806858491 / 3125000000000000000000000000 : ℚ)⟩
theorem b1044 (b : ℝ) (hb : rootInterval.Contains b) : i1044.Contains (n1044 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1035 b hb) (b1040 b hb))
    (by norm_num [i1044, i1035, i1040, RationalInterval.add]) (by norm_num [i1044, i1035, i1040, RationalInterval.add])

def n1045 (b : ℝ) : ℝ := (n1036 b) + (n1041 b)
def i1045 : RationalInterval := ⟨(1820252778053114169957012253959 / 500000000000000000000000000000 : ℚ), (3640506372234449498691245406357 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1045 (b : ℝ) (hb : rootInterval.Contains b) : i1045.Contains (n1045 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1036 b hb) (b1041 b hb))
    (by norm_num [i1045, i1036, i1041, RationalInterval.add]) (by norm_num [i1045, i1036, i1041, RationalInterval.add])

def n1046 (b : ℝ) : ℝ := (n1037 b) + (n1042 b)
def i1046 : RationalInterval := ⟨(1820252778053114169957012253959 / 500000000000000000000000000000 : ℚ), (3640506372234449498691245406357 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1046 (b : ℝ) (hb : rootInterval.Contains b) : i1046.Contains (n1046 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1037 b hb) (b1042 b hb))
    (by norm_num [i1046, i1037, i1042, RationalInterval.add]) (by norm_num [i1046, i1037, i1042, RationalInterval.add])

def n1047 (b : ℝ) : ℝ := (n1038 b) + (n1043 b)
def i1047 : RationalInterval := ⟨(2452915574559471639290991026117 / 1000000000000000000000000000000 : ℚ), (2452916096311304192811382477987 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1047 (b : ℝ) (hb : rootInterval.Contains b) : i1047.Contains (n1047 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1038 b hb) (b1043 b hb))
    (by norm_num [i1047, i1038, i1043, RationalInterval.add]) (by norm_num [i1047, i1038, i1043, RationalInterval.add])

def n1048 (b : ℝ) : ℝ := (n63 b) * (n197 b)
def i1048 : RationalInterval := ⟨(-940692481607071448016668101319 / 1000000000000000000000000000000 : ℚ), (-470346239873838903481253778373 / 500000000000000000000000000000 : ℚ)⟩
theorem b1048 (b : ℝ) (hb : rootInterval.Contains b) : i1048.Contains (n1048 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b63 b hb) (b197 b hb))
    (by norm_num [i1048, i63, i197, RationalInterval.mul]) (by norm_num [i1048, i63, i197, RationalInterval.mul])

def n1049 (b : ℝ) : ℝ := (n65 b) * (n199 b)
def i1049 : RationalInterval := ⟨(71586673164687876932962048469 / 500000000000000000000000000000 : ℚ), (143173346782637265196030259379 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1049 (b : ℝ) (hb : rootInterval.Contains b) : i1049.Contains (n1049 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b65 b hb) (b199 b hb))
    (by norm_num [i1049, i65, i199, RationalInterval.mul]) (by norm_num [i1049, i65, i199, RationalInterval.mul])

def n1050 (b : ℝ) : ℝ := (n1048 b) + (n1049 b)
def i1050 : RationalInterval := ⟨(-797519135277695694150744004381 / 1000000000000000000000000000000 : ℚ), (-797519132965040541766477297367 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1050 (b : ℝ) (hb : rootInterval.Contains b) : i1050.Contains (n1050 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1048 b hb) (b1049 b hb))
    (by norm_num [i1050, i1048, i1049, RationalInterval.add]) (by norm_num [i1050, i1048, i1049, RationalInterval.add])

def n1051 (b : ℝ) : ℝ := (n65 b) * (n197 b)
def i1051 : RationalInterval := ⟨(-110324910536872321008832141559 / 200000000000000000000000000000 : ℚ), (-551624551592399094313807892583 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1051 (b : ℝ) (hb : rootInterval.Contains b) : i1051.Contains (n1051 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b65 b hb) (b197 b hb))
    (by norm_num [i1051, i65, i197, RationalInterval.mul]) (by norm_num [i1051, i65, i197, RationalInterval.mul])

def n1052 (b : ℝ) : ℝ := (n0 b) * (n199 b)
def i1052 : RationalInterval := ⟨(18536468041396519763542229 / 200000000000000000000000000 : ℚ), (18536468100150925535706972879 / 200000000000000000000000000000 : ℚ)⟩
theorem b1052 (b : ℝ) (hb : rootInterval.Contains b) : i1052.Contains (n1052 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b0 b hb) (b199 b hb))
    (by norm_num [i1052, i0, i199, RationalInterval.mul]) (by norm_num [i1052, i0, i199, RationalInterval.mul])

def n1053 (b : ℝ) : ℝ := (n1051 b) + (n1052 b)
def i1053 : RationalInterval := ⟨(-91788442495475801245289912559 / 200000000000000000000000000000 : ℚ), (-114735552772911116658818257047 / 250000000000000000000000000000 : ℚ)⟩
theorem b1053 (b : ℝ) (hb : rootInterval.Contains b) : i1053.Contains (n1053 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1051 b hb) (b1052 b hb))
    (by norm_num [i1053, i1051, i1052, RationalInterval.add]) (by norm_num [i1053, i1051, i1052, RationalInterval.add])

def n1054 (b : ℝ) : ℝ := -(n1050 b)
def i1054 : RationalInterval := ⟨(797519132965040541766477297367 / 1000000000000000000000000000000 : ℚ), (797519135277695694150744004381 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1054 (b : ℝ) (hb : rootInterval.Contains b) : i1054.Contains (n1054 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b1050 b hb))
    (by norm_num [i1054, i1050, RationalInterval.neg]) (by norm_num [i1054, i1050, RationalInterval.neg])

def n1055 (b : ℝ) : ℝ := -(n1053 b)
def i1055 : RationalInterval := ⟨(114735552772911116658818257047 / 250000000000000000000000000000 : ℚ), (91788442495475801245289912559 / 200000000000000000000000000000 : ℚ)⟩
theorem b1055 (b : ℝ) (hb : rootInterval.Contains b) : i1055.Contains (n1055 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b1053 b hb))
    (by norm_num [i1055, i1053, RationalInterval.neg]) (by norm_num [i1055, i1053, RationalInterval.neg])

def n1056 (b : ℝ) : ℝ := (n1055 b) + (n15 b)
def i1056 : RationalInterval := ⟨(364735552772911116658818257047 / 250000000000000000000000000000 : ℚ), (291788442495475801245289912559 / 200000000000000000000000000000 : ℚ)⟩
theorem b1056 (b : ℝ) (hb : rootInterval.Contains b) : i1056.Contains (n1056 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1055 b hb) (b15 b hb))
    (by norm_num [i1056, i1055, i15, RationalInterval.add]) (by norm_num [i1056, i1055, i15, RationalInterval.add])

def n1057 (b : ℝ) : ℝ := (n210 b) * (n1054 b)
def i1057 : RationalInterval := ⟨(-60614565067950864806160355909 / 250000000000000000000000000000 : ℚ), (-12122912813062799759431399201 / 50000000000000000000000000000 : ℚ)⟩
theorem b1057 (b : ℝ) (hb : rootInterval.Contains b) : i1057.Contains (n1057 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b210 b hb) (b1054 b hb))
    (by norm_num [i1057, i210, i1054, RationalInterval.mul]) (by norm_num [i1057, i210, i1054, RationalInterval.mul])

def n1058 (b : ℝ) : ℝ := (n211 b) * (n1056 b)
def i1058 : RationalInterval := ⟨(-1567285936598308968645277257991 / 1000000000000000000000000000000 : ℚ), (-1567285919126228565137266261251 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1058 (b : ℝ) (hb : rootInterval.Contains b) : i1058.Contains (n1058 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b211 b hb) (b1056 b hb))
    (by norm_num [i1058, i211, i1056, RationalInterval.mul]) (by norm_num [i1058, i211, i1056, RationalInterval.mul])

def n1059 (b : ℝ) : ℝ := (n1057 b) + (n1058 b)
def i1059 : RationalInterval := ⟨(-1809744196870112427869918681627 / 1000000000000000000000000000000 : ℚ), (-1809744175387484560325894245271 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1059 (b : ℝ) (hb : rootInterval.Contains b) : i1059.Contains (n1059 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1057 b hb) (b1058 b hb))
    (by norm_num [i1059, i1057, i1058, RationalInterval.add]) (by norm_num [i1059, i1057, i1058, RationalInterval.add])

def n1060 (b : ℝ) : ℝ := (n212 b) * (n1054 b)
def i1060 : RationalInterval := ⟨(-53546523047608250293548447621 / 62500000000000000000000000000 : ℚ), (-856744357540115464181933556461 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1060 (b : ℝ) (hb : rootInterval.Contains b) : i1060.Contains (n1060 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b212 b hb) (b1054 b hb))
    (by norm_num [i1060, i212, i1054, RationalInterval.mul]) (by norm_num [i1060, i212, i1054, RationalInterval.mul])

def n1061 (b : ℝ) : ℝ := (n213 b) * (n1056 b)
def i1061 : RationalInterval := ⟨(-2769060948706753600195135915069 / 500000000000000000000000000000 : ℚ), (-5538121854743533744428644979101 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1061 (b : ℝ) (hb : rootInterval.Contains b) : i1061.Contains (n1061 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b213 b hb) (b1056 b hb))
    (by norm_num [i1061, i213, i1056, RationalInterval.mul]) (by norm_num [i1061, i213, i1056, RationalInterval.mul])

def n1062 (b : ℝ) : ℝ := (n1060 b) + (n1061 b)
def i1062 : RationalInterval := ⟨(-3197433133087619602543523496037 / 500000000000000000000000000000 : ℚ), (-3197433106141824604305289267781 / 500000000000000000000000000000 : ℚ)⟩
theorem b1062 (b : ℝ) (hb : rootInterval.Contains b) : i1062.Contains (n1062 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1060 b hb) (b1061 b hb))
    (by norm_num [i1062, i1060, i1061, RationalInterval.add]) (by norm_num [i1062, i1060, i1061, RationalInterval.add])

def n1063 (b : ℝ) : ℝ := -(n197 b)
def i1063 : RationalInterval := ⟨(389067928155278712648699664163 / 1000000000000000000000000000000 : ℚ), (97266982230677460743126848381 / 250000000000000000000000000000 : ℚ)⟩
theorem b1063 (b : ℝ) (hb : rootInterval.Contains b) : i1063.Contains (n1063 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b197 b hb))
    (by norm_num [i1063, i197, RationalInterval.neg]) (by norm_num [i1063, i197, RationalInterval.neg])

def n1064 (b : ℝ) : ℝ := -(n199 b)
def i1064 : RationalInterval := ⟨(-6311375785235329689686924373 / 62500000000000000000000000000 : ℚ), (-25245503061196577524106475969 / 250000000000000000000000000000 : ℚ)⟩
theorem b1064 (b : ℝ) (hb : rootInterval.Contains b) : i1064.Contains (n1064 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b199 b hb))
    (by norm_num [i1064, i199, RationalInterval.neg]) (by norm_num [i1064, i199, RationalInterval.neg])

def n1065 (b : ℝ) : ℝ := (n1059 b) + (n1063 b)
def i1065 : RationalInterval := ⟨(-177584533589354214402652377183 / 125000000000000000000000000000 : ℚ), (-1420676246464774717353386851747 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1065 (b : ℝ) (hb : rootInterval.Contains b) : i1065.Contains (n1065 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1059 b hb) (b1063 b hb))
    (by norm_num [i1065, i1059, i1063, RationalInterval.add]) (by norm_num [i1065, i1059, i1063, RationalInterval.add])

def n1066 (b : ℝ) : ℝ := (n1062 b) + (n1064 b)
def i1066 : RationalInterval := ⟨(-3247924139369502240061018891021 / 500000000000000000000000000000 : ℚ), (-3247924112264217759353502219719 / 500000000000000000000000000000 : ℚ)⟩
theorem b1066 (b : ℝ) (hb : rootInterval.Contains b) : i1066.Contains (n1066 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1062 b hb) (b1064 b hb))
    (by norm_num [i1066, i1062, i1064, RationalInterval.add]) (by norm_num [i1066, i1062, i1064, RationalInterval.add])

def n1067 (b : ℝ) : ℝ := (n1054 b) * (n21 b)
def i1067 : RationalInterval := ⟨(-83251413265369593248339206121 / 100000000000000000000000000000 : ℚ), (-416257064970101265609083119141 / 500000000000000000000000000000 : ℚ)⟩
theorem b1067 (b : ℝ) (hb : rootInterval.Contains b) : i1067.Contains (n1067 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1054 b hb) (b21 b hb))
    (by norm_num [i1067, i1054, i21, RationalInterval.mul]) (by norm_num [i1067, i1054, i21, RationalInterval.mul])

def n1068 (b : ℝ) : ℝ := (n1055 b) * (n320 b)
def i1068 : RationalInterval := ⟨(-421625954700975985491505842023 / 1000000000000000000000000000000 : ℚ), (-421625953170150131764888547807 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1068 (b : ℝ) (hb : rootInterval.Contains b) : i1068.Contains (n1068 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1055 b hb) (b320 b hb))
    (by norm_num [i1068, i1055, i320, RationalInterval.mul]) (by norm_num [i1068, i1055, i320, RationalInterval.mul])

def n1069 (b : ℝ) : ℝ := (n1067 b) + (n1068 b)
def i1069 : RationalInterval := ⟨(-1254140087354671917974897903233 / 1000000000000000000000000000000 : ℚ), (-1254140083110352662983054786089 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1069 (b : ℝ) (hb : rootInterval.Contains b) : i1069.Contains (n1069 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1067 b hb) (b1068 b hb))
    (by norm_num [i1069, i1067, i1068, RationalInterval.add]) (by norm_num [i1069, i1067, i1068, RationalInterval.add])

def n1070 (b : ℝ) : ℝ := (n302 b) * (n1065 b)
def i1070 : RationalInterval := ⟨(402849909078773481495035143311 / 200000000000000000000000000000 : ℚ), (1007124788477219515971210550771 / 500000000000000000000000000000 : ℚ)⟩
theorem b1070 (b : ℝ) (hb : rootInterval.Contains b) : i1070.Contains (n1070 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b302 b hb) (b1065 b hb))
    (by norm_num [i1070, i302, i1065, RationalInterval.mul]) (by norm_num [i1070, i302, i1065, RationalInterval.mul])

def n1071 (b : ℝ) : ℝ := (n303 b) * (n1066 b)
def i1071 : RationalInterval := ⟨(5961957002988442057740962290971 / 1000000000000000000000000000000 : ℚ), (5961957052808424070031912136533 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1071 (b : ℝ) (hb : rootInterval.Contains b) : i1071.Contains (n1071 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b303 b hb) (b1066 b hb))
    (by norm_num [i1071, i303, i1066, RationalInterval.mul]) (by norm_num [i1071, i303, i1066, RationalInterval.mul])

def n1072 (b : ℝ) : ℝ := (n1070 b) + (n1071 b)
def i1072 : RationalInterval := ⟨(3988103274191154732608069003763 / 500000000000000000000000000000 : ℚ), (319048265190514524078973329523 / 40000000000000000000000000000 : ℚ)⟩
theorem b1072 (b : ℝ) (hb : rootInterval.Contains b) : i1072.Contains (n1072 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1070 b hb) (b1071 b hb))
    (by norm_num [i1072, i1070, i1071, RationalInterval.add]) (by norm_num [i1072, i1070, i1071, RationalInterval.add])

def n1073 (b : ℝ) : ℝ := (n1069 b) + (n1072 b)
def i1073 : RationalInterval := ⟨(6722066461027637547241240104293 / 1000000000000000000000000000000 : ℚ), (3361033273326255219495639225993 / 500000000000000000000000000000 : ℚ)⟩
theorem b1073 (b : ℝ) (hb : rootInterval.Contains b) : i1073.Contains (n1073 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1069 b hb) (b1072 b hb))
    (by norm_num [i1073, i1069, i1072, RationalInterval.add]) (by norm_num [i1073, i1069, i1072, RationalInterval.add])

def n1074 (b : ℝ) : ℝ := (n63 b) * (n1065 b)
def i1074 : RationalInterval := ⟨(-1717462922834636373581820059503 / 500000000000000000000000000000 : ℚ), (-1717462895929321062414281284151 / 500000000000000000000000000000 : ℚ)⟩
theorem b1074 (b : ℝ) (hb : rootInterval.Contains b) : i1074.Contains (n1074 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b63 b hb) (b1065 b hb))
    (by norm_num [i1074, i63, i1065, RationalInterval.mul]) (by norm_num [i1074, i63, i1065, RationalInterval.mul])

def n1075 (b : ℝ) : ℝ := (n65 b) * (n1066 b)
def i1075 : RationalInterval := ⟨(-4604940596088963155046465513777 / 500000000000000000000000000000 : ℚ), (-920988111525265981709446451069 / 100000000000000000000000000000 : ℚ)⟩
theorem b1075 (b : ℝ) (hb : rootInterval.Contains b) : i1075.Contains (n1075 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b65 b hb) (b1066 b hb))
    (by norm_num [i1075, i65, i1066, RationalInterval.mul]) (by norm_num [i1075, i65, i1066, RationalInterval.mul])

def n1076 (b : ℝ) : ℝ := (n1074 b) + (n1075 b)
def i1076 : RationalInterval := ⟨(-39515021993272497053926784833 / 3125000000000000000000000000 : ℚ), (-790300431694456371370189192437 / 62500000000000000000000000000 : ℚ)⟩
theorem b1076 (b : ℝ) (hb : rootInterval.Contains b) : i1076.Contains (n1076 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1074 b hb) (b1075 b hb))
    (by norm_num [i1076, i1074, i1075, RationalInterval.add]) (by norm_num [i1076, i1074, i1075, RationalInterval.add])

def n1077 (b : ℝ) : ℝ := (n65 b) * (n1065 b)
def i1077 : RationalInterval := ⟨(-1007124788477219515971210550771 / 500000000000000000000000000000 : ℚ), (-402849909078773481495035143311 / 200000000000000000000000000000 : ℚ)⟩
theorem b1077 (b : ℝ) (hb : rootInterval.Contains b) : i1077.Contains (n1077 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b65 b hb) (b1065 b hb))
    (by norm_num [i1077, i65, i1065, RationalInterval.mul]) (by norm_num [i1077, i65, i1065, RationalInterval.mul])

def n1078 (b : ℝ) : ℝ := (n0 b) * (n1066 b)
def i1078 : RationalInterval := ⟨(-5961957052808424070031912136533 / 1000000000000000000000000000000 : ℚ), (-5961957002988442057740962290971 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1078 (b : ℝ) (hb : rootInterval.Contains b) : i1078.Contains (n1078 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b0 b hb) (b1066 b hb))
    (by norm_num [i1078, i0, i1066, RationalInterval.mul]) (by norm_num [i1078, i0, i1066, RationalInterval.mul])

def n1079 (b : ℝ) : ℝ := (n1077 b) + (n1078 b)
def i1079 : RationalInterval := ⟨(-319048265190514524078973329523 / 40000000000000000000000000000 : ℚ), (-3988103274191154732608069003763 / 500000000000000000000000000000 : ℚ)⟩
theorem b1079 (b : ℝ) (hb : rootInterval.Contains b) : i1079.Contains (n1079 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1077 b hb) (b1078 b hb))
    (by norm_num [i1079, i1077, i1078, RationalInterval.add]) (by norm_num [i1079, i1077, i1078, RationalInterval.add])

