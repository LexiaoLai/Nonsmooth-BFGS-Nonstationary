import BFGS.Counterexample.Certificates.IntervalTrace11

/-! Generated arithmetic proofs. Each bound is checked by the Lean kernel. -/
namespace BFGS.Counterexample.Trace
noncomputable section
open BFGS RationalInterval
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false

def n1080 (b : ℝ) : ℝ := (n1065 b) * (n931 b)
def i1080 : RationalInterval := ⟨(2718061049512958302165713681287 / 500000000000000000000000000000 : ℚ), (679515273326599802275469023613 / 125000000000000000000000000000 : ℚ)⟩
theorem b1080 (b : ℝ) (hb : rootInterval.Contains b) : i1080.Contains (n1080 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1065 b hb) (b931 b hb))
    (by norm_num [i1080, i1065, i931, RationalInterval.mul]) (by norm_num [i1080, i1065, i931, RationalInterval.mul])

def n1081 (b : ℝ) : ℝ := (n1066 b) * (n934 b)
def i1081 : RationalInterval := ⟨(7545601830215087819334259706483 / 500000000000000000000000000000 : ℚ), (1509120379330564177550854528939 / 100000000000000000000000000000 : ℚ)⟩
theorem b1081 (b : ℝ) (hb : rootInterval.Contains b) : i1081.Contains (n1081 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1066 b hb) (b934 b hb))
    (by norm_num [i1081, i1066, i934, RationalInterval.mul]) (by norm_num [i1081, i1066, i934, RationalInterval.mul])

def n1082 (b : ℝ) : ℝ := (n1080 b) + (n1081 b)
def i1082 : RationalInterval := ⟨(1026366287972804612149997338777 / 50000000000000000000000000000 : ℚ), (10263662989959220096856148739147 / 500000000000000000000000000000 : ℚ)⟩
theorem b1082 (b : ℝ) (hb : rootInterval.Contains b) : i1082.Contains (n1082 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1080 b hb) (b1081 b hb))
    (by norm_num [i1082, i1080, i1081, RationalInterval.add]) (by norm_num [i1082, i1080, i1081, RationalInterval.add])

def n1083 (b : ℝ) : ℝ := (n1082 b) * (n13 b)
def i1083 : RationalInterval := ⟨(1026366287972804612149997338777 / 25000000000000000000000000000 : ℚ), (10263662989959220096856148739147 / 250000000000000000000000000000 : ℚ)⟩
theorem b1083 (b : ℝ) (hb : rootInterval.Contains b) : i1083.Contains (n1083 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1082 b hb) (b13 b hb))
    (by norm_num [i1083, i1082, i13, RationalInterval.mul]) (by norm_num [i1083, i1082, i13, RationalInterval.mul])

def n1084 (b : ℝ) : ℝ := (n1054 b) * (n302 b)
def i1084 : RationalInterval := ⟨(-1130730917536439063633384970991 / 1000000000000000000000000000000 : ℚ), (-1130730914249557364950406954403 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1084 (b : ℝ) (hb : rootInterval.Contains b) : i1084.Contains (n1084 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1054 b hb) (b302 b hb))
    (by norm_num [i1084, i1054, i302, RationalInterval.mul]) (by norm_num [i1084, i1054, i302, RationalInterval.mul])

def n1085 (b : ℝ) : ℝ := (n1054 b) * (n303 b)
def i1085 : RationalInterval := ⟨(-914964187371989020697516211 / 1250000000000000000000000000 : ℚ), (-731971347767037094067168305719 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1085 (b : ℝ) (hb : rootInterval.Contains b) : i1085.Contains (n1085 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1054 b hb) (b303 b hb))
    (by norm_num [i1085, i1054, i303, RationalInterval.mul]) (by norm_num [i1085, i1054, i303, RationalInterval.mul])

def n1086 (b : ℝ) : ℝ := (n1055 b) * (n302 b)
def i1086 : RationalInterval := ⟨(-40668314876079390348963140201 / 62500000000000000000000000000 : ℚ), (-650693036047971993171795365133 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1086 (b : ℝ) (hb : rootInterval.Contains b) : i1086.Contains (n1086 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1055 b hb) (b302 b hb))
    (by norm_num [i1086, i1055, i302, RationalInterval.mul]) (by norm_num [i1086, i1055, i302, RationalInterval.mul])

def n1087 (b : ℝ) : ℝ := (n1055 b) * (n303 b)
def i1087 : RationalInterval := ⟨(-210610965889290371235092730909 / 500000000000000000000000000000 : ℚ), (-421221930502149759854158851039 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1087 (b : ℝ) (hb : rootInterval.Contains b) : i1087.Contains (n1087 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1055 b hb) (b303 b hb))
    (by norm_num [i1087, i1055, i303, RationalInterval.mul]) (by norm_num [i1087, i1055, i303, RationalInterval.mul])

def n1088 (b : ℝ) : ℝ := (n302 b) * (n1054 b)
def i1088 : RationalInterval := ⟨(-1130730917536439063633384970991 / 1000000000000000000000000000000 : ℚ), (-1130730914249557364950406954403 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1088 (b : ℝ) (hb : rootInterval.Contains b) : i1088.Contains (n1088 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b302 b hb) (b1054 b hb))
    (by norm_num [i1088, i302, i1054, RationalInterval.mul]) (by norm_num [i1088, i302, i1054, RationalInterval.mul])

def n1089 (b : ℝ) : ℝ := (n302 b) * (n1055 b)
def i1089 : RationalInterval := ⟨(-40668314876079390348963140201 / 62500000000000000000000000000 : ℚ), (-650693036047971993171795365133 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1089 (b : ℝ) (hb : rootInterval.Contains b) : i1089.Contains (n1089 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b302 b hb) (b1055 b hb))
    (by norm_num [i1089, i302, i1055, RationalInterval.mul]) (by norm_num [i1089, i302, i1055, RationalInterval.mul])

def n1090 (b : ℝ) : ℝ := (n303 b) * (n1054 b)
def i1090 : RationalInterval := ⟨(-914964187371989020697516211 / 1250000000000000000000000000 : ℚ), (-731971347767037094067168305719 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1090 (b : ℝ) (hb : rootInterval.Contains b) : i1090.Contains (n1090 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b303 b hb) (b1054 b hb))
    (by norm_num [i1090, i303, i1054, RationalInterval.mul]) (by norm_num [i1090, i303, i1054, RationalInterval.mul])

def n1091 (b : ℝ) : ℝ := (n303 b) * (n1055 b)
def i1091 : RationalInterval := ⟨(-210610965889290371235092730909 / 500000000000000000000000000000 : ℚ), (-421221930502149759854158851039 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1091 (b : ℝ) (hb : rootInterval.Contains b) : i1091.Contains (n1091 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b303 b hb) (b1055 b hb))
    (by norm_num [i1091, i303, i1055, RationalInterval.mul]) (by norm_num [i1091, i303, i1055, RationalInterval.mul])

def n1092 (b : ℝ) : ℝ := (n1084 b) + (n1088 b)
def i1092 : RationalInterval := ⟨(-1130730917536439063633384970991 / 500000000000000000000000000000 : ℚ), (-1130730914249557364950406954403 / 500000000000000000000000000000 : ℚ)⟩
theorem b1092 (b : ℝ) (hb : rootInterval.Contains b) : i1092.Contains (n1092 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1084 b hb) (b1088 b hb))
    (by norm_num [i1092, i1084, i1088, RationalInterval.add]) (by norm_num [i1092, i1084, i1088, RationalInterval.add])

def n1093 (b : ℝ) : ℝ := (n1085 b) + (n1089 b)
def i1093 : RationalInterval := ⟨(-86416524244678841383838950751 / 62500000000000000000000000000 : ℚ), (-345666095953752271809740917713 / 250000000000000000000000000000 : ℚ)⟩
theorem b1093 (b : ℝ) (hb : rootInterval.Contains b) : i1093.Contains (n1093 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1085 b hb) (b1089 b hb))
    (by norm_num [i1093, i1085, i1089, RationalInterval.add]) (by norm_num [i1093, i1085, i1089, RationalInterval.add])

def n1094 (b : ℝ) : ℝ := (n1086 b) + (n1090 b)
def i1094 : RationalInterval := ⟨(-86416524244678841383838950751 / 62500000000000000000000000000 : ℚ), (-345666095953752271809740917713 / 250000000000000000000000000000 : ℚ)⟩
theorem b1094 (b : ℝ) (hb : rootInterval.Contains b) : i1094.Contains (n1094 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1086 b hb) (b1090 b hb))
    (by norm_num [i1094, i1086, i1090, RationalInterval.add]) (by norm_num [i1094, i1086, i1090, RationalInterval.add])

def n1095 (b : ℝ) : ℝ := (n1087 b) + (n1091 b)
def i1095 : RationalInterval := ⟨(-210610965889290371235092730909 / 250000000000000000000000000000 : ℚ), (-421221930502149759854158851039 / 500000000000000000000000000000 : ℚ)⟩
theorem b1095 (b : ℝ) (hb : rootInterval.Contains b) : i1095.Contains (n1095 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1087 b hb) (b1091 b hb))
    (by norm_num [i1095, i1087, i1091, RationalInterval.add]) (by norm_num [i1095, i1087, i1091, RationalInterval.add])

def n1096 (b : ℝ) : ℝ := (n1076 b) * (n302 b)
def i1096 : RationalInterval := ⟨(17927938633183652107348179557599 / 1000000000000000000000000000000 : ℚ), (17927938818668813668224449911841 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1096 (b : ℝ) (hb : rootInterval.Contains b) : i1096.Contains (n1096 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1076 b hb) (b302 b hb))
    (by norm_num [i1096, i1076, i302, RationalInterval.mul]) (by norm_num [i1096, i1076, i302, RationalInterval.mul])

def n1097 (b : ℝ) : ℝ := (n1076 b) * (n303 b)
def i1097 : RationalInterval := ⟨(11605535179628001136386666018103 / 1000000000000000000000000000000 : ℚ), (11605535299745214139596164338561 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1097 (b : ℝ) (hb : rootInterval.Contains b) : i1097.Contains (n1097 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1076 b hb) (b303 b hb))
    (by norm_num [i1097, i1076, i303, RationalInterval.mul]) (by norm_num [i1097, i1076, i303, RationalInterval.mul])

def n1098 (b : ℝ) : ℝ := (n1079 b) * (n302 b)
def i1098 : RationalInterval := ⟨(5654374265081727395662885792849 / 500000000000000000000000000000 : ℚ), (11308748645625411481235563296523 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1098 (b : ℝ) (hb : rootInterval.Contains b) : i1098.Contains (n1098 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1079 b hb) (b302 b hb))
    (by norm_num [i1098, i1079, i302, RationalInterval.mul]) (by norm_num [i1098, i1079, i302, RationalInterval.mul])

def n1099 (b : ℝ) : ℝ := (n1079 b) * (n303 b)
def i1099 : RationalInterval := ⟨(1464129051194460011743540516387 / 200000000000000000000000000000 : ℚ), (3660322665371989965124198338743 / 500000000000000000000000000000 : ℚ)⟩
theorem b1099 (b : ℝ) (hb : rootInterval.Contains b) : i1099.Contains (n1099 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1079 b hb) (b303 b hb))
    (by norm_num [i1099, i1079, i303, RationalInterval.mul]) (by norm_num [i1099, i1079, i303, RationalInterval.mul])

def n1100 (b : ℝ) : ℝ := (n931 b) * (n1054 b)
def i1100 : RationalInterval := ⟨(-381456666184515180786977452677 / 125000000000000000000000000000 : ℚ), (-38145666490654778309246705391 / 12500000000000000000000000000 : ℚ)⟩
theorem b1100 (b : ℝ) (hb : rootInterval.Contains b) : i1100.Contains (n1100 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b931 b hb) (b1054 b hb))
    (by norm_num [i1100, i931, i1054, RationalInterval.mul]) (by norm_num [i1100, i931, i1054, RationalInterval.mul])

def n1101 (b : ℝ) : ℝ := (n931 b) * (n1055 b)
def i1101 : RationalInterval := ⟨(-1756111507288244071402840141557 / 1000000000000000000000000000000 : ℚ), (-109756968824677481991121472483 / 62500000000000000000000000000 : ℚ)⟩
theorem b1101 (b : ℝ) (hb : rootInterval.Contains b) : i1101.Contains (n1101 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b931 b hb) (b1055 b hb))
    (by norm_num [i1101, i931, i1055, RationalInterval.mul]) (by norm_num [i1101, i931, i1055, RationalInterval.mul])

def n1102 (b : ℝ) : ℝ := (n934 b) * (n1054 b)
def i1102 : RationalInterval := ⟨(-1852802479843782952190130148693 / 1000000000000000000000000000000 : ℚ), (-463200618404951865071445262269 / 250000000000000000000000000000 : ℚ)⟩
theorem b1102 (b : ℝ) (hb : rootInterval.Contains b) : i1102.Contains (n1102 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b934 b hb) (b1054 b hb))
    (by norm_num [i1102, i934, i1054, RationalInterval.mul]) (by norm_num [i1102, i934, i1054, RationalInterval.mul])

def n1103 (b : ℝ) : ℝ := (n934 b) * (n1055 b)
def i1103 : RationalInterval := ⟨(-1066218015053640082606175994027 / 1000000000000000000000000000000 : ℚ), (-533109005672229501062439762131 / 500000000000000000000000000000 : ℚ)⟩
theorem b1103 (b : ℝ) (hb : rootInterval.Contains b) : i1103.Contains (n1103 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b934 b hb) (b1055 b hb))
    (by norm_num [i1103, i934, i1055, RationalInterval.mul]) (by norm_num [i1103, i934, i1055, RationalInterval.mul])

def n1104 (b : ℝ) : ℝ := (n1096 b) + (n1100 b)
def i1104 : RationalInterval := ⟨(14876285303707530661052359936183 / 1000000000000000000000000000000 : ℚ), (14876285499416431403484713480561 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1104 (b : ℝ) (hb : rootInterval.Contains b) : i1104.Contains (n1104 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1096 b hb) (b1100 b hb))
    (by norm_num [i1104, i1096, i1100, RationalInterval.add]) (by norm_num [i1104, i1096, i1100, RationalInterval.add])

def n1105 (b : ℝ) : ℝ := (n1097 b) + (n1101 b)
def i1105 : RationalInterval := ⟨(4924711836169878532491912938273 / 500000000000000000000000000000 : ℚ), (9849423798550374427738220778833 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1105 (b : ℝ) (hb : rootInterval.Contains b) : i1105.Contains (n1105 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1097 b hb) (b1101 b hb))
    (by norm_num [i1105, i1097, i1101, RationalInterval.add]) (by norm_num [i1105, i1097, i1101, RationalInterval.add])

def n1106 (b : ℝ) : ℝ := (n1098 b) + (n1102 b)
def i1106 : RationalInterval := ⟨(1891189210063934367827128287401 / 200000000000000000000000000000 : ℚ), (9455946172005604020949782247447 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1106 (b : ℝ) (hb : rootInterval.Contains b) : i1106.Contains (n1106 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1098 b hb) (b1102 b hb))
    (by norm_num [i1106, i1098, i1102, RationalInterval.add]) (by norm_num [i1106, i1098, i1102, RationalInterval.add])

def n1107 (b : ℝ) : ℝ := (n1099 b) + (n1103 b)
def i1107 : RationalInterval := ⟨(1563606810229664994027881646977 / 250000000000000000000000000000 : ℚ), (781803414924940116015439644153 / 125000000000000000000000000000 : ℚ)⟩
theorem b1107 (b : ℝ) (hb : rootInterval.Contains b) : i1107.Contains (n1107 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1099 b hb) (b1103 b hb))
    (by norm_num [i1107, i1099, i1103, RationalInterval.add]) (by norm_num [i1107, i1099, i1103, RationalInterval.add])

def n1108 (b : ℝ) : ℝ := (n1054 b) * (n931 b)
def i1108 : RationalInterval := ⟨(-381456666184515180786977452677 / 125000000000000000000000000000 : ℚ), (-38145666490654778309246705391 / 12500000000000000000000000000 : ℚ)⟩
theorem b1108 (b : ℝ) (hb : rootInterval.Contains b) : i1108.Contains (n1108 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1054 b hb) (b931 b hb))
    (by norm_num [i1108, i1054, i931, RationalInterval.mul]) (by norm_num [i1108, i1054, i931, RationalInterval.mul])

def n1109 (b : ℝ) : ℝ := (n1054 b) * (n934 b)
def i1109 : RationalInterval := ⟨(-1852802479843782952190130148693 / 1000000000000000000000000000000 : ℚ), (-463200618404951865071445262269 / 250000000000000000000000000000 : ℚ)⟩
theorem b1109 (b : ℝ) (hb : rootInterval.Contains b) : i1109.Contains (n1109 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1054 b hb) (b934 b hb))
    (by norm_num [i1109, i1054, i934, RationalInterval.mul]) (by norm_num [i1109, i1054, i934, RationalInterval.mul])

def n1110 (b : ℝ) : ℝ := (n1055 b) * (n931 b)
def i1110 : RationalInterval := ⟨(-1756111507288244071402840141557 / 1000000000000000000000000000000 : ℚ), (-109756968824677481991121472483 / 62500000000000000000000000000 : ℚ)⟩
theorem b1110 (b : ℝ) (hb : rootInterval.Contains b) : i1110.Contains (n1110 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1055 b hb) (b931 b hb))
    (by norm_num [i1110, i1055, i931, RationalInterval.mul]) (by norm_num [i1110, i1055, i931, RationalInterval.mul])

def n1111 (b : ℝ) : ℝ := (n1055 b) * (n934 b)
def i1111 : RationalInterval := ⟨(-1066218015053640082606175994027 / 1000000000000000000000000000000 : ℚ), (-533109005672229501062439762131 / 500000000000000000000000000000 : ℚ)⟩
theorem b1111 (b : ℝ) (hb : rootInterval.Contains b) : i1111.Contains (n1111 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1055 b hb) (b934 b hb))
    (by norm_num [i1111, i1055, i934, RationalInterval.mul]) (by norm_num [i1111, i1055, i934, RationalInterval.mul])

def n1112 (b : ℝ) : ℝ := (n302 b) * (n1076 b)
def i1112 : RationalInterval := ⟨(17927938633183652107348179557599 / 1000000000000000000000000000000 : ℚ), (17927938818668813668224449911841 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1112 (b : ℝ) (hb : rootInterval.Contains b) : i1112.Contains (n1112 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b302 b hb) (b1076 b hb))
    (by norm_num [i1112, i302, i1076, RationalInterval.mul]) (by norm_num [i1112, i302, i1076, RationalInterval.mul])

def n1113 (b : ℝ) : ℝ := (n302 b) * (n1079 b)
def i1113 : RationalInterval := ⟨(5654374265081727395662885792849 / 500000000000000000000000000000 : ℚ), (11308748645625411481235563296523 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1113 (b : ℝ) (hb : rootInterval.Contains b) : i1113.Contains (n1113 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b302 b hb) (b1079 b hb))
    (by norm_num [i1113, i302, i1079, RationalInterval.mul]) (by norm_num [i1113, i302, i1079, RationalInterval.mul])

def n1114 (b : ℝ) : ℝ := (n303 b) * (n1076 b)
def i1114 : RationalInterval := ⟨(11605535179628001136386666018103 / 1000000000000000000000000000000 : ℚ), (11605535299745214139596164338561 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1114 (b : ℝ) (hb : rootInterval.Contains b) : i1114.Contains (n1114 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b303 b hb) (b1076 b hb))
    (by norm_num [i1114, i303, i1076, RationalInterval.mul]) (by norm_num [i1114, i303, i1076, RationalInterval.mul])

def n1115 (b : ℝ) : ℝ := (n303 b) * (n1079 b)
def i1115 : RationalInterval := ⟨(1464129051194460011743540516387 / 200000000000000000000000000000 : ℚ), (3660322665371989965124198338743 / 500000000000000000000000000000 : ℚ)⟩
theorem b1115 (b : ℝ) (hb : rootInterval.Contains b) : i1115.Contains (n1115 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b303 b hb) (b1079 b hb))
    (by norm_num [i1115, i303, i1079, RationalInterval.mul]) (by norm_num [i1115, i303, i1079, RationalInterval.mul])

def n1116 (b : ℝ) : ℝ := (n1108 b) + (n1112 b)
def i1116 : RationalInterval := ⟨(14876285303707530661052359936183 / 1000000000000000000000000000000 : ℚ), (14876285499416431403484713480561 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1116 (b : ℝ) (hb : rootInterval.Contains b) : i1116.Contains (n1116 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1108 b hb) (b1112 b hb))
    (by norm_num [i1116, i1108, i1112, RationalInterval.add]) (by norm_num [i1116, i1108, i1112, RationalInterval.add])

def n1117 (b : ℝ) : ℝ := (n1109 b) + (n1113 b)
def i1117 : RationalInterval := ⟨(1891189210063934367827128287401 / 200000000000000000000000000000 : ℚ), (9455946172005604020949782247447 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1117 (b : ℝ) (hb : rootInterval.Contains b) : i1117.Contains (n1117 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1109 b hb) (b1113 b hb))
    (by norm_num [i1117, i1109, i1113, RationalInterval.add]) (by norm_num [i1117, i1109, i1113, RationalInterval.add])

def n1118 (b : ℝ) : ℝ := (n1110 b) + (n1114 b)
def i1118 : RationalInterval := ⟨(4924711836169878532491912938273 / 500000000000000000000000000000 : ℚ), (9849423798550374427738220778833 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1118 (b : ℝ) (hb : rootInterval.Contains b) : i1118.Contains (n1118 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1110 b hb) (b1114 b hb))
    (by norm_num [i1118, i1110, i1114, RationalInterval.add]) (by norm_num [i1118, i1110, i1114, RationalInterval.add])

def n1119 (b : ℝ) : ℝ := (n1111 b) + (n1115 b)
def i1119 : RationalInterval := ⟨(1563606810229664994027881646977 / 250000000000000000000000000000 : ℚ), (781803414924940116015439644153 / 125000000000000000000000000000 : ℚ)⟩
theorem b1119 (b : ℝ) (hb : rootInterval.Contains b) : i1119.Contains (n1119 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1111 b hb) (b1115 b hb))
    (by norm_num [i1119, i1111, i1115, RationalInterval.add]) (by norm_num [i1119, i1111, i1115, RationalInterval.add])

def n1120 (b : ℝ) : ℝ := (n1104 b) + (n1116 b)
def i1120 : RationalInterval := ⟨(14876285303707530661052359936183 / 500000000000000000000000000000 : ℚ), (14876285499416431403484713480561 / 500000000000000000000000000000 : ℚ)⟩
theorem b1120 (b : ℝ) (hb : rootInterval.Contains b) : i1120.Contains (n1120 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1104 b hb) (b1116 b hb))
    (by norm_num [i1120, i1104, i1116, RationalInterval.add]) (by norm_num [i1120, i1104, i1116, RationalInterval.add])

def n1121 (b : ℝ) : ℝ := (n1105 b) + (n1117 b)
def i1121 : RationalInterval := ⟨(19305369722659428904119467313551 / 1000000000000000000000000000000 : ℚ), (482634249263899461217200075657 / 25000000000000000000000000000 : ℚ)⟩
theorem b1121 (b : ℝ) (hb : rootInterval.Contains b) : i1121.Contains (n1121 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1105 b hb) (b1117 b hb))
    (by norm_num [i1121, i1105, i1117, RationalInterval.add]) (by norm_num [i1121, i1105, i1117, RationalInterval.add])

def n1122 (b : ℝ) : ℝ := (n1106 b) + (n1118 b)
def i1122 : RationalInterval := ⟨(19305369722659428904119467313551 / 1000000000000000000000000000000 : ℚ), (482634249263899461217200075657 / 25000000000000000000000000000 : ℚ)⟩
theorem b1122 (b : ℝ) (hb : rootInterval.Contains b) : i1122.Contains (n1122 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1106 b hb) (b1118 b hb))
    (by norm_num [i1122, i1106, i1118, RationalInterval.add]) (by norm_num [i1122, i1106, i1118, RationalInterval.add])

def n1123 (b : ℝ) : ℝ := (n1107 b) + (n1119 b)
def i1123 : RationalInterval := ⟨(1563606810229664994027881646977 / 125000000000000000000000000000 : ℚ), (781803414924940116015439644153 / 62500000000000000000000000000 : ℚ)⟩
theorem b1123 (b : ℝ) (hb : rootInterval.Contains b) : i1123.Contains (n1123 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1107 b hb) (b1119 b hb))
    (by norm_num [i1123, i1107, i1119, RationalInterval.add]) (by norm_num [i1123, i1107, i1119, RationalInterval.add])

def n1124 (b : ℝ) : ℝ := (n1005 b) * (n1120 b)
def i1124 : RationalInterval := ⟨(-3201669493147896997336685307589 / 250000000000000000000000000000 : ℚ), (-12806677798226428559758403365819 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1124 (b : ℝ) (hb : rootInterval.Contains b) : i1124.Contains (n1124 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1005 b hb) (b1120 b hb))
    (by norm_num [i1124, i1005, i1120, RationalInterval.mul]) (by norm_num [i1124, i1005, i1120, RationalInterval.mul])

def n1125 (b : ℝ) : ℝ := (n1005 b) * (n1121 b)
def i1125 : RationalInterval := ⟨(-2077447831015587101000712569867 / 250000000000000000000000000000 : ℚ), (-8309791213540305028344782938371 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1125 (b : ℝ) (hb : rootInterval.Contains b) : i1125.Contains (n1125 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1005 b hb) (b1121 b hb))
    (by norm_num [i1125, i1005, i1121, RationalInterval.mul]) (by norm_num [i1125, i1005, i1121, RationalInterval.mul])

def n1126 (b : ℝ) : ℝ := (n1005 b) * (n1122 b)
def i1126 : RationalInterval := ⟨(-2077447831015587101000712569867 / 250000000000000000000000000000 : ℚ), (-8309791213540305028344782938371 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1126 (b : ℝ) (hb : rootInterval.Contains b) : i1126.Contains (n1126 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1005 b hb) (b1122 b hb))
    (by norm_num [i1126, i1005, i1122, RationalInterval.mul]) (by norm_num [i1126, i1005, i1122, RationalInterval.mul])

def n1127 (b : ℝ) : ℝ := (n1005 b) * (n1123 b)
def i1127 : RationalInterval := ⟨(-336518970854951524509902086441 / 62500000000000000000000000000 : ℚ), (-2692151731821555970440630650671 / 500000000000000000000000000000 : ℚ)⟩
theorem b1127 (b : ℝ) (hb : rootInterval.Contains b) : i1127.Contains (n1127 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1005 b hb) (b1123 b hb))
    (by norm_num [i1127, i1005, i1123, RationalInterval.mul]) (by norm_num [i1127, i1005, i1123, RationalInterval.mul])

def n1128 (b : ℝ) : ℝ := (n1073 b) * (n1011 b)
def i1128 : RationalInterval := ⟨(1245451383987829529256018432769 / 1000000000000000000000000000000 : ℚ), (1245451400996587029679261018053 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1128 (b : ℝ) (hb : rootInterval.Contains b) : i1128.Contains (n1128 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1073 b hb) (b1011 b hb))
    (by norm_num [i1128, i1073, i1011, RationalInterval.mul]) (by norm_num [i1128, i1073, i1011, RationalInterval.mul])

def n1129 (b : ℝ) : ℝ := (n1128 b) * (n946 b)
def i1129 : RationalInterval := ⟨(1351353634196332931847414735109 / 100000000000000000000000000000 : ℚ), (13513536532695712006253140335471 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1129 (b : ℝ) (hb : rootInterval.Contains b) : i1129.Contains (n1129 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1128 b hb) (b946 b hb))
    (by norm_num [i1129, i1128, i946, RationalInterval.mul]) (by norm_num [i1129, i1128, i946, RationalInterval.mul])

def n1130 (b : ℝ) : ℝ := (n1128 b) * (n947 b)
def i1130 : RationalInterval := ⟨(2119075605125636230416446757573 / 250000000000000000000000000000 : ℚ), (2119075635048059287910526929757 / 250000000000000000000000000000 : ℚ)⟩
theorem b1130 (b : ℝ) (hb : rootInterval.Contains b) : i1130.Contains (n1130 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1128 b hb) (b947 b hb))
    (by norm_num [i1130, i1128, i947, RationalInterval.mul]) (by norm_num [i1130, i1128, i947, RationalInterval.mul])

def n1131 (b : ℝ) : ℝ := (n1128 b) * (n948 b)
def i1131 : RationalInterval := ⟨(2119075605125636230416446757573 / 250000000000000000000000000000 : ℚ), (2119075635048059287910526929757 / 250000000000000000000000000000 : ℚ)⟩
theorem b1131 (b : ℝ) (hb : rootInterval.Contains b) : i1131.Contains (n1131 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1128 b hb) (b948 b hb))
    (by norm_num [i1131, i1128, i948, RationalInterval.mul]) (by norm_num [i1131, i1128, i948, RationalInterval.mul])

def n1132 (b : ℝ) : ℝ := (n1128 b) * (n949 b)
def i1132 : RationalInterval := ⟨(5311262385271096856677105221677 / 1000000000000000000000000000000 : ℚ), (132781561507583527705009440671 / 25000000000000000000000000000 : ℚ)⟩
theorem b1132 (b : ℝ) (hb : rootInterval.Contains b) : i1132.Contains (n1132 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1128 b hb) (b949 b hb))
    (by norm_num [i1132, i1128, i949, RationalInterval.mul]) (by norm_num [i1132, i1128, i949, RationalInterval.mul])

def n1133 (b : ℝ) : ℝ := (n1124 b) + (n1129 b)
def i1133 : RationalInterval := ⟨(353429184685870664563703060367 / 500000000000000000000000000000 : ℚ), (176714683617320861623684242413 / 250000000000000000000000000000 : ℚ)⟩
theorem b1133 (b : ℝ) (hb : rootInterval.Contains b) : i1133.Contains (n1133 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1124 b hb) (b1129 b hb))
    (by norm_num [i1133, i1124, i1129, RationalInterval.add]) (by norm_num [i1133, i1124, i1129, RationalInterval.add])

def n1134 (b : ℝ) : ℝ := (n1125 b) + (n1130 b)
def i1134 : RationalInterval := ⟨(20813887055024564707867093853 / 125000000000000000000000000000 : ℚ), (166511326651932123297324780657 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1134 (b : ℝ) (hb : rootInterval.Contains b) : i1134.Contains (n1134 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1125 b hb) (b1130 b hb))
    (by norm_num [i1134, i1125, i1130, RationalInterval.add]) (by norm_num [i1134, i1125, i1130, RationalInterval.add])

def n1135 (b : ℝ) : ℝ := (n1126 b) + (n1131 b)
def i1135 : RationalInterval := ⟨(20813887055024564707867093853 / 125000000000000000000000000000 : ℚ), (166511326651932123297324780657 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1135 (b : ℝ) (hb : rootInterval.Contains b) : i1135.Contains (n1135 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1126 b hb) (b1131 b hb))
    (by norm_num [i1135, i1126, i1131, RationalInterval.add]) (by norm_num [i1135, i1126, i1131, RationalInterval.add])

def n1136 (b : ℝ) : ℝ := (n1127 b) + (n1132 b)
def i1136 : RationalInterval := ⟨(-73041148408127535481328161379 / 1000000000000000000000000000000 : ℚ), (-36520501669885416340441837251 / 500000000000000000000000000000 : ℚ)⟩
theorem b1136 (b : ℝ) (hb : rootInterval.Contains b) : i1136.Contains (n1136 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1127 b hb) (b1132 b hb))
    (by norm_num [i1136, i1127, i1132, RationalInterval.add]) (by norm_num [i1136, i1127, i1132, RationalInterval.add])

def n1137 (b : ℝ) : ℝ := (n1073 b) + (n1083 b)
def i1137 : RationalInterval := ⟨(47776717979939822033241133655373 / 1000000000000000000000000000000 : ℚ), (23888359253244695413207936704287 / 500000000000000000000000000000 : ℚ)⟩
theorem b1137 (b : ℝ) (hb : rootInterval.Contains b) : i1137.Contains (n1137 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1073 b hb) (b1083 b hb))
    (by norm_num [i1137, i1073, i1083, RationalInterval.add]) (by norm_num [i1137, i1073, i1083, RationalInterval.add])

def n1138 (b : ℝ) : ℝ := (n1137 b) * (n1011 b)
def i1138 : RationalInterval := ⟨(8851977271497498141081850336927 / 1000000000000000000000000000000 : ℚ), (4425988688594482952458769842989 / 500000000000000000000000000000 : ℚ)⟩
theorem b1138 (b : ℝ) (hb : rootInterval.Contains b) : i1138.Contains (n1138 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1137 b hb) (b1011 b hb))
    (by norm_num [i1138, i1137, i1011, RationalInterval.mul]) (by norm_num [i1138, i1137, i1011, RationalInterval.mul])

def n1139 (b : ℝ) : ℝ := (n1024 b) * (n1073 b)
def i1139 : RationalInterval := ⟨(56813915632331080959017605706141 / 500000000000000000000000000000 : ℚ), (5681391640030541881152075984119 / 50000000000000000000000000000 : ℚ)⟩
theorem b1139 (b : ℝ) (hb : rootInterval.Contains b) : i1139.Contains (n1139 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1024 b hb) (b1073 b hb))
    (by norm_num [i1139, i1024, i1073, RationalInterval.mul]) (by norm_num [i1139, i1024, i1073, RationalInterval.mul])

def n1140 (b : ℝ) : ℝ := (n1139 b) * (n1027 b)
def i1140 : RationalInterval := ⟨(9061929602016713406897846670111 / 1000000000000000000000000000000 : ℚ), (4530964868499777344941854650081 / 500000000000000000000000000000 : ℚ)⟩
theorem b1140 (b : ℝ) (hb : rootInterval.Contains b) : i1140.Contains (n1140 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1139 b hb) (b1027 b hb))
    (by norm_num [i1140, i1139, i1027, RationalInterval.mul]) (by norm_num [i1140, i1139, i1027, RationalInterval.mul])

def n1141 (b : ℝ) : ℝ := -(n1140 b)
def i1141 : RationalInterval := ⟨(-4530964868499777344941854650081 / 500000000000000000000000000000 : ℚ), (-9061929602016713406897846670111 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1141 (b : ℝ) (hb : rootInterval.Contains b) : i1141.Contains (n1141 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b1140 b hb))
    (by norm_num [i1141, i1140, RationalInterval.neg]) (by norm_num [i1141, i1140, RationalInterval.neg])

def n1142 (b : ℝ) : ℝ := (n1138 b) + (n1141 b)
def i1142 : RationalInterval := ⟨(-41990493100411309760371792647 / 200000000000000000000000000000 : ℚ), (-209952224827747501980306984133 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1142 (b : ℝ) (hb : rootInterval.Contains b) : i1142.Contains (n1142 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1138 b hb) (b1141 b hb))
    (by norm_num [i1142, i1138, i1141, RationalInterval.add]) (by norm_num [i1142, i1138, i1141, RationalInterval.add])

def n1143 (b : ℝ) : ℝ := (n1142 b) * (n950 b)
def i1143 : RationalInterval := ⟨(-52755446400499018554831214077 / 125000000000000000000000000000 : ℚ), (-13188846481182446442413979283 / 31250000000000000000000000000 : ℚ)⟩
theorem b1143 (b : ℝ) (hb : rootInterval.Contains b) : i1143.Contains (n1143 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1142 b hb) (b950 b hb))
    (by norm_num [i1143, i1142, i950, RationalInterval.mul]) (by norm_num [i1143, i1142, i950, RationalInterval.mul])

def n1144 (b : ℝ) : ℝ := (n1142 b) * (n951 b)
def i1144 : RationalInterval := ⟨(-6830179438332879844251105379 / 25000000000000000000000000000 : ℚ), (-54641372868695855499276395337 / 200000000000000000000000000000 : ℚ)⟩
theorem b1144 (b : ℝ) (hb : rootInterval.Contains b) : i1144.Contains (n1144 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1142 b hb) (b951 b hb))
    (by norm_num [i1144, i1142, i951, RationalInterval.mul]) (by norm_num [i1144, i1142, i951, RationalInterval.mul])

def n1145 (b : ℝ) : ℝ := (n1142 b) * (n952 b)
def i1145 : RationalInterval := ⟨(-6830179438332879844251105379 / 25000000000000000000000000000 : ℚ), (-54641372868695855499276395337 / 200000000000000000000000000000 : ℚ)⟩
theorem b1145 (b : ℝ) (hb : rootInterval.Contains b) : i1145.Contains (n1145 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1142 b hb) (b952 b hb))
    (by norm_num [i1145, i1142, i952, RationalInterval.mul]) (by norm_num [i1145, i1142, i952, RationalInterval.mul])

def n1146 (b : ℝ) : ℝ := (n1142 b) * (n953 b)
def i1146 : RationalInterval := ⟨(-11053681264884523518868966157 / 62500000000000000000000000000 : ℚ), (-44214674374014286082648340587 / 250000000000000000000000000000 : ℚ)⟩
theorem b1146 (b : ℝ) (hb : rootInterval.Contains b) : i1146.Contains (n1146 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1142 b hb) (b953 b hb))
    (by norm_num [i1146, i1142, i953, RationalInterval.mul]) (by norm_num [i1146, i1142, i953, RationalInterval.mul])

def n1147 (b : ℝ) : ℝ := (n1133 b) + (n1143 b)
def i1147 : RationalInterval := ⟨(142407399083874590344378204059 / 500000000000000000000000000000 : ℚ), (71203911767861290084372408149 / 250000000000000000000000000000 : ℚ)⟩
theorem b1147 (b : ℝ) (hb : rootInterval.Contains b) : i1147.Contains (n1147 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1133 b hb) (b1143 b hb))
    (by norm_num [i1147, i1133, i1143, RationalInterval.add]) (by norm_num [i1147, i1133, i1143, RationalInterval.add])

def n1148 (b : ℝ) : ℝ := (n1134 b) + (n1144 b)
def i1148 : RationalInterval := ⟨(-6668505068319917256694216521 / 62500000000000000000000000000 : ℚ), (-26673884422886788549764299007 / 250000000000000000000000000000 : ℚ)⟩
theorem b1148 (b : ℝ) (hb : rootInterval.Contains b) : i1148.Contains (n1148 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1134 b hb) (b1144 b hb))
    (by norm_num [i1148, i1134, i1144, RationalInterval.add]) (by norm_num [i1148, i1134, i1144, RationalInterval.add])

def n1149 (b : ℝ) : ℝ := (n1135 b) + (n1145 b)
def i1149 : RationalInterval := ⟨(-6668505068319917256694216521 / 62500000000000000000000000000 : ℚ), (-26673884422886788549764299007 / 250000000000000000000000000000 : ℚ)⟩
theorem b1149 (b : ℝ) (hb : rootInterval.Contains b) : i1149.Contains (n1149 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1135 b hb) (b1145 b hb))
    (by norm_num [i1149, i1135, i1145, RationalInterval.add]) (by norm_num [i1149, i1135, i1145, RationalInterval.add])

def n1150 (b : ℝ) : ℝ := (n1136 b) + (n1146 b)
def i1150 : RationalInterval := ⟨(-249900048646279911783231619891 / 1000000000000000000000000000000 : ℚ), (-4997994016716559540229540737 / 20000000000000000000000000000 : ℚ)⟩
theorem b1150 (b : ℝ) (hb : rootInterval.Contains b) : i1150.Contains (n1150 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1136 b hb) (b1146 b hb))
    (by norm_num [i1150, i1136, i1146, RationalInterval.add]) (by norm_num [i1150, i1136, i1146, RationalInterval.add])

def n1151 (b : ℝ) : ℝ := (n1039 b) * (n1092 b)
def i1151 : RationalInterval := ⟨(-3541319910560162318973338252231 / 1000000000000000000000000000000 : ℚ), (-1770659947125890940140420850589 / 500000000000000000000000000000 : ℚ)⟩
theorem b1151 (b : ℝ) (hb : rootInterval.Contains b) : i1151.Contains (n1151 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1039 b hb) (b1092 b hb))
    (by norm_num [i1151, i1039, i1092, RationalInterval.mul]) (by norm_num [i1151, i1039, i1092, RationalInterval.mul])

def n1152 (b : ℝ) : ℝ := (n1039 b) * (n1093 b)
def i1152 : RationalInterval := ⟨(-2165173362913544367098434729797 / 1000000000000000000000000000000 : ℚ), (-2165173352816284291315077003989 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1152 (b : ℝ) (hb : rootInterval.Contains b) : i1152.Contains (n1152 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1039 b hb) (b1093 b hb))
    (by norm_num [i1152, i1039, i1093, RationalInterval.mul]) (by norm_num [i1152, i1039, i1093, RationalInterval.mul])

def n1153 (b : ℝ) : ℝ := (n1039 b) * (n1094 b)
def i1153 : RationalInterval := ⟨(-2165173362913544367098434729797 / 1000000000000000000000000000000 : ℚ), (-2165173352816284291315077003989 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1153 (b : ℝ) (hb : rootInterval.Contains b) : i1153.Contains (n1153 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1039 b hb) (b1094 b hb))
    (by norm_num [i1153, i1039, i1094, RationalInterval.mul]) (by norm_num [i1153, i1039, i1094, RationalInterval.mul])

def n1154 (b : ℝ) : ℝ := (n1039 b) * (n1095 b)
def i1154 : RationalInterval := ⟨(-164902364328871290346490243151 / 125000000000000000000000000000 : ℚ), (-1319218908392897807908459371753 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1154 (b : ℝ) (hb : rootInterval.Contains b) : i1154.Contains (n1154 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1039 b hb) (b1095 b hb))
    (by norm_num [i1154, i1039, i1095, RationalInterval.mul]) (by norm_num [i1154, i1039, i1095, RationalInterval.mul])

def n1155 (b : ℝ) : ℝ := (n1147 b) + (n1151 b)
def i1155 : RationalInterval := ⟨(-3256505112392413138284581844113 / 1000000000000000000000000000000 : ℚ), (-1628252123590168359971676034291 / 500000000000000000000000000000 : ℚ)⟩
theorem b1155 (b : ℝ) (hb : rootInterval.Contains b) : i1155.Contains (n1155 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1147 b hb) (b1151 b hb))
    (by norm_num [i1155, i1147, i1151, RationalInterval.add]) (by norm_num [i1155, i1147, i1151, RationalInterval.add])

def n1156 (b : ℝ) : ℝ := (n1148 b) + (n1152 b)
def i1156 : RationalInterval := ⟨(-2271869444006663043205542194133 / 1000000000000000000000000000000 : ℚ), (-2271868890507831445514134200017 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1156 (b : ℝ) (hb : rootInterval.Contains b) : i1156.Contains (n1156 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1148 b hb) (b1152 b hb))
    (by norm_num [i1156, i1148, i1152, RationalInterval.add]) (by norm_num [i1156, i1148, i1152, RationalInterval.add])

def n1157 (b : ℝ) : ℝ := (n1149 b) + (n1153 b)
def i1157 : RationalInterval := ⟨(-2271869444006663043205542194133 / 1000000000000000000000000000000 : ℚ), (-2271868890507831445514134200017 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1157 (b : ℝ) (hb : rootInterval.Contains b) : i1157.Contains (n1157 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1149 b hb) (b1153 b hb))
    (by norm_num [i1157, i1149, i1153, RationalInterval.add]) (by norm_num [i1157, i1149, i1153, RationalInterval.add])

def n1158 (b : ℝ) : ℝ := (n1150 b) + (n1154 b)
def i1158 : RationalInterval := ⟨(-1569118963277250234555153565099 / 1000000000000000000000000000000 : ℚ), (-1569118609228725784919936408603 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1158 (b : ℝ) (hb : rootInterval.Contains b) : i1158.Contains (n1158 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1150 b hb) (b1154 b hb))
    (by norm_num [i1158, i1150, i1154, RationalInterval.add]) (by norm_num [i1158, i1150, i1154, RationalInterval.add])

def n1159 (b : ℝ) : ℝ := (n21 b) * (n21 b)
def i1159 : RationalInterval := ⟨(27242127028831210019471365943 / 25000000000000000000000000000 : ℚ), (136210635242114574045585581681 / 125000000000000000000000000000 : ℚ)⟩
theorem b1159 (b : ℝ) (hb : rootInterval.Contains b) : i1159.Contains (n1159 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b21 b hb) (b21 b hb))
    (by norm_num [i1159, i21, i21, RationalInterval.mul]) (by norm_num [i1159, i21, i21, RationalInterval.mul])

def n1160 (b : ℝ) : ℝ := (n21 b) * (n303 b)
def i1160 : RationalInterval := ⟨(95808374754031791198997746787 / 100000000000000000000000000000 : ℚ), (239520936973817244581307408341 / 250000000000000000000000000000 : ℚ)⟩
theorem b1160 (b : ℝ) (hb : rootInterval.Contains b) : i1160.Contains (n1160 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b21 b hb) (b303 b hb))
    (by norm_num [i1160, i21, i303, RationalInterval.mul]) (by norm_num [i1160, i21, i303, RationalInterval.mul])

def n1161 (b : ℝ) : ℝ := (n303 b) * (n21 b)
def i1161 : RationalInterval := ⟨(95808374754031791198997746787 / 100000000000000000000000000000 : ℚ), (239520936973817244581307408341 / 250000000000000000000000000000 : ℚ)⟩
theorem b1161 (b : ℝ) (hb : rootInterval.Contains b) : i1161.Contains (n1161 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b303 b hb) (b21 b hb))
    (by norm_num [i1161, i303, i21, RationalInterval.mul]) (by norm_num [i1161, i303, i21, RationalInterval.mul])

def n1162 (b : ℝ) : ℝ := (n362 b) + (n321 b)
def i1162 : RationalInterval := ⟨(59200946326040969142697862491 / 20000000000000000000000000000 : ℚ), (11562684833544194587273828921 / 3906250000000000000000000000 : ℚ)⟩
theorem b1162 (b : ℝ) (hb : rootInterval.Contains b) : i1162.Contains (n1162 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b362 b hb) (b321 b hb))
    (by norm_num [i1162, i362, i321, RationalInterval.add]) (by norm_num [i1162, i362, i321, RationalInterval.add])

def n1163 (b : ℝ) : ℝ := (n1005 b) * (n1162 b)
def i1163 : RationalInterval := ⟨(-637060454017570561539645565723 / 500000000000000000000000000000 : ℚ), (-1274120906982655207328691061953 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1163 (b : ℝ) (hb : rootInterval.Contains b) : i1163.Contains (n1163 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1005 b hb) (b1162 b hb))
    (by norm_num [i1163, i1005, i1162, RationalInterval.mul]) (by norm_num [i1163, i1005, i1162, RationalInterval.mul])

def n1164 (b : ℝ) : ℝ := (n1005 b) * (n1160 b)
def i1164 : RationalInterval := ⟨(-412396966653727412795699919061 / 1000000000000000000000000000000 : ℚ), (-412396966311482855272265135709 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1164 (b : ℝ) (hb : rootInterval.Contains b) : i1164.Contains (n1164 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1005 b hb) (b1160 b hb))
    (by norm_num [i1164, i1005, i1160, RationalInterval.mul]) (by norm_num [i1164, i1005, i1160, RationalInterval.mul])

def n1165 (b : ℝ) : ℝ := (n1005 b) * (n1161 b)
def i1165 : RationalInterval := ⟨(-412396966653727412795699919061 / 1000000000000000000000000000000 : ℚ), (-412396966311482855272265135709 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1165 (b : ℝ) (hb : rootInterval.Contains b) : i1165.Contains (n1165 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1005 b hb) (b1161 b hb))
    (by norm_num [i1165, i1005, i1161, RationalInterval.mul]) (by norm_num [i1165, i1005, i1161, RationalInterval.mul])

def n1166 (b : ℝ) : ℝ := (n1163 b) + (n15 b)
def i1166 : RationalInterval := ⟨(-137060454017570561539645565723 / 500000000000000000000000000000 : ℚ), (-274120906982655207328691061953 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1166 (b : ℝ) (hb : rootInterval.Contains b) : i1166.Contains (n1166 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1163 b hb) (b15 b hb))
    (by norm_num [i1166, i1163, i15, RationalInterval.add]) (by norm_num [i1166, i1163, i15, RationalInterval.add])

def n1167 (b : ℝ) : ℝ := (n1159 b) * (n1011 b)
def i1167 : RationalInterval := ⟨(201894729887233062468595932377 / 1000000000000000000000000000000 : ℚ), (100947365108967420336261670247 / 500000000000000000000000000000 : ℚ)⟩
theorem b1167 (b : ℝ) (hb : rootInterval.Contains b) : i1167.Contains (n1167 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1159 b hb) (b1011 b hb))
    (by norm_num [i1167, i1159, i1011, RationalInterval.mul]) (by norm_num [i1167, i1159, i1011, RationalInterval.mul])

def n1168 (b : ℝ) : ℝ := (n1167 b) * (n950 b)
def i1168 : RationalInterval := ⟨(202923010701287990382513830973 / 500000000000000000000000000000 : ℚ), (405846022073073135823271810831 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1168 (b : ℝ) (hb : rootInterval.Contains b) : i1168.Contains (n1168 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1167 b hb) (b950 b hb))
    (by norm_num [i1168, i1167, i950, RationalInterval.mul]) (by norm_num [i1168, i1167, i950, RationalInterval.mul])

def n1169 (b : ℝ) : ℝ := (n1167 b) * (n951 b)
def i1169 : RationalInterval := ⟨(16420112398552563756109335619 / 62500000000000000000000000000 : ℚ), (262721798811892492669226477441 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1169 (b : ℝ) (hb : rootInterval.Contains b) : i1169.Contains (n1169 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1167 b hb) (b951 b hb))
    (by norm_num [i1169, i1167, i951, RationalInterval.mul]) (by norm_num [i1169, i1167, i951, RationalInterval.mul])

