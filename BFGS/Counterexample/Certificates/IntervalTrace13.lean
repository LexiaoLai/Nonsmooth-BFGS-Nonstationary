import BFGS.Counterexample.Certificates.IntervalTrace12

/-! Generated arithmetic proofs. Each bound is checked by the Lean kernel. -/
namespace BFGS.Counterexample.Trace
noncomputable section
open BFGS RationalInterval
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false

def n1170 (b : ℝ) : ℝ := (n1167 b) * (n952 b)
def i1170 : RationalInterval := ⟨(16420112398552563756109335619 / 62500000000000000000000000000 : ℚ), (262721798811892492669226477441 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1170 (b : ℝ) (hb : rootInterval.Contains b) : i1170.Contains (n1170 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1167 b hb) (b952 b hb))
    (by norm_num [i1170, i1167, i952, RationalInterval.mul]) (by norm_num [i1170, i1167, i952, RationalInterval.mul])

def n1171 (b : ℝ) : ℝ := (n1167 b) * (n953 b)
def i1171 : RationalInterval := ⟨(42517814455728581261905015239 / 250000000000000000000000000000 : ℚ), (6802850324207822387332479167 / 40000000000000000000000000000 : ℚ)⟩
theorem b1171 (b : ℝ) (hb : rootInterval.Contains b) : i1171.Contains (n1171 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1167 b hb) (b953 b hb))
    (by norm_num [i1171, i1167, i953, RationalInterval.mul]) (by norm_num [i1171, i1167, i953, RationalInterval.mul])

def n1172 (b : ℝ) : ℝ := (n1166 b) + (n1168 b)
def i1172 : RationalInterval := ⟨(263450226734869715371473061 / 2000000000000000000000000000 : ℚ), (65862557545208964247290374439 / 500000000000000000000000000000 : ℚ)⟩
theorem b1172 (b : ℝ) (hb : rootInterval.Contains b) : i1172.Contains (n1172 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1166 b hb) (b1168 b hb))
    (by norm_num [i1172, i1166, i1168, RationalInterval.add]) (by norm_num [i1172, i1166, i1168, RationalInterval.add])

def n1173 (b : ℝ) : ℝ := (n1164 b) + (n1169 b)
def i1173 : RationalInterval := ⟨(-149675168276886392697950549157 / 1000000000000000000000000000000 : ℚ), (-37418791874897590650759664567 / 250000000000000000000000000000 : ℚ)⟩
theorem b1173 (b : ℝ) (hb : rootInterval.Contains b) : i1173.Contains (n1173 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1164 b hb) (b1169 b hb))
    (by norm_num [i1173, i1164, i1169, RationalInterval.add]) (by norm_num [i1173, i1164, i1169, RationalInterval.add])

def n1174 (b : ℝ) : ℝ := (n1165 b) + (n1170 b)
def i1174 : RationalInterval := ⟨(-149675168276886392697950549157 / 1000000000000000000000000000000 : ℚ), (-37418791874897590650759664567 / 250000000000000000000000000000 : ℚ)⟩
theorem b1174 (b : ℝ) (hb : rootInterval.Contains b) : i1174.Contains (n1174 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1165 b hb) (b1170 b hb))
    (by norm_num [i1174, i1165, i1170, RationalInterval.add]) (by norm_num [i1174, i1165, i1170, RationalInterval.add])

def n1175 (b : ℝ) : ℝ := (n210 b) * (n16 b)
def i1175 : RationalInterval := ⟨(304015598171090167181267651997 / 1000000000000000000000000000000 : ℚ), (304015602318281222815061084761 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1175 (b : ℝ) (hb : rootInterval.Contains b) : i1175.Contains (n1175 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b210 b hb) (b16 b hb))
    (by norm_num [i1175, i210, i16, RationalInterval.mul]) (by norm_num [i1175, i210, i16, RationalInterval.mul])

def n1176 (b : ℝ) : ℝ := (n212 b) * (n16 b)
def i1176 : RationalInterval := ⟨(1074261822854187343377343754867 / 1000000000000000000000000000000 : ℚ), (134282729226210685066719959941 / 125000000000000000000000000000 : ℚ)⟩
theorem b1176 (b : ℝ) (hb : rootInterval.Contains b) : i1176.Contains (n1176 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b212 b hb) (b16 b hb))
    (by norm_num [i1176, i212, i16, RationalInterval.mul]) (by norm_num [i1176, i212, i16, RationalInterval.mul])

def n1177 (b : ℝ) : ℝ := (n16 b) * (n21 b)
def i1177 : RationalInterval := ⟨(1043879821221412633154938188809 / 1000000000000000000000000000000 : ℚ), (130484977699596982211455117131 / 125000000000000000000000000000 : ℚ)⟩
theorem b1177 (b : ℝ) (hb : rootInterval.Contains b) : i1177.Contains (n1177 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b16 b hb) (b21 b hb))
    (by norm_num [i1177, i16, i21, RationalInterval.mul]) (by norm_num [i1177, i16, i21, RationalInterval.mul])

def n1178 (b : ℝ) : ℝ := (n302 b) * (n1175 b)
def i1178 : RationalInterval := ⟨(-53879560023824118559282834013 / 125000000000000000000000000000 : ℚ), (-431036474307622217657026164549 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1178 (b : ℝ) (hb : rootInterval.Contains b) : i1178.Contains (n1178 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b302 b hb) (b1175 b hb))
    (by norm_num [i1178, i302, i1175, RationalInterval.mul]) (by norm_num [i1178, i302, i1175, RationalInterval.mul])

def n1179 (b : ℝ) : ℝ := (n303 b) * (n1176 b)
def i1179 : RationalInterval := ⟨(-197193734884702928490401684503 / 200000000000000000000000000000 : ℚ), (-985968664357701988239091031957 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1179 (b : ℝ) (hb : rootInterval.Contains b) : i1179.Contains (n1179 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b303 b hb) (b1176 b hb))
    (by norm_num [i1179, i303, i1176, RationalInterval.mul]) (by norm_num [i1179, i303, i1176, RationalInterval.mul])

def n1180 (b : ℝ) : ℝ := (n1178 b) + (n1179 b)
def i1180 : RationalInterval := ⟨(-1417005154614107590926271094619 / 1000000000000000000000000000000 : ℚ), (-708502569332662102948058598253 / 500000000000000000000000000000 : ℚ)⟩
theorem b1180 (b : ℝ) (hb : rootInterval.Contains b) : i1180.Contains (n1180 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1178 b hb) (b1179 b hb))
    (by norm_num [i1180, i1178, i1179, RationalInterval.add]) (by norm_num [i1180, i1178, i1179, RationalInterval.add])

def n1181 (b : ℝ) : ℝ := (n1177 b) + (n1180 b)
def i1181 : RationalInterval := ⟨(-37312533339269495777133290581 / 100000000000000000000000000000 : ℚ), (-186562658534274174102238129729 / 500000000000000000000000000000 : ℚ)⟩
theorem b1181 (b : ℝ) (hb : rootInterval.Contains b) : i1181.Contains (n1181 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1177 b hb) (b1180 b hb))
    (by norm_num [i1181, i1177, i1180, RationalInterval.add]) (by norm_num [i1181, i1177, i1180, RationalInterval.add])

def n1182 (b : ℝ) : ℝ := (n63 b) * (n1175 b)
def i1182 : RationalInterval := ⟨(367526036239356192419146908273 / 500000000000000000000000000000 : ℚ), (147010416501774834257864751373 / 200000000000000000000000000000 : ℚ)⟩
theorem b1182 (b : ℝ) (hb : rootInterval.Contains b) : i1182.Contains (n1182 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b63 b hb) (b1175 b hb))
    (by norm_num [i1182, i63, i1175, RationalInterval.mul]) (by norm_num [i1182, i63, i1175, RationalInterval.mul])

def n1183 (b : ℝ) : ℝ := (n65 b) * (n1176 b)
def i1183 : RationalInterval := ⟨(152309957578479565992776290939 / 100000000000000000000000000000 : ℚ), (1523099591328357382718888262279 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1183 (b : ℝ) (hb : rootInterval.Contains b) : i1183.Contains (n1183 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b65 b hb) (b1176 b hb))
    (by norm_num [i1183, i65, i1176, RationalInterval.mul]) (by norm_num [i1183, i65, i1176, RationalInterval.mul])

def n1184 (b : ℝ) : ℝ := (n1182 b) + (n1183 b)
def i1184 : RationalInterval := ⟨(141134478016469252797878545371 / 62500000000000000000000000000 : ℚ), (282268959229653944251026502393 / 125000000000000000000000000000 : ℚ)⟩
theorem b1184 (b : ℝ) (hb : rootInterval.Contains b) : i1184.Contains (n1184 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1182 b hb) (b1183 b hb))
    (by norm_num [i1184, i1182, i1183, RationalInterval.add]) (by norm_num [i1184, i1182, i1183, RationalInterval.add])

def n1185 (b : ℝ) : ℝ := (n65 b) * (n1175 b)
def i1185 : RationalInterval := ⟨(431036474307622217657026164549 / 1000000000000000000000000000000 : ℚ), (53879560023824118559282834013 / 125000000000000000000000000000 : ℚ)⟩
theorem b1185 (b : ℝ) (hb : rootInterval.Contains b) : i1185.Contains (n1185 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b65 b hb) (b1175 b hb))
    (by norm_num [i1185, i65, i1175, RationalInterval.mul]) (by norm_num [i1185, i65, i1175, RationalInterval.mul])

def n1186 (b : ℝ) : ℝ := (n0 b) * (n1176 b)
def i1186 : RationalInterval := ⟨(985968664357701988239091031957 / 1000000000000000000000000000000 : ℚ), (197193734884702928490401684503 / 200000000000000000000000000000 : ℚ)⟩
theorem b1186 (b : ℝ) (hb : rootInterval.Contains b) : i1186.Contains (n1186 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b0 b hb) (b1176 b hb))
    (by norm_num [i1186, i0, i1176, RationalInterval.mul]) (by norm_num [i1186, i0, i1176, RationalInterval.mul])

def n1187 (b : ℝ) : ℝ := (n1185 b) + (n1186 b)
def i1187 : RationalInterval := ⟨(708502569332662102948058598253 / 500000000000000000000000000000 : ℚ), (1417005154614107590926271094619 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1187 (b : ℝ) (hb : rootInterval.Contains b) : i1187.Contains (n1187 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1185 b hb) (b1186 b hb))
    (by norm_num [i1187, i1185, i1186, RationalInterval.add]) (by norm_num [i1187, i1185, i1186, RationalInterval.add])

def n1188 (b : ℝ) : ℝ := (n320 b) + (n1184 b)
def i1188 : RationalInterval := ⟨(669730460774316420475422663797 / 500000000000000000000000000000 : ℚ), (1339460947684005238192593027529 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1188 (b : ℝ) (hb : rootInterval.Contains b) : i1188.Contains (n1188 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b320 b hb) (b1184 b hb))
    (by norm_num [i1188, i320, i1184, RationalInterval.add]) (by norm_num [i1188, i320, i1184, RationalInterval.add])

def n1189 (b : ℝ) : ℝ := (n21 b) + (n1187 b)
def i1189 : RationalInterval := ⟨(186562658534274174102238129729 / 500000000000000000000000000000 : ℚ), (37312533339269495777133290581 / 100000000000000000000000000000 : ℚ)⟩
theorem b1189 (b : ℝ) (hb : rootInterval.Contains b) : i1189.Contains (n1189 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b21 b hb) (b1187 b hb))
    (by norm_num [i1189, i21, i1187, RationalInterval.add]) (by norm_num [i1189, i21, i1187, RationalInterval.add])

def n1190 (b : ℝ) : ℝ := (n1175 b) * (n931 b)
def i1190 : RationalInterval := ⟨(-1163295253980619883656625258363 / 1000000000000000000000000000000 : ℚ), (-1163295237587703058882361494987 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1190 (b : ℝ) (hb : rootInterval.Contains b) : i1190.Contains (n1190 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1175 b hb) (b931 b hb))
    (by norm_num [i1190, i1175, i931, RationalInterval.mul]) (by norm_num [i1190, i1175, i931, RationalInterval.mul])

def n1191 (b : ℝ) : ℝ := (n1176 b) * (n934 b)
def i1191 : RationalInterval := ⟨(-2495733207694208777291179724219 / 1000000000000000000000000000000 : ℚ), (-1247866590547872912427421121953 / 500000000000000000000000000000 : ℚ)⟩
theorem b1191 (b : ℝ) (hb : rootInterval.Contains b) : i1191.Contains (n1191 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1176 b hb) (b934 b hb))
    (by norm_num [i1191, i1176, i934, RationalInterval.mul]) (by norm_num [i1191, i1176, i934, RationalInterval.mul])

def n1192 (b : ℝ) : ℝ := (n1190 b) + (n1191 b)
def i1192 : RationalInterval := ⟨(-1829514230837414330473902491291 / 500000000000000000000000000000 : ℚ), (-3659028418683448883737203738893 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1192 (b : ℝ) (hb : rootInterval.Contains b) : i1192.Contains (n1192 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1190 b hb) (b1191 b hb))
    (by norm_num [i1192, i1190, i1191, RationalInterval.add]) (by norm_num [i1192, i1190, i1191, RationalInterval.add])

def n1193 (b : ℝ) : ℝ := (n1192 b) * (n13 b)
def i1193 : RationalInterval := ⟨(-1829514230837414330473902491291 / 250000000000000000000000000000 : ℚ), (-3659028418683448883737203738893 / 500000000000000000000000000000 : ℚ)⟩
theorem b1193 (b : ℝ) (hb : rootInterval.Contains b) : i1193.Contains (n1193 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1192 b hb) (b13 b hb))
    (by norm_num [i1193, i1192, i13, RationalInterval.mul]) (by norm_num [i1193, i1192, i13, RationalInterval.mul])

def n1194 (b : ℝ) : ℝ := (n21 b) * (n320 b)
def i1194 : RationalInterval := ⟨(479501355487299818929352949593 / 500000000000000000000000000000 : ℚ), (479501355952868146092293975533 / 500000000000000000000000000000 : ℚ)⟩
theorem b1194 (b : ℝ) (hb : rootInterval.Contains b) : i1194.Contains (n1194 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b21 b hb) (b320 b hb))
    (by norm_num [i1194, i21, i320, RationalInterval.mul]) (by norm_num [i1194, i21, i320, RationalInterval.mul])

def n1195 (b : ℝ) : ℝ := (n320 b) * (n21 b)
def i1195 : RationalInterval := ⟨(479501355487299818929352949593 / 500000000000000000000000000000 : ℚ), (479501355952868146092293975533 / 500000000000000000000000000000 : ℚ)⟩
theorem b1195 (b : ℝ) (hb : rootInterval.Contains b) : i1195.Contains (n1195 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b320 b hb) (b21 b hb))
    (by norm_num [i1195, i320, i21, RationalInterval.mul]) (by norm_num [i1195, i320, i21, RationalInterval.mul])

def n1196 (b : ℝ) : ℝ := (n1194 b) + (n1195 b)
def i1196 : RationalInterval := ⟨(479501355487299818929352949593 / 250000000000000000000000000000 : ℚ), (479501355952868146092293975533 / 250000000000000000000000000000 : ℚ)⟩
theorem b1196 (b : ℝ) (hb : rootInterval.Contains b) : i1196.Contains (n1196 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1194 b hb) (b1195 b hb))
    (by norm_num [i1196, i1194, i1195, RationalInterval.add]) (by norm_num [i1196, i1194, i1195, RationalInterval.add])

def n1197 (b : ℝ) : ℝ := (n1193 b) + (n1196 b)
def i1197 : RationalInterval := ⟨(-675006437675057255772274770849 / 125000000000000000000000000000 : ℚ), (-2700025706777712591552615787827 / 500000000000000000000000000000 : ℚ)⟩
theorem b1197 (b : ℝ) (hb : rootInterval.Contains b) : i1197.Contains (n1197 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1193 b hb) (b1196 b hb))
    (by norm_num [i1197, i1193, i1196, RationalInterval.add]) (by norm_num [i1197, i1193, i1196, RationalInterval.add])

def n1198 (b : ℝ) : ℝ := (n16 b) * (n302 b)
def i1198 : RationalInterval := ⟨(35445259791 / 25000000000 : ℚ), (28356207833 / 20000000000 : ℚ)⟩
theorem b1198 (b : ℝ) (hb : rootInterval.Contains b) : i1198.Contains (n1198 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b16 b hb) (b302 b hb))
    (by norm_num [i1198, i16, i302, RationalInterval.mul]) (by norm_num [i1198, i16, i302, RationalInterval.mul])

def n1199 (b : ℝ) : ℝ := (n16 b) * (n303 b)
def i1199 : RationalInterval := ⟨(22945259791 / 25000000000 : ℚ), (18356207833 / 20000000000 : ℚ)⟩
theorem b1199 (b : ℝ) (hb : rootInterval.Contains b) : i1199.Contains (n1199 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b16 b hb) (b303 b hb))
    (by norm_num [i1199, i16, i303, RationalInterval.mul]) (by norm_num [i1199, i16, i303, RationalInterval.mul])

def n1200 (b : ℝ) : ℝ := (n302 b) * (n16 b)
def i1200 : RationalInterval := ⟨(35445259791 / 25000000000 : ℚ), (28356207833 / 20000000000 : ℚ)⟩
theorem b1200 (b : ℝ) (hb : rootInterval.Contains b) : i1200.Contains (n1200 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b302 b hb) (b16 b hb))
    (by norm_num [i1200, i302, i16, RationalInterval.mul]) (by norm_num [i1200, i302, i16, RationalInterval.mul])

def n1201 (b : ℝ) : ℝ := (n303 b) * (n16 b)
def i1201 : RationalInterval := ⟨(22945259791 / 25000000000 : ℚ), (18356207833 / 20000000000 : ℚ)⟩
theorem b1201 (b : ℝ) (hb : rootInterval.Contains b) : i1201.Contains (n1201 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b303 b hb) (b16 b hb))
    (by norm_num [i1201, i303, i16, RationalInterval.mul]) (by norm_num [i1201, i303, i16, RationalInterval.mul])

def n1202 (b : ℝ) : ℝ := (n1198 b) + (n1200 b)
def i1202 : RationalInterval := ⟨(35445259791 / 12500000000 : ℚ), (28356207833 / 10000000000 : ℚ)⟩
theorem b1202 (b : ℝ) (hb : rootInterval.Contains b) : i1202.Contains (n1202 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1198 b hb) (b1200 b hb))
    (by norm_num [i1202, i1198, i1200, RationalInterval.add]) (by norm_num [i1202, i1198, i1200, RationalInterval.add])

def n1203 (b : ℝ) : ℝ := (n1188 b) * (n302 b)
def i1203 : RationalInterval := ⟨(-189910165083573962720249185849 / 100000000000000000000000000000 : ℚ), (-379820322753468488707016768781 / 200000000000000000000000000000 : ℚ)⟩
theorem b1203 (b : ℝ) (hb : rootInterval.Contains b) : i1203.Contains (n1203 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1188 b hb) (b302 b hb))
    (by norm_num [i1203, i1188, i302, RationalInterval.mul]) (by norm_num [i1203, i1188, i302, RationalInterval.mul])

def n1204 (b : ℝ) : ℝ := (n1188 b) * (n303 b)
def i1204 : RationalInterval := ⟨(-614685588496868504053097672363 / 500000000000000000000000000000 : ℚ), (-307342788248256505764915295027 / 250000000000000000000000000000 : ℚ)⟩
theorem b1204 (b : ℝ) (hb : rootInterval.Contains b) : i1204.Contains (n1204 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1188 b hb) (b303 b hb))
    (by norm_num [i1204, i1188, i303, RationalInterval.mul]) (by norm_num [i1204, i1188, i303, RationalInterval.mul])

def n1205 (b : ℝ) : ℝ := (n1189 b) * (n302 b)
def i1205 : RationalInterval := ⟨(-52902097507203366132675371833 / 100000000000000000000000000000 : ℚ), (-529020951923757710294063576223 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1205 (b : ℝ) (hb : rootInterval.Contains b) : i1205.Contains (n1205 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1189 b hb) (b302 b hb))
    (by norm_num [i1205, i1189, i302, RationalInterval.mul]) (by norm_num [i1205, i1189, i302, RationalInterval.mul])

def n1206 (b : ℝ) : ℝ := (n1189 b) * (n303 b)
def i1206 : RationalInterval := ⟨(-13698332335027447297643490617 / 40000000000000000000000000000 : ℚ), (-171229146694741768095912723247 / 500000000000000000000000000000 : ℚ)⟩
theorem b1206 (b : ℝ) (hb : rootInterval.Contains b) : i1206.Contains (n1206 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1189 b hb) (b303 b hb))
    (by norm_num [i1206, i1189, i303, RationalInterval.mul]) (by norm_num [i1206, i1189, i303, RationalInterval.mul])

def n1207 (b : ℝ) : ℝ := (n931 b) * (n16 b)
def i1207 : RationalInterval := ⟨(1913216368807889327599240919807 / 500000000000000000000000000000 : ℚ), (3826432739339273095464809485847 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1207 (b : ℝ) (hb : rootInterval.Contains b) : i1207.Contains (n1207 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b931 b hb) (b16 b hb))
    (by norm_num [i1207, i931, i16, RationalInterval.mul]) (by norm_num [i1207, i931, i16, RationalInterval.mul])

def n1208 (b : ℝ) : ℝ := (n934 b) * (n16 b)
def i1208 : RationalInterval := ⟨(1161603776658876432067867077499 / 500000000000000000000000000000 : ℚ), (580801888596264908966390712407 / 250000000000000000000000000000 : ℚ)⟩
theorem b1208 (b : ℝ) (hb : rootInterval.Contains b) : i1208.Contains (n1208 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b934 b hb) (b16 b hb))
    (by norm_num [i1208, i934, i16, RationalInterval.mul]) (by norm_num [i1208, i934, i16, RationalInterval.mul])

def n1209 (b : ℝ) : ℝ := (n1203 b) + (n1207 b)
def i1209 : RationalInterval := ⟨(481832771695009756998997495281 / 250000000000000000000000000000 : ℚ), (963665562785965325964862820971 / 500000000000000000000000000000 : ℚ)⟩
theorem b1209 (b : ℝ) (hb : rootInterval.Contains b) : i1209.Contains (n1209 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1203 b hb) (b1207 b hb))
    (by norm_num [i1209, i1203, i1207, RationalInterval.add]) (by norm_num [i1209, i1203, i1207, RationalInterval.add])

def n1210 (b : ℝ) : ℝ := (n1205 b) + (n1208 b)
def i1210 : RationalInterval := ⟨(448546644561429800702245109167 / 250000000000000000000000000000 : ℚ), (358837320492260385114299854681 / 200000000000000000000000000000 : ℚ)⟩
theorem b1210 (b : ℝ) (hb : rootInterval.Contains b) : i1210.Contains (n1210 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1205 b hb) (b1208 b hb))
    (by norm_num [i1210, i1205, i1208, RationalInterval.add]) (by norm_num [i1210, i1205, i1208, RationalInterval.add])

def n1211 (b : ℝ) : ℝ := (n16 b) * (n931 b)
def i1211 : RationalInterval := ⟨(1913216368807889327599240919807 / 500000000000000000000000000000 : ℚ), (3826432739339273095464809485847 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1211 (b : ℝ) (hb : rootInterval.Contains b) : i1211.Contains (n1211 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b16 b hb) (b931 b hb))
    (by norm_num [i1211, i16, i931, RationalInterval.mul]) (by norm_num [i1211, i16, i931, RationalInterval.mul])

def n1212 (b : ℝ) : ℝ := (n16 b) * (n934 b)
def i1212 : RationalInterval := ⟨(1161603776658876432067867077499 / 500000000000000000000000000000 : ℚ), (580801888596264908966390712407 / 250000000000000000000000000000 : ℚ)⟩
theorem b1212 (b : ℝ) (hb : rootInterval.Contains b) : i1212.Contains (n1212 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b16 b hb) (b934 b hb))
    (by norm_num [i1212, i16, i934, RationalInterval.mul]) (by norm_num [i1212, i16, i934, RationalInterval.mul])

def n1213 (b : ℝ) : ℝ := (n302 b) * (n1188 b)
def i1213 : RationalInterval := ⟨(-189910165083573962720249185849 / 100000000000000000000000000000 : ℚ), (-379820322753468488707016768781 / 200000000000000000000000000000 : ℚ)⟩
theorem b1213 (b : ℝ) (hb : rootInterval.Contains b) : i1213.Contains (n1213 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b302 b hb) (b1188 b hb))
    (by norm_num [i1213, i302, i1188, RationalInterval.mul]) (by norm_num [i1213, i302, i1188, RationalInterval.mul])

def n1214 (b : ℝ) : ℝ := (n302 b) * (n1189 b)
def i1214 : RationalInterval := ⟨(-52902097507203366132675371833 / 100000000000000000000000000000 : ℚ), (-529020951923757710294063576223 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1214 (b : ℝ) (hb : rootInterval.Contains b) : i1214.Contains (n1214 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b302 b hb) (b1189 b hb))
    (by norm_num [i1214, i302, i1189, RationalInterval.mul]) (by norm_num [i1214, i302, i1189, RationalInterval.mul])

def n1215 (b : ℝ) : ℝ := (n303 b) * (n1188 b)
def i1215 : RationalInterval := ⟨(-614685588496868504053097672363 / 500000000000000000000000000000 : ℚ), (-307342788248256505764915295027 / 250000000000000000000000000000 : ℚ)⟩
theorem b1215 (b : ℝ) (hb : rootInterval.Contains b) : i1215.Contains (n1215 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b303 b hb) (b1188 b hb))
    (by norm_num [i1215, i303, i1188, RationalInterval.mul]) (by norm_num [i1215, i303, i1188, RationalInterval.mul])

def n1216 (b : ℝ) : ℝ := (n303 b) * (n1189 b)
def i1216 : RationalInterval := ⟨(-13698332335027447297643490617 / 40000000000000000000000000000 : ℚ), (-171229146694741768095912723247 / 500000000000000000000000000000 : ℚ)⟩
theorem b1216 (b : ℝ) (hb : rootInterval.Contains b) : i1216.Contains (n1216 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b303 b hb) (b1189 b hb))
    (by norm_num [i1216, i303, i1189, RationalInterval.mul]) (by norm_num [i1216, i303, i1189, RationalInterval.mul])

def n1217 (b : ℝ) : ℝ := (n1211 b) + (n1213 b)
def i1217 : RationalInterval := ⟨(481832771695009756998997495281 / 250000000000000000000000000000 : ℚ), (963665562785965325964862820971 / 500000000000000000000000000000 : ℚ)⟩
theorem b1217 (b : ℝ) (hb : rootInterval.Contains b) : i1217.Contains (n1217 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1211 b hb) (b1213 b hb))
    (by norm_num [i1217, i1211, i1213, RationalInterval.add]) (by norm_num [i1217, i1211, i1213, RationalInterval.add])

def n1218 (b : ℝ) : ℝ := (n1212 b) + (n1214 b)
def i1218 : RationalInterval := ⟨(448546644561429800702245109167 / 250000000000000000000000000000 : ℚ), (358837320492260385114299854681 / 200000000000000000000000000000 : ℚ)⟩
theorem b1218 (b : ℝ) (hb : rootInterval.Contains b) : i1218.Contains (n1218 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1212 b hb) (b1214 b hb))
    (by norm_num [i1218, i1212, i1214, RationalInterval.add]) (by norm_num [i1218, i1212, i1214, RationalInterval.add])

def n1219 (b : ℝ) : ℝ := (n1209 b) + (n1217 b)
def i1219 : RationalInterval := ⟨(481832771695009756998997495281 / 125000000000000000000000000000 : ℚ), (963665562785965325964862820971 / 250000000000000000000000000000 : ℚ)⟩
theorem b1219 (b : ℝ) (hb : rootInterval.Contains b) : i1219.Contains (n1219 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1209 b hb) (b1217 b hb))
    (by norm_num [i1219, i1209, i1217, RationalInterval.add]) (by norm_num [i1219, i1209, i1217, RationalInterval.add])

def n1220 (b : ℝ) : ℝ := (n1204 b) + (n1218 b)
def i1220 : RationalInterval := ⟨(282407700625991097351392545971 / 500000000000000000000000000000 : ℚ), (564815449468275902511838093297 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1220 (b : ℝ) (hb : rootInterval.Contains b) : i1220.Contains (n1220 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1204 b hb) (b1218 b hb))
    (by norm_num [i1220, i1204, i1218, RationalInterval.add]) (by norm_num [i1220, i1204, i1218, RationalInterval.add])

def n1221 (b : ℝ) : ℝ := (n1210 b) + (n1215 b)
def i1221 : RationalInterval := ⟨(282407700625991097351392545971 / 500000000000000000000000000000 : ℚ), (564815449468275902511838093297 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1221 (b : ℝ) (hb : rootInterval.Contains b) : i1221.Contains (n1221 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1210 b hb) (b1215 b hb))
    (by norm_num [i1221, i1210, i1215, RationalInterval.add]) (by norm_num [i1221, i1210, i1215, RationalInterval.add])

def n1222 (b : ℝ) : ℝ := (n1206 b) + (n1216 b)
def i1222 : RationalInterval := ⟨(-13698332335027447297643490617 / 20000000000000000000000000000 : ℚ), (-171229146694741768095912723247 / 250000000000000000000000000000 : ℚ)⟩
theorem b1222 (b : ℝ) (hb : rootInterval.Contains b) : i1222.Contains (n1222 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1206 b hb) (b1216 b hb))
    (by norm_num [i1222, i1206, i1216, RationalInterval.add]) (by norm_num [i1222, i1206, i1216, RationalInterval.add])

def n1223 (b : ℝ) : ℝ := (n1005 b) * (n1219 b)
def i1223 : RationalInterval := ⟨(-414799599549236471153009095831 / 250000000000000000000000000000 : ℚ), (-829599182019788606908550619033 / 500000000000000000000000000000 : ℚ)⟩
theorem b1223 (b : ℝ) (hb : rootInterval.Contains b) : i1223.Contains (n1223 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1005 b hb) (b1219 b hb))
    (by norm_num [i1223, i1005, i1219, RationalInterval.mul]) (by norm_num [i1223, i1005, i1219, RationalInterval.mul])

def n1224 (b : ℝ) : ℝ := (n1005 b) * (n1220 b)
def i1224 : RationalInterval := ⟨(-30389850912247798484130991581 / 125000000000000000000000000000 : ℚ), (-30389848304012474993827176639 / 125000000000000000000000000000 : ℚ)⟩
theorem b1224 (b : ℝ) (hb : rootInterval.Contains b) : i1224.Contains (n1224 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1005 b hb) (b1220 b hb))
    (by norm_num [i1224, i1005, i1220, RationalInterval.mul]) (by norm_num [i1224, i1005, i1220, RationalInterval.mul])

def n1225 (b : ℝ) : ℝ := (n1005 b) * (n1221 b)
def i1225 : RationalInterval := ⟨(-30389850912247798484130991581 / 125000000000000000000000000000 : ℚ), (-30389848304012474993827176639 / 125000000000000000000000000000 : ℚ)⟩
theorem b1225 (b : ℝ) (hb : rootInterval.Contains b) : i1225.Contains (n1225 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1005 b hb) (b1221 b hb))
    (by norm_num [i1225, i1005, i1221, RationalInterval.mul]) (by norm_num [i1225, i1005, i1221, RationalInterval.mul])

def n1226 (b : ℝ) : ℝ := (n1005 b) * (n1222 b)
def i1226 : RationalInterval := ⟨(294815065268785576057734432697 / 1000000000000000000000000000000 : ℚ), (294815078305530125555765008691 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1226 (b : ℝ) (hb : rootInterval.Contains b) : i1226.Contains (n1226 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1005 b hb) (b1222 b hb))
    (by norm_num [i1226, i1005, i1222, RationalInterval.mul]) (by norm_num [i1226, i1005, i1222, RationalInterval.mul])

def n1227 (b : ℝ) : ℝ := (n1224 b) + (n15 b)
def i1227 : RationalInterval := ⟨(94610149087752201515869008419 / 125000000000000000000000000000 : ℚ), (94610151695987525006172823361 / 125000000000000000000000000000 : ℚ)⟩
theorem b1227 (b : ℝ) (hb : rootInterval.Contains b) : i1227.Contains (n1227 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1224 b hb) (b15 b hb))
    (by norm_num [i1227, i1224, i15, RationalInterval.add]) (by norm_num [i1227, i1224, i15, RationalInterval.add])

def n1228 (b : ℝ) : ℝ := (n1225 b) + (n15 b)
def i1228 : RationalInterval := ⟨(94610149087752201515869008419 / 125000000000000000000000000000 : ℚ), (94610151695987525006172823361 / 125000000000000000000000000000 : ℚ)⟩
theorem b1228 (b : ℝ) (hb : rootInterval.Contains b) : i1228.Contains (n1228 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1225 b hb) (b15 b hb))
    (by norm_num [i1228, i1225, i15, RationalInterval.add]) (by norm_num [i1228, i1225, i15, RationalInterval.add])

def n1229 (b : ℝ) : ℝ := (n1181 b) * (n1011 b)
def i1229 : RationalInterval := ⟨(-6913193524581647948737711783 / 100000000000000000000000000000 : ℚ), (-69131932157790460641812467013 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1229 (b : ℝ) (hb : rootInterval.Contains b) : i1229.Contains (n1229 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1181 b hb) (b1011 b hb))
    (by norm_num [i1229, i1181, i1011, RationalInterval.mul]) (by norm_num [i1229, i1181, i1011, RationalInterval.mul])

def n1230 (b : ℝ) : ℝ := (n1229 b) * (n946 b)
def i1230 : RationalInterval := ⟨(-750103080515829290586364590137 / 1000000000000000000000000000000 : ℚ), (-75010304666663236083493398071 / 100000000000000000000000000000 : ℚ)⟩
theorem b1230 (b : ℝ) (hb : rootInterval.Contains b) : i1230.Contains (n1230 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1229 b hb) (b946 b hb))
    (by norm_num [i1230, i1229, i946, RationalInterval.mul]) (by norm_num [i1230, i1229, i946, RationalInterval.mul])

def n1231 (b : ℝ) : ℝ := (n1229 b) * (n947 b)
def i1231 : RationalInterval := ⟨(-470498646405332739023515074173 / 1000000000000000000000000000000 : ℚ), (-235249312585300878582777919101 / 500000000000000000000000000000 : ℚ)⟩
theorem b1231 (b : ℝ) (hb : rootInterval.Contains b) : i1231.Contains (n1231 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1229 b hb) (b947 b hb))
    (by norm_num [i1231, i1229, i947, RationalInterval.mul]) (by norm_num [i1231, i1229, i947, RationalInterval.mul])

def n1232 (b : ℝ) : ℝ := (n1229 b) * (n948 b)
def i1232 : RationalInterval := ⟨(-470498646405332739023515074173 / 1000000000000000000000000000000 : ℚ), (-235249312585300878582777919101 / 500000000000000000000000000000 : ℚ)⟩
theorem b1232 (b : ℝ) (hb : rootInterval.Contains b) : i1232.Contains (n1232 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1229 b hb) (b948 b hb))
    (by norm_num [i1232, i1229, i948, RationalInterval.mul]) (by norm_num [i1232, i1229, i948, RationalInterval.mul])

def n1233 (b : ℝ) : ℝ := (n1229 b) * (n949 b)
def i1233 : RationalInterval := ⟨(-147407539220485686584005944829 / 500000000000000000000000000000 : ℚ), (-294815065133344334496932707033 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1233 (b : ℝ) (hb : rootInterval.Contains b) : i1233.Contains (n1233 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1229 b hb) (b949 b hb))
    (by norm_num [i1233, i1229, i949, RationalInterval.mul]) (by norm_num [i1233, i1229, i949, RationalInterval.mul])

def n1234 (b : ℝ) : ℝ := (n1223 b) + (n1230 b)
def i1234 : RationalInterval := ⟨(-2409301478712775175198400973461 / 1000000000000000000000000000000 : ℚ), (-301162676338276196831504402347 / 125000000000000000000000000000 : ℚ)⟩
theorem b1234 (b : ℝ) (hb : rootInterval.Contains b) : i1234.Contains (n1234 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1223 b hb) (b1230 b hb))
    (by norm_num [i1234, i1223, i1230, RationalInterval.add]) (by norm_num [i1234, i1223, i1230, RationalInterval.add])

def n1235 (b : ℝ) : ℝ := (n1227 b) + (n1231 b)
def i1235 : RationalInterval := ⟨(286382546296684873103436993179 / 1000000000000000000000000000000 : ℚ), (143191294198649221441913374343 / 500000000000000000000000000000 : ℚ)⟩
theorem b1235 (b : ℝ) (hb : rootInterval.Contains b) : i1235.Contains (n1235 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1227 b hb) (b1231 b hb))
    (by norm_num [i1235, i1227, i1231, RationalInterval.add]) (by norm_num [i1235, i1227, i1231, RationalInterval.add])

def n1236 (b : ℝ) : ℝ := (n1228 b) + (n1232 b)
def i1236 : RationalInterval := ⟨(286382546296684873103436993179 / 1000000000000000000000000000000 : ℚ), (143191294198649221441913374343 / 500000000000000000000000000000 : ℚ)⟩
theorem b1236 (b : ℝ) (hb : rootInterval.Contains b) : i1236.Contains (n1236 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1228 b hb) (b1232 b hb))
    (by norm_num [i1236, i1228, i1232, RationalInterval.add]) (by norm_num [i1236, i1228, i1232, RationalInterval.add])

def n1237 (b : ℝ) : ℝ := (n1226 b) + (n1233 b)
def i1237 : RationalInterval := ⟨(-13172185797110277456961 / 1000000000000000000000000000000 : ℚ), (6586092895529416150829 / 500000000000000000000000000000 : ℚ)⟩
theorem b1237 (b : ℝ) (hb : rootInterval.Contains b) : i1237.Contains (n1237 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1226 b hb) (b1233 b hb))
    (by norm_num [i1237, i1226, i1233, RationalInterval.add]) (by norm_num [i1237, i1226, i1233, RationalInterval.add])

def n1238 (b : ℝ) : ℝ := (n1181 b) + (n1197 b)
def i1238 : RationalInterval := ⟨(-2886588417396576501974765536301 / 500000000000000000000000000000 : ℚ), (-721647091327996691413713479389 / 125000000000000000000000000000 : ℚ)⟩
theorem b1238 (b : ℝ) (hb : rootInterval.Contains b) : i1238.Contains (n1238 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1181 b hb) (b1197 b hb))
    (by norm_num [i1238, i1181, i1197, RationalInterval.add]) (by norm_num [i1238, i1181, i1197, RationalInterval.add])

def n1239 (b : ℝ) : ℝ := (n1238 b) * (n1011 b)
def i1239 : RationalInterval := ⟨(-106964296279911018208518580893 / 100000000000000000000000000000 : ℚ), (-33426341953626133749288247269 / 31250000000000000000000000000 : ℚ)⟩
theorem b1239 (b : ℝ) (hb : rootInterval.Contains b) : i1239.Contains (n1239 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1238 b hb) (b1011 b hb))
    (by norm_num [i1239, i1238, i1011, RationalInterval.mul]) (by norm_num [i1239, i1238, i1011, RationalInterval.mul])

def n1240 (b : ℝ) : ℝ := (n1024 b) * (n1181 b)
def i1240 : RationalInterval := ⟨(-6307200724981011528493543549079 / 1000000000000000000000000000000 : ℚ), (-1576800111031521407051856241007 / 250000000000000000000000000000 : ℚ)⟩
theorem b1240 (b : ℝ) (hb : rootInterval.Contains b) : i1240.Contains (n1240 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1024 b hb) (b1181 b hb))
    (by norm_num [i1240, i1024, i1181, RationalInterval.mul]) (by norm_num [i1240, i1024, i1181, RationalInterval.mul])

def n1241 (b : ℝ) : ℝ := (n1240 b) * (n1027 b)
def i1241 : RationalInterval := ⟨(-503005367595317930476168556879 / 1000000000000000000000000000000 : ℚ), (-31437834031475448590472205329 / 62500000000000000000000000000 : ℚ)⟩
theorem b1241 (b : ℝ) (hb : rootInterval.Contains b) : i1241.Contains (n1241 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1240 b hb) (b1027 b hb))
    (by norm_num [i1241, i1240, i1027, RationalInterval.mul]) (by norm_num [i1241, i1240, i1027, RationalInterval.mul])

def n1242 (b : ℝ) : ℝ := -(n1241 b)
def i1242 : RationalInterval := ⟨(31437834031475448590472205329 / 62500000000000000000000000000 : ℚ), (503005367595317930476168556879 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1242 (b : ℝ) (hb : rootInterval.Contains b) : i1242.Contains (n1242 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b1241 b hb))
    (by norm_num [i1242, i1241, RationalInterval.neg]) (by norm_num [i1242, i1241, RationalInterval.neg])

def n1243 (b : ℝ) : ℝ := (n1239 b) + (n1242 b)
def i1243 : RationalInterval := ⟨(-283318809147751502318815261833 / 500000000000000000000000000000 : ℚ), (-566637574920718349501055355729 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1243 (b : ℝ) (hb : rootInterval.Contains b) : i1243.Contains (n1243 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1239 b hb) (b1242 b hb))
    (by norm_num [i1243, i1239, i1242, RationalInterval.add]) (by norm_num [i1243, i1239, i1242, RationalInterval.add])

def n1244 (b : ℝ) : ℝ := (n1243 b) * (n950 b)
def i1244 : RationalInterval := ⟨(-1139047181142134005304718115419 / 1000000000000000000000000000000 : ℚ), (-569523546967334071958623551051 / 500000000000000000000000000000 : ℚ)⟩
theorem b1244 (b : ℝ) (hb : rootInterval.Contains b) : i1244.Contains (n1244 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1243 b hb) (b950 b hb))
    (by norm_num [i1244, i1243, i950, RationalInterval.mul]) (by norm_num [i1244, i1243, i950, RationalInterval.mul])

def n1245 (b : ℝ) : ℝ := (n1243 b) * (n951 b)
def i1245 : RationalInterval := ⟨(-184338707345637211271300691469 / 250000000000000000000000000000 : ℚ), (-737354772926526381389134255853 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1245 (b : ℝ) (hb : rootInterval.Contains b) : i1245.Contains (n1245 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1243 b hb) (b951 b hb))
    (by norm_num [i1245, i1243, i951, RationalInterval.mul]) (by norm_num [i1245, i1243, i951, RationalInterval.mul])

def n1246 (b : ℝ) : ℝ := (n1243 b) * (n952 b)
def i1246 : RationalInterval := ⟨(-184338707345637211271300691469 / 250000000000000000000000000000 : ℚ), (-737354772926526381389134255853 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1246 (b : ℝ) (hb : rootInterval.Contains b) : i1246.Contains (n1246 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1243 b hb) (b952 b hb))
    (by norm_num [i1246, i1243, i952, RationalInterval.mul]) (by norm_num [i1246, i1243, i952, RationalInterval.mul])

def n1247 (b : ℝ) : ℝ := (n1243 b) * (n953 b)
def i1247 : RationalInterval := ⟨(-477321882196839436025095047249 / 1000000000000000000000000000000 : ℚ), (-95464369129712841247257049707 / 200000000000000000000000000000 : ℚ)⟩
theorem b1247 (b : ℝ) (hb : rootInterval.Contains b) : i1247.Contains (n1247 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1243 b hb) (b953 b hb))
    (by norm_num [i1247, i1243, i953, RationalInterval.mul]) (by norm_num [i1247, i1243, i953, RationalInterval.mul])

def n1248 (b : ℝ) : ℝ := (n1234 b) + (n1244 b)
def i1248 : RationalInterval := ⟨(-44354358248186364756288988611 / 12500000000000000000000000000 : ℚ), (-1774174252320438859284641160439 / 500000000000000000000000000000 : ℚ)⟩
theorem b1248 (b : ℝ) (hb : rootInterval.Contains b) : i1248.Contains (n1248 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1234 b hb) (b1244 b hb))
    (by norm_num [i1248, i1234, i1244, RationalInterval.add]) (by norm_num [i1248, i1234, i1244, RationalInterval.add])

def n1249 (b : ℝ) : ℝ := (n1235 b) + (n1245 b)
def i1249 : RationalInterval := ⟨(-450972283085863971981765772697 / 1000000000000000000000000000000 : ℚ), (-450972184529227938505307507167 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1249 (b : ℝ) (hb : rootInterval.Contains b) : i1249.Contains (n1249 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1235 b hb) (b1245 b hb))
    (by norm_num [i1249, i1235, i1245, RationalInterval.add]) (by norm_num [i1249, i1235, i1245, RationalInterval.add])

def n1250 (b : ℝ) : ℝ := (n1236 b) + (n1246 b)
def i1250 : RationalInterval := ⟨(-450972283085863971981765772697 / 1000000000000000000000000000000 : ℚ), (-450972184529227938505307507167 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1250 (b : ℝ) (hb : rootInterval.Contains b) : i1250.Contains (n1250 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1236 b hb) (b1246 b hb))
    (by norm_num [i1250, i1236, i1246, RationalInterval.add]) (by norm_num [i1250, i1236, i1246, RationalInterval.add])

def n1251 (b : ℝ) : ℝ := (n1237 b) + (n1247 b)
def i1251 : RationalInterval := ⟨(-47732189536902523313537250421 / 100000000000000000000000000000 : ℚ), (-477321832476378415177452946877 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1251 (b : ℝ) (hb : rootInterval.Contains b) : i1251.Contains (n1251 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1237 b hb) (b1247 b hb))
    (by norm_num [i1251, i1237, i1247, RationalInterval.add]) (by norm_num [i1251, i1237, i1247, RationalInterval.add])

def n1252 (b : ℝ) : ℝ := (n1039 b) * (n1202 b)
def i1252 : RationalInterval := ⟨(1110104995564732287491691548861 / 250000000000000000000000000000 : ℚ), (2220209994915718735435894958393 / 500000000000000000000000000000 : ℚ)⟩
theorem b1252 (b : ℝ) (hb : rootInterval.Contains b) : i1252.Contains (n1252 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1039 b hb) (b1202 b hb))
    (by norm_num [i1252, i1039, i1202, RationalInterval.mul]) (by norm_num [i1252, i1039, i1202, RationalInterval.mul])

def n1253 (b : ℝ) : ℝ := (n1039 b) * (n1199 b)
def i1253 : RationalInterval := ⟨(1437238585283962778438452571061 / 1000000000000000000000000000000 : ℚ), (1437238587740492331657866562817 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1253 (b : ℝ) (hb : rootInterval.Contains b) : i1253.Contains (n1253 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1039 b hb) (b1199 b hb))
    (by norm_num [i1253, i1039, i1199, RationalInterval.mul]) (by norm_num [i1253, i1039, i1199, RationalInterval.mul])

def n1254 (b : ℝ) : ℝ := (n1039 b) * (n1201 b)
def i1254 : RationalInterval := ⟨(1437238585283962778438452571061 / 1000000000000000000000000000000 : ℚ), (1437238587740492331657866562817 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1254 (b : ℝ) (hb : rootInterval.Contains b) : i1254.Contains (n1254 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1039 b hb) (b1201 b hb))
    (by norm_num [i1254, i1039, i1201, RationalInterval.mul]) (by norm_num [i1254, i1039, i1201, RationalInterval.mul])

def n1255 (b : ℝ) : ℝ := (n1248 b) + (n1252 b)
def i1255 : RationalInterval := ⟨(223017830601004992365911776641 / 250000000000000000000000000000 : ℚ), (223017871297639938075626898977 / 250000000000000000000000000000 : ℚ)⟩
theorem b1255 (b : ℝ) (hb : rootInterval.Contains b) : i1255.Contains (n1255 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1248 b hb) (b1252 b hb))
    (by norm_num [i1255, i1248, i1252, RationalInterval.add]) (by norm_num [i1255, i1248, i1252, RationalInterval.add])

def n1256 (b : ℝ) : ℝ := (n1249 b) + (n1253 b)
def i1256 : RationalInterval := ⟨(246566575549524701614171699591 / 250000000000000000000000000000 : ℚ), (19725328064225287863051181113 / 20000000000000000000000000000 : ℚ)⟩
theorem b1256 (b : ℝ) (hb : rootInterval.Contains b) : i1256.Contains (n1256 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1249 b hb) (b1253 b hb))
    (by norm_num [i1256, i1249, i1253, RationalInterval.add]) (by norm_num [i1256, i1249, i1253, RationalInterval.add])

def n1257 (b : ℝ) : ℝ := (n1250 b) + (n1254 b)
def i1257 : RationalInterval := ⟨(246566575549524701614171699591 / 250000000000000000000000000000 : ℚ), (19725328064225287863051181113 / 20000000000000000000000000000 : ℚ)⟩
theorem b1257 (b : ℝ) (hb : rootInterval.Contains b) : i1257.Contains (n1257 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1250 b hb) (b1254 b hb))
    (by norm_num [i1257, i1250, i1254, RationalInterval.add]) (by norm_num [i1257, i1250, i1254, RationalInterval.add])

def n1258 (b : ℝ) : ℝ := (n211 b) * (n16 b)
def i1258 : RationalInterval := ⟨(1074261822854187343377343754867 / 1000000000000000000000000000000 : ℚ), (134282729226210685066719959941 / 125000000000000000000000000000 : ℚ)⟩
theorem b1258 (b : ℝ) (hb : rootInterval.Contains b) : i1258.Contains (n1258 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b211 b hb) (b16 b hb))
    (by norm_num [i1258, i211, i16, RationalInterval.mul]) (by norm_num [i1258, i211, i16, RationalInterval.mul])

def n1259 (b : ℝ) : ℝ := (n213 b) * (n16 b)
def i1259 : RationalInterval := ⟨(3795984386934468359098160162079 / 1000000000000000000000000000000 : ℚ), (759196882515232061002779665111 / 200000000000000000000000000000 : ℚ)⟩
theorem b1259 (b : ℝ) (hb : rootInterval.Contains b) : i1259.Contains (n1259 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b213 b hb) (b16 b hb))
    (by norm_num [i1259, i213, i16, RationalInterval.mul]) (by norm_num [i1259, i213, i16, RationalInterval.mul])

