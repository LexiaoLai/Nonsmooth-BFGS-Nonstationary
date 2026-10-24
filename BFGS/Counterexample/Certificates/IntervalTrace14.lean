import BFGS.Counterexample.Certificates.IntervalTrace13

/-! Generated arithmetic proofs. Each bound is checked by the Lean kernel. -/
namespace BFGS.Counterexample.Trace
noncomputable section
open BFGS RationalInterval
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false

def n1260 (b : ℝ) : ℝ := (n16 b) * (n320 b)
def i1260 : RationalInterval := ⟨(183738145230645263163123798323 / 200000000000000000000000000000 : ℚ), (459345363357437601907605699171 / 500000000000000000000000000000 : ℚ)⟩
theorem b1260 (b : ℝ) (hb : rootInterval.Contains b) : i1260.Contains (n1260 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b16 b hb) (b320 b hb))
    (by norm_num [i1260, i16, i320, RationalInterval.mul]) (by norm_num [i1260, i16, i320, RationalInterval.mul])

def n1261 (b : ℝ) : ℝ := (n302 b) * (n1258 b)
def i1261 : RationalInterval := ⟨(-1523099591328357382718888262279 / 1000000000000000000000000000000 : ℚ), (-152309957578479565992776290939 / 100000000000000000000000000000 : ℚ)⟩
theorem b1261 (b : ℝ) (hb : rootInterval.Contains b) : i1261.Contains (n1261 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b302 b hb) (b1258 b hb))
    (by norm_num [i1261, i302, i1258, RationalInterval.mul]) (by norm_num [i1261, i302, i1258, RationalInterval.mul])

def n1262 (b : ℝ) : ℝ := (n303 b) * (n1259 b)
def i1262 : RationalInterval := ⟨(-3483993940403820874997989480871 / 1000000000000000000000000000000 : ℚ), (-3483993916831649703679070535561 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1262 (b : ℝ) (hb : rootInterval.Contains b) : i1262.Contains (n1262 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b303 b hb) (b1259 b hb))
    (by norm_num [i1262, i303, i1259, RationalInterval.mul]) (by norm_num [i1262, i303, i1259, RationalInterval.mul])

def n1263 (b : ℝ) : ℝ := (n1261 b) + (n1262 b)
def i1263 : RationalInterval := ⟨(-100141870634643565154337554863 / 20000000000000000000000000000 : ℚ), (-5007093492616445363606833444951 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1263 (b : ℝ) (hb : rootInterval.Contains b) : i1263.Contains (n1263 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1261 b hb) (b1262 b hb))
    (by norm_num [i1263, i1261, i1262, RationalInterval.add]) (by norm_num [i1263, i1261, i1262, RationalInterval.add])

def n1264 (b : ℝ) : ℝ := (n1260 b) + (n1263 b)
def i1264 : RationalInterval := ⟨(-817680561115790388380251750307 / 200000000000000000000000000000 : ℚ), (-4088402765901570159791622046609 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1264 (b : ℝ) (hb : rootInterval.Contains b) : i1264.Contains (n1264 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1260 b hb) (b1263 b hb))
    (by norm_num [i1264, i1260, i1263, RationalInterval.add]) (by norm_num [i1264, i1260, i1263, RationalInterval.add])

def n1265 (b : ℝ) : ℝ := (n63 b) * (n1258 b)
def i1265 : RationalInterval := ⟨(2597361398638983003305106664257 / 1000000000000000000000000000000 : ℚ), (2597361425138042863252647941807 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1265 (b : ℝ) (hb : rootInterval.Contains b) : i1265.Contains (n1265 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b63 b hb) (b1258 b hb))
    (by norm_num [i1265, i63, i1258, RationalInterval.mul]) (by norm_num [i1265, i63, i1258, RationalInterval.mul])

def n1266 (b : ℝ) : ℝ := (n65 b) * (n1259 b)
def i1266 : RationalInterval := ⟨(26909930551494419416140753083 / 5000000000000000000000000000 : ℚ), (5381986146691901027504938643649 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1266 (b : ℝ) (hb : rootInterval.Contains b) : i1266.Contains (n1266 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b65 b hb) (b1259 b hb))
    (by norm_num [i1266, i65, i1259, RationalInterval.mul]) (by norm_num [i1266, i65, i1259, RationalInterval.mul])

def n1267 (b : ℝ) : ℝ := (n1265 b) + (n1266 b)
def i1267 : RationalInterval := ⟨(7979347508937866886533257280857 / 1000000000000000000000000000000 : ℚ), (498709223239371493172349161591 / 62500000000000000000000000000 : ℚ)⟩
theorem b1267 (b : ℝ) (hb : rootInterval.Contains b) : i1267.Contains (n1267 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1265 b hb) (b1266 b hb))
    (by norm_num [i1267, i1265, i1266, RationalInterval.add]) (by norm_num [i1267, i1265, i1266, RationalInterval.add])

def n1268 (b : ℝ) : ℝ := (n65 b) * (n1258 b)
def i1268 : RationalInterval := ⟨(152309957578479565992776290939 / 100000000000000000000000000000 : ℚ), (1523099591328357382718888262279 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1268 (b : ℝ) (hb : rootInterval.Contains b) : i1268.Contains (n1268 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b65 b hb) (b1258 b hb))
    (by norm_num [i1268, i65, i1258, RationalInterval.mul]) (by norm_num [i1268, i65, i1258, RationalInterval.mul])

def n1269 (b : ℝ) : ℝ := (n0 b) * (n1259 b)
def i1269 : RationalInterval := ⟨(3483993916831649703679070535561 / 1000000000000000000000000000000 : ℚ), (3483993940403820874997989480871 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1269 (b : ℝ) (hb : rootInterval.Contains b) : i1269.Contains (n1269 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b0 b hb) (b1259 b hb))
    (by norm_num [i1269, i0, i1259, RationalInterval.mul]) (by norm_num [i1269, i0, i1259, RationalInterval.mul])

def n1270 (b : ℝ) : ℝ := (n1268 b) + (n1269 b)
def i1270 : RationalInterval := ⟨(5007093492616445363606833444951 / 1000000000000000000000000000000 : ℚ), (100141870634643565154337554863 / 20000000000000000000000000000 : ℚ)⟩
theorem b1270 (b : ℝ) (hb : rootInterval.Contains b) : i1270.Contains (n1270 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1268 b hb) (b1269 b hb))
    (by norm_num [i1270, i1268, i1269, RationalInterval.add]) (by norm_num [i1270, i1268, i1269, RationalInterval.add])

def n1271 (b : ℝ) : ℝ := (n320 b) + (n1270 b)
def i1271 : RationalInterval := ⟨(4088402765901570159791622046609 / 1000000000000000000000000000000 : ℚ), (817680561115790388380251750307 / 200000000000000000000000000000 : ℚ)⟩
theorem b1271 (b : ℝ) (hb : rootInterval.Contains b) : i1271.Contains (n1271 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b320 b hb) (b1270 b hb))
    (by norm_num [i1271, i320, i1270, RationalInterval.add]) (by norm_num [i1271, i320, i1270, RationalInterval.add])

def n1272 (b : ℝ) : ℝ := (n1258 b) * (n931 b)
def i1272 : RationalInterval := ⟨(-41105906515120257557036399571 / 10000000000000000000000000000 : ℚ), (-164423624309602589153533979759 / 40000000000000000000000000000 : ℚ)⟩
theorem b1272 (b : ℝ) (hb : rootInterval.Contains b) : i1272.Contains (n1272 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1258 b hb) (b931 b hb))
    (by norm_num [i1272, i1258, i931, RationalInterval.mul]) (by norm_num [i1272, i1258, i931, RationalInterval.mul])

def n1273 (b : ℝ) : ℝ := (n1259 b) * (n934 b)
def i1273 : RationalInterval := ⟨(-8818859663624868596581161446961 / 1000000000000000000000000000000 : ℚ), (-1102357450000302039882414773939 / 125000000000000000000000000000 : ℚ)⟩
theorem b1273 (b : ℝ) (hb : rootInterval.Contains b) : i1273.Contains (n1273 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1259 b hb) (b934 b hb))
    (by norm_num [i1273, i1259, i934, RationalInterval.mul]) (by norm_num [i1273, i1259, i934, RationalInterval.mul])

def n1274 (b : ℝ) : ℝ := (n1272 b) + (n1273 b)
def i1274 : RationalInterval := ⟨(-12929450315136894352284801404061 / 1000000000000000000000000000000 : ℚ), (-12929450207742481047897667685487 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1274 (b : ℝ) (hb : rootInterval.Contains b) : i1274.Contains (n1274 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1272 b hb) (b1273 b hb))
    (by norm_num [i1274, i1272, i1273, RationalInterval.add]) (by norm_num [i1274, i1272, i1273, RationalInterval.add])

def n1275 (b : ℝ) : ℝ := (n1274 b) * (n13 b)
def i1275 : RationalInterval := ⟨(-12929450315136894352284801404061 / 500000000000000000000000000000 : ℚ), (-12929450207742481047897667685487 / 500000000000000000000000000000 : ℚ)⟩
theorem b1275 (b : ℝ) (hb : rootInterval.Contains b) : i1275.Contains (n1275 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1274 b hb) (b13 b hb))
    (by norm_num [i1275, i1274, i13, RationalInterval.mul]) (by norm_num [i1275, i1274, i13, RationalInterval.mul])

def n1276 (b : ℝ) : ℝ := (n320 b) * (n320 b)
def i1276 : RationalInterval := ⟨(16879853006398845333227817819 / 20000000000000000000000000000 : ℚ), (843992651351905516495835615803 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1276 (b : ℝ) (hb : rootInterval.Contains b) : i1276.Contains (n1276 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b320 b hb) (b320 b hb))
    (by norm_num [i1276, i320, i320, RationalInterval.mul]) (by norm_num [i1276, i320, i320, RationalInterval.mul])

def n1277 (b : ℝ) : ℝ := (n1275 b) + (n1276 b)
def i1277 : RationalInterval := ⟨(-6253726994988461609477052979293 / 250000000000000000000000000000 : ℚ), (-25014907764133056579299499755171 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1277 (b : ℝ) (hb : rootInterval.Contains b) : i1277.Contains (n1277 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1275 b hb) (b1276 b hb))
    (by norm_num [i1277, i1275, i1276, RationalInterval.add]) (by norm_num [i1277, i1275, i1276, RationalInterval.add])

def n1278 (b : ℝ) : ℝ := (n1199 b) + (n1201 b)
def i1278 : RationalInterval := ⟨(22945259791 / 12500000000 : ℚ), (18356207833 / 10000000000 : ℚ)⟩
theorem b1278 (b : ℝ) (hb : rootInterval.Contains b) : i1278.Contains (n1278 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1199 b hb) (b1201 b hb))
    (by norm_num [i1278, i1199, i1201, RationalInterval.add]) (by norm_num [i1278, i1199, i1201, RationalInterval.add])

def n1279 (b : ℝ) : ℝ := (n1267 b) * (n302 b)
def i1279 : RationalInterval := ⟨(-2262640381185537850990507730387 / 200000000000000000000000000000 : ℚ), (-1414150227084856931352738118407 / 125000000000000000000000000000 : ℚ)⟩
theorem b1279 (b : ℝ) (hb : rootInterval.Contains b) : i1279.Contains (n1279 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1267 b hb) (b302 b hb))
    (by norm_num [i1279, i1267, i302, RationalInterval.mul]) (by norm_num [i1279, i1267, i302, RationalInterval.mul])

def n1280 (b : ℝ) : ℝ := (n1267 b) * (n303 b)
def i1280 : RationalInterval := ⟨(-7323528120012717309573745359207 / 1000000000000000000000000000000 : ℚ), (-1830882015552480501888819076707 / 250000000000000000000000000000 : ℚ)⟩
theorem b1280 (b : ℝ) (hb : rootInterval.Contains b) : i1280.Contains (n1280 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1267 b hb) (b303 b hb))
    (by norm_num [i1280, i1267, i303, RationalInterval.mul]) (by norm_num [i1280, i1267, i303, RationalInterval.mul])

def n1281 (b : ℝ) : ℝ := (n1271 b) * (n302 b)
def i1281 : RationalInterval := ⟨(-2898289991500426328871775858071 / 500000000000000000000000000000 : ℚ), (-5796579926704964425945097034693 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1281 (b : ℝ) (hb : rootInterval.Contains b) : i1281.Contains (n1281 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1271 b hb) (b302 b hb))
    (by norm_num [i1281, i1271, i302, RationalInterval.mul]) (by norm_num [i1281, i1271, i302, RationalInterval.mul])

def n1282 (b : ℝ) : ℝ := (n1271 b) * (n303 b)
def i1282 : RationalInterval := ⟨(-30019028641691013494343378723 / 8000000000000000000000000000 : ℚ), (-3752378543754179346049286011389 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1282 (b : ℝ) (hb : rootInterval.Contains b) : i1282.Contains (n1282 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1271 b hb) (b303 b hb))
    (by norm_num [i1282, i1271, i303, RationalInterval.mul]) (by norm_num [i1282, i1271, i303, RationalInterval.mul])

def n1283 (b : ℝ) : ℝ := (n1280 b) + (n1207 b)
def i1283 : RationalInterval := ⟨(-3497095382396938654375263519593 / 1000000000000000000000000000000 : ℚ), (-3497095322870648912090466820981 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1283 (b : ℝ) (hb : rootInterval.Contains b) : i1283.Contains (n1283 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1280 b hb) (b1207 b hb))
    (by norm_num [i1283, i1280, i1207, RationalInterval.add]) (by norm_num [i1283, i1280, i1207, RationalInterval.add])

def n1284 (b : ℝ) : ℝ := (n1282 b) + (n1208 b)
def i1284 : RationalInterval := ⟨(-1429171026893623822657188185377 / 1000000000000000000000000000000 : ℚ), (-1429170989369119710183723161761 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1284 (b : ℝ) (hb : rootInterval.Contains b) : i1284.Contains (n1284 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1282 b hb) (b1208 b hb))
    (by norm_num [i1284, i1282, i1208, RationalInterval.add]) (by norm_num [i1284, i1282, i1208, RationalInterval.add])

def n1285 (b : ℝ) : ℝ := (n302 b) * (n1267 b)
def i1285 : RationalInterval := ⟨(-2262640381185537850990507730387 / 200000000000000000000000000000 : ℚ), (-1414150227084856931352738118407 / 125000000000000000000000000000 : ℚ)⟩
theorem b1285 (b : ℝ) (hb : rootInterval.Contains b) : i1285.Contains (n1285 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b302 b hb) (b1267 b hb))
    (by norm_num [i1285, i302, i1267, RationalInterval.mul]) (by norm_num [i1285, i302, i1267, RationalInterval.mul])

def n1286 (b : ℝ) : ℝ := (n302 b) * (n1271 b)
def i1286 : RationalInterval := ⟨(-2898289991500426328871775858071 / 500000000000000000000000000000 : ℚ), (-5796579926704964425945097034693 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1286 (b : ℝ) (hb : rootInterval.Contains b) : i1286.Contains (n1286 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b302 b hb) (b1271 b hb))
    (by norm_num [i1286, i302, i1271, RationalInterval.mul]) (by norm_num [i1286, i302, i1271, RationalInterval.mul])

def n1287 (b : ℝ) : ℝ := (n303 b) * (n1267 b)
def i1287 : RationalInterval := ⟨(-7323528120012717309573745359207 / 1000000000000000000000000000000 : ℚ), (-1830882015552480501888819076707 / 250000000000000000000000000000 : ℚ)⟩
theorem b1287 (b : ℝ) (hb : rootInterval.Contains b) : i1287.Contains (n1287 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b303 b hb) (b1267 b hb))
    (by norm_num [i1287, i303, i1267, RationalInterval.mul]) (by norm_num [i1287, i303, i1267, RationalInterval.mul])

def n1288 (b : ℝ) : ℝ := (n303 b) * (n1271 b)
def i1288 : RationalInterval := ⟨(-30019028641691013494343378723 / 8000000000000000000000000000 : ℚ), (-3752378543754179346049286011389 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1288 (b : ℝ) (hb : rootInterval.Contains b) : i1288.Contains (n1288 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b303 b hb) (b1271 b hb))
    (by norm_num [i1288, i303, i1271, RationalInterval.mul]) (by norm_num [i1288, i303, i1271, RationalInterval.mul])

def n1289 (b : ℝ) : ℝ := (n1211 b) + (n1287 b)
def i1289 : RationalInterval := ⟨(-3497095382396938654375263519593 / 1000000000000000000000000000000 : ℚ), (-3497095322870648912090466820981 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1289 (b : ℝ) (hb : rootInterval.Contains b) : i1289.Contains (n1289 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1211 b hb) (b1287 b hb))
    (by norm_num [i1289, i1211, i1287, RationalInterval.add]) (by norm_num [i1289, i1211, i1287, RationalInterval.add])

def n1290 (b : ℝ) : ℝ := (n1212 b) + (n1288 b)
def i1290 : RationalInterval := ⟨(-1429171026893623822657188185377 / 1000000000000000000000000000000 : ℚ), (-1429170989369119710183723161761 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1290 (b : ℝ) (hb : rootInterval.Contains b) : i1290.Contains (n1290 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1212 b hb) (b1288 b hb))
    (by norm_num [i1290, i1212, i1288, RationalInterval.add]) (by norm_num [i1290, i1212, i1288, RationalInterval.add])

def n1291 (b : ℝ) : ℝ := (n1279 b) + (n1285 b)
def i1291 : RationalInterval := ⟨(-2262640381185537850990507730387 / 100000000000000000000000000000 : ℚ), (-1414150227084856931352738118407 / 62500000000000000000000000000 : ℚ)⟩
theorem b1291 (b : ℝ) (hb : rootInterval.Contains b) : i1291.Contains (n1291 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1279 b hb) (b1285 b hb))
    (by norm_num [i1291, i1279, i1285, RationalInterval.add]) (by norm_num [i1291, i1279, i1285, RationalInterval.add])

def n1292 (b : ℝ) : ℝ := (n1283 b) + (n1286 b)
def i1292 : RationalInterval := ⟨(-1858735073079558262423763047147 / 200000000000000000000000000000 : ℚ), (-4646837624787806669017781927837 / 500000000000000000000000000000 : ℚ)⟩
theorem b1292 (b : ℝ) (hb : rootInterval.Contains b) : i1292.Contains (n1292 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1283 b hb) (b1286 b hb))
    (by norm_num [i1292, i1283, i1286, RationalInterval.add]) (by norm_num [i1292, i1283, i1286, RationalInterval.add])

def n1293 (b : ℝ) : ℝ := (n1281 b) + (n1289 b)
def i1293 : RationalInterval := ⟨(-1858735073079558262423763047147 / 200000000000000000000000000000 : ℚ), (-4646837624787806669017781927837 / 500000000000000000000000000000 : ℚ)⟩
theorem b1293 (b : ℝ) (hb : rootInterval.Contains b) : i1293.Contains (n1293 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1281 b hb) (b1289 b hb))
    (by norm_num [i1293, i1281, i1289, RationalInterval.add]) (by norm_num [i1293, i1281, i1289, RationalInterval.add])

def n1294 (b : ℝ) : ℝ := (n1284 b) + (n1290 b)
def i1294 : RationalInterval := ⟨(-1429171026893623822657188185377 / 500000000000000000000000000000 : ℚ), (-1429170989369119710183723161761 / 500000000000000000000000000000 : ℚ)⟩
theorem b1294 (b : ℝ) (hb : rootInterval.Contains b) : i1294.Contains (n1294 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1284 b hb) (b1290 b hb))
    (by norm_num [i1294, i1284, i1290, RationalInterval.add]) (by norm_num [i1294, i1284, i1290, RationalInterval.add])

def n1295 (b : ℝ) : ℝ := (n1005 b) * (n1291 b)
def i1295 : RationalInterval := ⟨(9739294963401062326887254333707 / 1000000000000000000000000000000 : ℚ), (1947859008941564818921385727043 / 200000000000000000000000000000 : ℚ)⟩
theorem b1295 (b : ℝ) (hb : rootInterval.Contains b) : i1295.Contains (n1295 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1005 b hb) (b1291 b hb))
    (by norm_num [i1295, i1005, i1291, RationalInterval.mul]) (by norm_num [i1295, i1005, i1291, RationalInterval.mul])

def n1296 (b : ℝ) : ℝ := (n1005 b) * (n1292 b)
def i1296 : RationalInterval := ⟨(800072747011671840912427501739 / 200000000000000000000000000000 : ℚ), (4000363786750595271198286404823 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1296 (b : ℝ) (hb : rootInterval.Contains b) : i1296.Contains (n1296 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1005 b hb) (b1292 b hb))
    (by norm_num [i1296, i1005, i1292, RationalInterval.mul]) (by norm_num [i1296, i1005, i1292, RationalInterval.mul])

def n1297 (b : ℝ) : ℝ := (n1005 b) * (n1293 b)
def i1297 : RationalInterval := ⟨(800072747011671840912427501739 / 200000000000000000000000000000 : ℚ), (4000363786750595271198286404823 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1297 (b : ℝ) (hb : rootInterval.Contains b) : i1297.Contains (n1297 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1005 b hb) (b1293 b hb))
    (by norm_num [i1297, i1005, i1293, RationalInterval.mul]) (by norm_num [i1297, i1005, i1293, RationalInterval.mul])

def n1298 (b : ℝ) : ℝ := (n1005 b) * (n1294 b)
def i1298 : RationalInterval := ⟨(615171462692412548329935872949 / 500000000000000000000000000000 : ℚ), (615171479127052977186128794021 / 500000000000000000000000000000 : ℚ)⟩
theorem b1298 (b : ℝ) (hb : rootInterval.Contains b) : i1298.Contains (n1298 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1005 b hb) (b1294 b hb))
    (by norm_num [i1298, i1005, i1294, RationalInterval.mul]) (by norm_num [i1298, i1005, i1294, RationalInterval.mul])

def n1299 (b : ℝ) : ℝ := (n1298 b) + (n15 b)
def i1299 : RationalInterval := ⟨(1115171462692412548329935872949 / 500000000000000000000000000000 : ℚ), (1115171479127052977186128794021 / 500000000000000000000000000000 : ℚ)⟩
theorem b1299 (b : ℝ) (hb : rootInterval.Contains b) : i1299.Contains (n1299 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1298 b hb) (b15 b hb))
    (by norm_num [i1299, i1298, i15, RationalInterval.add]) (by norm_num [i1299, i1298, i15, RationalInterval.add])

def n1300 (b : ℝ) : ℝ := (n1264 b) * (n1011 b)
def i1300 : RationalInterval := ⟨(-757491311147816138675397421573 / 1000000000000000000000000000000 : ℚ), (-757491303100468642533894566463 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1300 (b : ℝ) (hb : rootInterval.Contains b) : i1300.Contains (n1300 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1264 b hb) (b1011 b hb))
    (by norm_num [i1300, i1264, i1011, RationalInterval.mul]) (by norm_num [i1300, i1264, i1011, RationalInterval.mul])

def n1301 (b : ℝ) : ℝ := (n1300 b) * (n946 b)
def i1301 : RationalInterval := ⟨(-8219017215930402493184672469819 / 1000000000000000000000000000000 : ℚ), (-1643803424970841232489394768381 / 200000000000000000000000000000 : ℚ)⟩
theorem b1301 (b : ℝ) (hb : rootInterval.Contains b) : i1301.Contains (n1301 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1300 b hb) (b946 b hb))
    (by norm_num [i1301, i1300, i946, RationalInterval.mul]) (by norm_num [i1301, i1300, i946, RationalInterval.mul])

def n1302 (b : ℝ) : ℝ := (n1300 b) * (n947 b)
def i1302 : RationalInterval := ⟨(-20138047186264018557967882569 / 3906250000000000000000000000 : ℚ), (-5155340022523811479696190791971 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1302 (b : ℝ) (hb : rootInterval.Contains b) : i1302.Contains (n1302 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1300 b hb) (b947 b hb))
    (by norm_num [i1302, i1300, i947, RationalInterval.mul]) (by norm_num [i1302, i1300, i947, RationalInterval.mul])

def n1303 (b : ℝ) : ℝ := (n1300 b) * (n948 b)
def i1303 : RationalInterval := ⟨(-20138047186264018557967882569 / 3906250000000000000000000000 : ℚ), (-5155340022523811479696190791971 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1303 (b : ℝ) (hb : rootInterval.Contains b) : i1303.Contains (n1303 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1300 b hb) (b948 b hb))
    (by norm_num [i1303, i1300, i948, RationalInterval.mul]) (by norm_num [i1303, i1300, i948, RationalInterval.mul])

def n1304 (b : ℝ) : ℝ := (n1300 b) * (n949 b)
def i1304 : RationalInterval := ⟨(-1615171479869080289690052114489 / 500000000000000000000000000000 : ℚ), (-3230342923900770487434320372993 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1304 (b : ℝ) (hb : rootInterval.Contains b) : i1304.Contains (n1304 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1300 b hb) (b949 b hb))
    (by norm_num [i1304, i1300, i949, RationalInterval.mul]) (by norm_num [i1304, i1300, i949, RationalInterval.mul])

def n1305 (b : ℝ) : ℝ := (n1295 b) + (n1301 b)
def i1305 : RationalInterval := ⟨(95017359216916239606411366493 / 62500000000000000000000000000 : ℚ), (152027791985361793215995479331 / 100000000000000000000000000000 : ℚ)⟩
theorem b1305 (b : ℝ) (hb : rootInterval.Contains b) : i1305.Contains (n1305 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1295 b hb) (b1301 b hb))
    (by norm_num [i1305, i1295, i1301, RationalInterval.add]) (by norm_num [i1305, i1295, i1301, RationalInterval.add])

def n1306 (b : ℝ) : ℝ := (n1296 b) + (n1302 b)
def i1306 : RationalInterval := ⟨(-1154976344625229546277640428969 / 1000000000000000000000000000000 : ℚ), (-288744058943304052124476096787 / 250000000000000000000000000000 : ℚ)⟩
theorem b1306 (b : ℝ) (hb : rootInterval.Contains b) : i1306.Contains (n1306 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1296 b hb) (b1302 b hb))
    (by norm_num [i1306, i1296, i1302, RationalInterval.add]) (by norm_num [i1306, i1296, i1302, RationalInterval.add])

def n1307 (b : ℝ) : ℝ := (n1297 b) + (n1303 b)
def i1307 : RationalInterval := ⟨(-1154976344625229546277640428969 / 1000000000000000000000000000000 : ℚ), (-288744058943304052124476096787 / 250000000000000000000000000000 : ℚ)⟩
theorem b1307 (b : ℝ) (hb : rootInterval.Contains b) : i1307.Contains (n1307 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1297 b hb) (b1303 b hb))
    (by norm_num [i1307, i1297, i1303, RationalInterval.add]) (by norm_num [i1307, i1297, i1303, RationalInterval.add])

def n1308 (b : ℝ) : ℝ := (n1299 b) + (n1304 b)
def i1308 : RationalInterval := ⟨(-25000000858833387068005812077 / 25000000000000000000000000000 : ℚ), (-999999965646664533062062784951 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1308 (b : ℝ) (hb : rootInterval.Contains b) : i1308.Contains (n1308 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1299 b hb) (b1304 b hb))
    (by norm_num [i1308, i1299, i1304, RationalInterval.add]) (by norm_num [i1308, i1299, i1304, RationalInterval.add])

def n1309 (b : ℝ) : ℝ := (n1264 b) + (n1277 b)
def i1309 : RationalInterval := ⟨(-29103310785532798379809470668707 / 1000000000000000000000000000000 : ℚ), (-1455165526501731336954556090089 / 50000000000000000000000000000 : ℚ)⟩
theorem b1309 (b : ℝ) (hb : rootInterval.Contains b) : i1309.Contains (n1309 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1264 b hb) (b1277 b hb))
    (by norm_num [i1309, i1264, i1277, RationalInterval.add]) (by norm_num [i1309, i1264, i1277, RationalInterval.add])

def n1310 (b : ℝ) : ℝ := (n1309 b) * (n1011 b)
def i1310 : RationalInterval := ⟨(-5392204754285161705730084806983 / 1000000000000000000000000000000 : ℚ), (-5392204701992483191930150893249 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1310 (b : ℝ) (hb : rootInterval.Contains b) : i1310.Contains (n1310 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1309 b hb) (b1011 b hb))
    (by norm_num [i1310, i1309, i1011, RationalInterval.mul]) (by norm_num [i1310, i1309, i1011, RationalInterval.mul])

def n1311 (b : ℝ) : ℝ := (n1024 b) * (n1264 b)
def i1311 : RationalInterval := ⟨(-6910915671390007130698281497729 / 100000000000000000000000000000 : ℚ), (-34554577994667917045098395214499 / 500000000000000000000000000000 : ℚ)⟩
theorem b1311 (b : ℝ) (hb : rootInterval.Contains b) : i1311.Contains (n1311 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1024 b hb) (b1264 b hb))
    (by norm_num [i1311, i1024, i1264, RationalInterval.mul]) (by norm_num [i1311, i1024, i1264, RationalInterval.mul])

def n1312 (b : ℝ) : ℝ := (n1311 b) * (n1027 b)
def i1312 : RationalInterval := ⟨(-220460887755763599250938511277 / 40000000000000000000000000000 : ℚ), (-5511522128513230871355176869307 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1312 (b : ℝ) (hb : rootInterval.Contains b) : i1312.Contains (n1312 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1311 b hb) (b1027 b hb))
    (by norm_num [i1312, i1311, i1027, RationalInterval.mul]) (by norm_num [i1312, i1311, i1027, RationalInterval.mul])

def n1313 (b : ℝ) : ℝ := -(n1312 b)
def i1313 : RationalInterval := ⟨(5511522128513230871355176869307 / 1000000000000000000000000000000 : ℚ), (220460887755763599250938511277 / 40000000000000000000000000000 : ℚ)⟩
theorem b1313 (b : ℝ) (hb : rootInterval.Contains b) : i1313.Contains (n1313 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b1312 b hb))
    (by norm_num [i1313, i1312, RationalInterval.neg]) (by norm_num [i1313, i1312, RationalInterval.neg])

def n1314 (b : ℝ) : ℝ := (n1310 b) + (n1313 b)
def i1314 : RationalInterval := ⟨(29829343557017291406273015581 / 250000000000000000000000000000 : ℚ), (29829372975401697335827972169 / 250000000000000000000000000000 : ℚ)⟩
theorem b1314 (b : ℝ) (hb : rootInterval.Contains b) : i1314.Contains (n1314 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1310 b hb) (b1313 b hb))
    (by norm_num [i1314, i1310, i1313, RationalInterval.add]) (by norm_num [i1314, i1310, i1313, RationalInterval.add])

def n1315 (b : ℝ) : ℝ := (n1314 b) * (n950 b)
def i1315 : RationalInterval := ⟨(239850151817787880945880254989 / 1000000000000000000000000000000 : ℚ), (239850388366905257908460644317 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1315 (b : ℝ) (hb : rootInterval.Contains b) : i1315.Contains (n1315 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1314 b hb) (b950 b hb))
    (by norm_num [i1315, i1314, i950, RationalInterval.mul]) (by norm_num [i1315, i1314, i950, RationalInterval.mul])

def n1316 (b : ℝ) : ℝ := (n1314 b) * (n951 b)
def i1316 : RationalInterval := ⟨(77632722637955143873960176921 / 500000000000000000000000000000 : ℚ), (155265598405048845276890606721 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1316 (b : ℝ) (hb : rootInterval.Contains b) : i1316.Contains (n1316 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1314 b hb) (b951 b hb))
    (by norm_num [i1316, i1314, i951, RationalInterval.mul]) (by norm_num [i1316, i1314, i951, RationalInterval.mul])

def n1317 (b : ℝ) : ℝ := (n1314 b) * (n952 b)
def i1317 : RationalInterval := ⟨(77632722637955143873960176921 / 500000000000000000000000000000 : ℚ), (155265598405048845276890606721 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1317 (b : ℝ) (hb : rootInterval.Contains b) : i1317.Contains (n1317 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1314 b hb) (b952 b hb))
    (by norm_num [i1317, i1314, i952, RationalInterval.mul]) (by norm_num [i1317, i1314, i952, RationalInterval.mul])

def n1318 (b : ℝ) : ℝ := (n1314 b) * (n953 b)
def i1318 : RationalInterval := ⟨(4020403291641999438249338731 / 40000000000000000000000000000 : ℚ), (50255090709297064990574270647 / 500000000000000000000000000000 : ℚ)⟩
theorem b1318 (b : ℝ) (hb : rootInterval.Contains b) : i1318.Contains (n1318 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1314 b hb) (b953 b hb))
    (by norm_num [i1318, i1314, i953, RationalInterval.mul]) (by norm_num [i1318, i1314, i953, RationalInterval.mul])

def n1319 (b : ℝ) : ℝ := (n1305 b) + (n1315 b)
def i1319 : RationalInterval := ⟨(1760127899288447714648462118877 / 1000000000000000000000000000000 : ℚ), (1760128308220523190068415437627 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1319 (b : ℝ) (hb : rootInterval.Contains b) : i1319.Contains (n1319 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1305 b hb) (b1315 b hb))
    (by norm_num [i1319, i1305, i1315, RationalInterval.add]) (by norm_num [i1319, i1305, i1315, RationalInterval.add])

def n1320 (b : ℝ) : ℝ := (n1306 b) + (n1316 b)
def i1320 : RationalInterval := ⟨(-999710899349319258529720075127 / 1000000000000000000000000000000 : ℚ), (-999710637368167363221013780427 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1320 (b : ℝ) (hb : rootInterval.Contains b) : i1320.Contains (n1320 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1306 b hb) (b1316 b hb))
    (by norm_num [i1320, i1306, i1316, RationalInterval.add]) (by norm_num [i1320, i1306, i1316, RationalInterval.add])

def n1321 (b : ℝ) : ℝ := (n1307 b) + (n1317 b)
def i1321 : RationalInterval := ⟨(-999710899349319258529720075127 / 1000000000000000000000000000000 : ℚ), (-999710637368167363221013780427 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1321 (b : ℝ) (hb : rootInterval.Contains b) : i1321.Contains (n1321 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1307 b hb) (b1317 b hb))
    (by norm_num [i1321, i1307, i1317, RationalInterval.add]) (by norm_num [i1321, i1307, i1317, RationalInterval.add])

def n1322 (b : ℝ) : ℝ := (n1308 b) + (n1318 b)
def i1322 : RationalInterval := ⟨(-179897990412457099352799802961 / 200000000000000000000000000000 : ℚ), (-899489784228070403080914243657 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1322 (b : ℝ) (hb : rootInterval.Contains b) : i1322.Contains (n1322 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1308 b hb) (b1318 b hb))
    (by norm_num [i1322, i1308, i1318, RationalInterval.add]) (by norm_num [i1322, i1308, i1318, RationalInterval.add])

def n1323 (b : ℝ) : ℝ := (n1039 b) * (n1200 b)
def i1323 : RationalInterval := ⟨(1110104995564732287491691548861 / 500000000000000000000000000000 : ℚ), (2220209994915718735435894958393 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1323 (b : ℝ) (hb : rootInterval.Contains b) : i1323.Contains (n1323 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1039 b hb) (b1200 b hb))
    (by norm_num [i1323, i1039, i1200, RationalInterval.mul]) (by norm_num [i1323, i1039, i1200, RationalInterval.mul])

def n1324 (b : ℝ) : ℝ := (n1039 b) * (n1198 b)
def i1324 : RationalInterval := ⟨(1110104995564732287491691548861 / 500000000000000000000000000000 : ℚ), (2220209994915718735435894958393 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1324 (b : ℝ) (hb : rootInterval.Contains b) : i1324.Contains (n1324 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1039 b hb) (b1198 b hb))
    (by norm_num [i1324, i1039, i1198, RationalInterval.mul]) (by norm_num [i1324, i1039, i1198, RationalInterval.mul])

def n1325 (b : ℝ) : ℝ := (n1039 b) * (n1278 b)
def i1325 : RationalInterval := ⟨(2874477170567925556876905142123 / 1000000000000000000000000000000 : ℚ), (1437238587740492331657866562817 / 500000000000000000000000000000 : ℚ)⟩
theorem b1325 (b : ℝ) (hb : rootInterval.Contains b) : i1325.Contains (n1325 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1039 b hb) (b1278 b hb))
    (by norm_num [i1325, i1039, i1278, RationalInterval.mul]) (by norm_num [i1325, i1039, i1278, RationalInterval.mul])

def n1326 (b : ℝ) : ℝ := (n1320 b) + (n1323 b)
def i1326 : RationalInterval := ⟨(244099818356029063290732604519 / 200000000000000000000000000000 : ℚ), (610249678773775686107440588983 / 500000000000000000000000000000 : ℚ)⟩
theorem b1326 (b : ℝ) (hb : rootInterval.Contains b) : i1326.Contains (n1326 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1320 b hb) (b1323 b hb))
    (by norm_num [i1326, i1320, i1323, RationalInterval.add]) (by norm_num [i1326, i1320, i1323, RationalInterval.add])

def n1327 (b : ℝ) : ℝ := (n1321 b) + (n1324 b)
def i1327 : RationalInterval := ⟨(244099818356029063290732604519 / 200000000000000000000000000000 : ℚ), (610249678773775686107440588983 / 500000000000000000000000000000 : ℚ)⟩
theorem b1327 (b : ℝ) (hb : rootInterval.Contains b) : i1327.Contains (n1327 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1321 b hb) (b1324 b hb))
    (by norm_num [i1327, i1321, i1324, RationalInterval.add]) (by norm_num [i1327, i1321, i1324, RationalInterval.add])

def n1328 (b : ℝ) : ℝ := (n1322 b) + (n1325 b)
def i1328 : RationalInterval := ⟨(987493609252820030056453063659 / 500000000000000000000000000000 : ℚ), (1974987391252914260234818881977 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1328 (b : ℝ) (hb : rootInterval.Contains b) : i1328.Contains (n1328 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1322 b hb) (b1325 b hb))
    (by norm_num [i1328, i1322, i1325, RationalInterval.add]) (by norm_num [i1328, i1322, i1325, RationalInterval.add])

def n1329 (b : ℝ) : ℝ := (n911 b) * (n583 b)
def i1329 : RationalInterval := ⟨(-66624655362355729109818487667 / 125000000000000000000000000000 : ℚ), (-133249309896804231435553051691 / 250000000000000000000000000000 : ℚ)⟩
theorem b1329 (b : ℝ) (hb : rootInterval.Contains b) : i1329.Contains (n1329 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b911 b hb) (b583 b hb))
    (by norm_num [i1329, i911, i583, RationalInterval.mul]) (by norm_num [i1329, i911, i583, RationalInterval.mul])

def n1330 (b : ℝ) : ℝ := (n1054 b) * (n582 b)
def i1330 : RationalInterval := ⟨(-109946348981882392778249357357 / 500000000000000000000000000000 : ℚ), (-109946348410132956074665856321 / 500000000000000000000000000000 : ℚ)⟩
theorem b1330 (b : ℝ) (hb : rootInterval.Contains b) : i1330.Contains (n1330 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1054 b hb) (b582 b hb))
    (by norm_num [i1330, i1054, i582, RationalInterval.mul]) (by norm_num [i1330, i1054, i582, RationalInterval.mul])

def n1331 (b : ℝ) : ℝ := (n1329 b) + (n1330 b)
def i1331 : RationalInterval := ⟨(-15057798817252212368700932321 / 20000000000000000000000000000 : ℚ), (-376444968203741418945771959703 / 500000000000000000000000000000 : ℚ)⟩
theorem b1331 (b : ℝ) (hb : rootInterval.Contains b) : i1331.Contains (n1331 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1329 b hb) (b1330 b hb))
    (by norm_num [i1331, i1329, i1330, RationalInterval.add]) (by norm_num [i1331, i1329, i1330, RationalInterval.add])

def n1332 (b : ℝ) : ℝ := (n16 b) * (n681 b)
def i1332 : RationalInterval := ⟨(13103242267176903310349301343 / 40000000000000000000000000000 : ℚ), (81895284010497685266305853829 / 250000000000000000000000000000 : ℚ)⟩
theorem b1332 (b : ℝ) (hb : rootInterval.Contains b) : i1332.Contains (n1332 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b16 b hb) (b681 b hb))
    (by norm_num [i1332, i16, i681, RationalInterval.mul]) (by norm_num [i1332, i16, i681, RationalInterval.mul])

def n1333 (b : ℝ) : ℝ := (n1331 b) + (n1332 b)
def i1333 : RationalInterval := ⟨(-17012355367327521427052563299 / 40000000000000000000000000000 : ℚ), (-42530880036549209682632050409 / 100000000000000000000000000000 : ℚ)⟩
theorem b1333 (b : ℝ) (hb : rootInterval.Contains b) : i1333.Contains (n1333 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1331 b hb) (b1332 b hb))
    (by norm_num [i1333, i1331, i1332, RationalInterval.add]) (by norm_num [i1333, i1331, i1332, RationalInterval.add])

def n1334 (b : ℝ) : ℝ := (n911 b) * (n689 b)
def i1334 : RationalInterval := ⟨(-1174683536947183906189116187317 / 1000000000000000000000000000000 : ℚ), (-1174683532397802842949782056987 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1334 (b : ℝ) (hb : rootInterval.Contains b) : i1334.Contains (n1334 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b911 b hb) (b689 b hb))
    (by norm_num [i1334, i911, i689, RationalInterval.mul]) (by norm_num [i1334, i911, i689, RationalInterval.mul])

def n1335 (b : ℝ) : ℝ := (n1054 b) * (n691 b)
def i1335 : RationalInterval := ⟨(965279776751514617838756844751 / 1000000000000000000000000000000 : ℚ), (193055956011209935878970470087 / 200000000000000000000000000000 : ℚ)⟩
theorem b1335 (b : ℝ) (hb : rootInterval.Contains b) : i1335.Contains (n1335 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1054 b hb) (b691 b hb))
    (by norm_num [i1335, i1054, i691, RationalInterval.mul]) (by norm_num [i1335, i1054, i691, RationalInterval.mul])

def n1336 (b : ℝ) : ℝ := (n1334 b) + (n1335 b)
def i1336 : RationalInterval := ⟨(-104701880097834644175179671283 / 500000000000000000000000000000 : ℚ), (-26175469042719145444366213319 / 125000000000000000000000000000 : ℚ)⟩
theorem b1336 (b : ℝ) (hb : rootInterval.Contains b) : i1336.Contains (n1336 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1334 b hb) (b1335 b hb))
    (by norm_num [i1336, i1334, i1335, RationalInterval.add]) (by norm_num [i1336, i1334, i1335, RationalInterval.add])

def n1337 (b : ℝ) : ℝ := (n16 b) * (n777 b)
def i1337 : RationalInterval := ⟨(-565878482390547262217394817741 / 250000000000000000000000000000 : ℚ), (-1131756915261541399616960287157 / 500000000000000000000000000000 : ℚ)⟩
theorem b1337 (b : ℝ) (hb : rootInterval.Contains b) : i1337.Contains (n1337 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b16 b hb) (b777 b hb))
    (by norm_num [i1337, i16, i777, RationalInterval.mul]) (by norm_num [i1337, i16, i777, RationalInterval.mul])

def n1338 (b : ℝ) : ℝ := (n1336 b) + (n1337 b)
def i1338 : RationalInterval := ⟨(-247291768975785833721993861353 / 100000000000000000000000000000 : ℚ), (-1236458791432417981394425140433 / 500000000000000000000000000000 : ℚ)⟩
theorem b1338 (b : ℝ) (hb : rootInterval.Contains b) : i1338.Contains (n1338 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1336 b hb) (b1337 b hb))
    (by norm_num [i1338, i1336, i1337, RationalInterval.add]) (by norm_num [i1338, i1336, i1337, RationalInterval.add])

def n1339 (b : ℝ) : ℝ := (n911 b) * (n16 b)
def i1339 : RationalInterval := ⟨(1036358356777564124559816663061 / 500000000000000000000000000000 : ℚ), (2072716717511546448183706778167 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1339 (b : ℝ) (hb : rootInterval.Contains b) : i1339.Contains (n1339 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b911 b hb) (b16 b hb))
    (by norm_num [i1339, i911, i16, RationalInterval.mul]) (by norm_num [i1339, i911, i16, RationalInterval.mul])

def n1340 (b : ℝ) : ℝ := (n16 b) * (n840 b)
def i1340 : RationalInterval := ⟨(4835834825360688285104890916483 / 1000000000000000000000000000000 : ℚ), (967166969561903851435037550871 / 200000000000000000000000000000 : ℚ)⟩
theorem b1340 (b : ℝ) (hb : rootInterval.Contains b) : i1340.Contains (n1340 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b16 b hb) (b840 b hb))
    (by norm_num [i1340, i16, i840, RationalInterval.mul]) (by norm_num [i1340, i16, i840, RationalInterval.mul])

def n1341 (b : ℝ) : ℝ := (n1339 b) + (n1340 b)
def i1341 : RationalInterval := ⟨(1381710307783163306844904848521 / 200000000000000000000000000000 : ℚ), (3454275782660532852679447266261 / 500000000000000000000000000000 : ℚ)⟩
theorem b1341 (b : ℝ) (hb : rootInterval.Contains b) : i1341.Contains (n1341 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1339 b hb) (b1340 b hb))
    (by norm_num [i1341, i1339, i1340, RationalInterval.add]) (by norm_num [i1341, i1339, i1340, RationalInterval.add])

def n1342 (b : ℝ) : ℝ := (n1054 b) * (n16 b)
def i1342 : RationalInterval := ⟨(-797519135277695694150744004381 / 1000000000000000000000000000000 : ℚ), (-797519132965040541766477297367 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1342 (b : ℝ) (hb : rootInterval.Contains b) : i1342.Contains (n1342 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1054 b hb) (b16 b hb))
    (by norm_num [i1342, i1054, i16, RationalInterval.mul]) (by norm_num [i1342, i1054, i16, RationalInterval.mul])

def n1343 (b : ℝ) : ℝ := (n16 b) * (n900 b)
def i1343 : RationalInterval := ⟨(-169343205391954967925280053603 / 62500000000000000000000000000 : ℚ), (-2709491272922078168723893472531 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1343 (b : ℝ) (hb : rootInterval.Contains b) : i1343.Contains (n1343 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b16 b hb) (b900 b hb))
    (by norm_num [i1343, i16, i900, RationalInterval.mul]) (by norm_num [i1343, i16, i900, RationalInterval.mul])

def n1344 (b : ℝ) : ℝ := (n1342 b) + (n1343 b)
def i1344 : RationalInterval := ⟨(-3507010421548975180955224862029 / 1000000000000000000000000000000 : ℚ), (-1753505202943559355245185384949 / 500000000000000000000000000000 : ℚ)⟩
theorem b1344 (b : ℝ) (hb : rootInterval.Contains b) : i1344.Contains (n1344 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1342 b hb) (b1343 b hb))
    (by norm_num [i1344, i1342, i1343, RationalInterval.add]) (by norm_num [i1344, i1342, i1343, RationalInterval.add])

def n1345 (b : ℝ) : ℝ := ((-4 : ℚ) : ℝ)
def i1345 : RationalInterval := ⟨(-4 : ℚ), (-4 : ℚ)⟩
theorem b1345 (b : ℝ) (hb : rootInterval.Contains b) : i1345.Contains (n1345 b) := by
  exact RationalInterval.contains_point (-4 : ℚ)

def n1346 (b : ℝ) : ℝ := (n910 b) * (n583 b)
def i1346 : RationalInterval := ⟨(-45469944948363954321515830053 / 100000000000000000000000000000 : ℚ), (-227349723455383487413750316519 / 500000000000000000000000000000 : ℚ)⟩
theorem b1346 (b : ℝ) (hb : rootInterval.Contains b) : i1346.Contains (n1346 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b910 b hb) (b583 b hb))
    (by norm_num [i1346, i910, i583, RationalInterval.mul]) (by norm_num [i1346, i910, i583, RationalInterval.mul])

def n1347 (b : ℝ) : ℝ := (n1056 b) * (n582 b)
def i1347 : RationalInterval := ⟨(-402260867588047199473596907909 / 1000000000000000000000000000000 : ℚ), (-100565216570147850719300496681 / 250000000000000000000000000000 : ℚ)⟩
theorem b1347 (b : ℝ) (hb : rootInterval.Contains b) : i1347.Contains (n1347 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1056 b hb) (b582 b hb))
    (by norm_num [i1347, i1056, i582, RationalInterval.mul]) (by norm_num [i1347, i1056, i582, RationalInterval.mul])

def n1348 (b : ℝ) : ℝ := (n1346 b) + (n1347 b)
def i1348 : RationalInterval := ⟨(-856960317071686742688755208439 / 1000000000000000000000000000000 : ℚ), (-428480156595679188852351309881 / 500000000000000000000000000000 : ℚ)⟩
theorem b1348 (b : ℝ) (hb : rootInterval.Contains b) : i1348.Contains (n1348 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1346 b hb) (b1347 b hb))
    (by norm_num [i1348, i1346, i1347, RationalInterval.add]) (by norm_num [i1348, i1346, i1347, RationalInterval.add])

def n1349 (b : ℝ) : ℝ := (n16 b) * (n683 b)
def i1349 : RationalInterval := ⟨(322728757402015922251796874003 / 1000000000000000000000000000000 : ℚ), (12909151843867058414400669159 / 40000000000000000000000000000 : ℚ)⟩
theorem b1349 (b : ℝ) (hb : rootInterval.Contains b) : i1349.Contains (n1349 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b16 b hb) (b683 b hb))
    (by norm_num [i1349, i16, i683, RationalInterval.mul]) (by norm_num [i1349, i16, i683, RationalInterval.mul])

