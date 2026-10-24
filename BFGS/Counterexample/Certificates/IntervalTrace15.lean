import BFGS.Counterexample.Certificates.IntervalTrace14

/-! Generated arithmetic proofs. Each bound is checked by the Lean kernel. -/
namespace BFGS.Counterexample.Trace
noncomputable section
open BFGS RationalInterval
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false

def n1350 (b : ℝ) : ℝ := (n1348 b) + (n1349 b)
def i1350 : RationalInterval := ⟨(-133557889917417705109239583609 / 250000000000000000000000000000 : ℚ), (-534231517094681917344685890787 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1350 (b : ℝ) (hb : rootInterval.Contains b) : i1350.Contains (n1350 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1348 b hb) (b1349 b hb))
    (by norm_num [i1350, i1348, i1349, RationalInterval.add]) (by norm_num [i1350, i1348, i1349, RationalInterval.add])

def n1351 (b : ℝ) : ℝ := (n910 b) * (n689 b)
def i1351 : RationalInterval := ⟨(-1002121426862142008802402984121 / 1000000000000000000000000000000 : ℚ), (-1002121423537063219080345917299 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1351 (b : ℝ) (hb : rootInterval.Contains b) : i1351.Contains (n1351 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b910 b hb) (b689 b hb))
    (by norm_num [i1351, i910, i689, RationalInterval.mul]) (by norm_num [i1351, i910, i689, RationalInterval.mul])

def n1352 (b : ℝ) : ℝ := (n1056 b) * (n691 b)
def i1352 : RationalInterval := ⟨(882917633950755842705398894367 / 500000000000000000000000000000 : ℚ), (88291763525165202097224769973 / 50000000000000000000000000000 : ℚ)⟩
theorem b1352 (b : ℝ) (hb : rootInterval.Contains b) : i1352.Contains (n1352 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1056 b hb) (b691 b hb))
    (by norm_num [i1352, i1056, i691, RationalInterval.mul]) (by norm_num [i1352, i1056, i691, RationalInterval.mul])

def n1353 (b : ℝ) : ℝ := (n1351 b) + (n1352 b)
def i1353 : RationalInterval := ⟨(763713841039369676608394804613 / 1000000000000000000000000000000 : ℚ), (763713846966240822864149482161 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1353 (b : ℝ) (hb : rootInterval.Contains b) : i1353.Contains (n1353 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1351 b hb) (b1352 b hb))
    (by norm_num [i1353, i1351, i1352, RationalInterval.add]) (by norm_num [i1353, i1351, i1352, RationalInterval.add])

def n1354 (b : ℝ) : ℝ := (n16 b) * (n779 b)
def i1354 : RationalInterval := ⟨(-171216653903855658357629379219 / 125000000000000000000000000000 : ℚ), (-1369733182936433252643470728353 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1354 (b : ℝ) (hb : rootInterval.Contains b) : i1354.Contains (n1354 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b16 b hb) (b779 b hb))
    (by norm_num [i1354, i16, i779, RationalInterval.mul]) (by norm_num [i1354, i16, i779, RationalInterval.mul])

def n1355 (b : ℝ) : ℝ := (n1353 b) + (n1354 b)
def i1355 : RationalInterval := ⟨(-606019390191475590252640229139 / 1000000000000000000000000000000 : ℚ), (-37876208498137026861207577887 / 62500000000000000000000000000 : ℚ)⟩
theorem b1355 (b : ℝ) (hb : rootInterval.Contains b) : i1355.Contains (n1355 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1353 b hb) (b1354 b hb))
    (by norm_num [i1355, i1353, i1354, RationalInterval.add]) (by norm_num [i1355, i1353, i1354, RationalInterval.add])

def n1356 (b : ℝ) : ℝ := (n910 b) * (n16 b)
def i1356 : RationalInterval := ⟨(1768232691010024671817980790127 / 1000000000000000000000000000000 : ℚ), (884116346702097944038491538273 / 500000000000000000000000000000 : ℚ)⟩
theorem b1356 (b : ℝ) (hb : rootInterval.Contains b) : i1356.Contains (n1356 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b910 b hb) (b16 b hb))
    (by norm_num [i1356, i910, i16, RationalInterval.mul]) (by norm_num [i1356, i910, i16, RationalInterval.mul])

def n1357 (b : ℝ) : ℝ := (n16 b) * (n836 b)
def i1357 : RationalInterval := ⟨(3067602138885138871495013924657 / 1000000000000000000000000000000 : ℚ), (3067602149870848110882426568201 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1357 (b : ℝ) (hb : rootInterval.Contains b) : i1357.Contains (n1357 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b16 b hb) (b836 b hb))
    (by norm_num [i1357, i16, i836, RationalInterval.mul]) (by norm_num [i1357, i16, i836, RationalInterval.mul])

def n1358 (b : ℝ) : ℝ := (n1356 b) + (n1357 b)
def i1358 : RationalInterval := ⟨(151119838434223860728531084837 / 31250000000000000000000000000 : ℚ), (4835834843275043998959409644747 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1358 (b : ℝ) (hb : rootInterval.Contains b) : i1358.Contains (n1358 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1356 b hb) (b1357 b hb))
    (by norm_num [i1358, i1356, i1357, RationalInterval.add]) (by norm_num [i1358, i1356, i1357, RationalInterval.add])

def n1359 (b : ℝ) : ℝ := (n1056 b) * (n16 b)
def i1359 : RationalInterval := ⟨(-291788442495475801245289912559 / 200000000000000000000000000000 : ℚ), (-364735552772911116658818257047 / 250000000000000000000000000000 : ℚ)⟩
theorem b1359 (b : ℝ) (hb : rootInterval.Contains b) : i1359.Contains (n1359 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1056 b hb) (b16 b hb))
    (by norm_num [i1359, i1056, i16, RationalInterval.mul]) (by norm_num [i1359, i1056, i16, RationalInterval.mul])

def n1360 (b : ℝ) : ℝ := (n16 b) * (n902 b)
def i1360 : RationalInterval := ⟨(-62527453554013995769646826049 / 50000000000000000000000000000 : ℚ), (-1250549064544054267270525428567 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1360 (b : ℝ) (hb : rootInterval.Contains b) : i1360.Contains (n1360 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b16 b hb) (b902 b hb))
    (by norm_num [i1360, i16, i902, RationalInterval.mul]) (by norm_num [i1360, i16, i902, RationalInterval.mul])

def n1361 (b : ℝ) : ℝ := (n1359 b) + (n1360 b)
def i1361 : RationalInterval := ⟨(-108379651342306356864775443351 / 40000000000000000000000000000 : ℚ), (-541898255127139746781159691351 / 200000000000000000000000000000 : ℚ)⟩
theorem b1361 (b : ℝ) (hb : rootInterval.Contains b) : i1361.Contains (n1361 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1359 b hb) (b1360 b hb))
    (by norm_num [i1361, i1359, i1360, RationalInterval.add]) (by norm_num [i1361, i1359, i1360, RationalInterval.add])

def n1362 (b : ℝ) : ℝ := (n1044 b) * (n583 b)
def i1362 : RationalInterval := ⟨(273826180445562689152375415569 / 200000000000000000000000000000 : ℚ), (1369131236354007162179620613837 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1362 (b : ℝ) (hb : rootInterval.Contains b) : i1362.Contains (n1362 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1044 b hb) (b583 b hb))
    (by norm_num [i1362, i1044, i583, RationalInterval.mul]) (by norm_num [i1362, i1044, i583, RationalInterval.mul])

def n1363 (b : ℝ) : ℝ := (n1155 b) * (n582 b)
def i1363 : RationalInterval := ⟨(897886297043263142337211682791 / 1000000000000000000000000000000 : ℚ), (897886537665859983758781296339 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1363 (b : ℝ) (hb : rootInterval.Contains b) : i1363.Contains (n1363 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1155 b hb) (b582 b hb))
    (by norm_num [i1363, i1155, i582, RationalInterval.mul]) (by norm_num [i1363, i1155, i582, RationalInterval.mul])

def n1364 (b : ℝ) : ℝ := (n1362 b) + (n1363 b)
def i1364 : RationalInterval := ⟨(566754299817769147024772190159 / 250000000000000000000000000000 : ℚ), (70844305438120848310575059693 / 31250000000000000000000000000 : ℚ)⟩
theorem b1364 (b : ℝ) (hb : rootInterval.Contains b) : i1364.Contains (n1364 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1362 b hb) (b1363 b hb))
    (by norm_num [i1364, i1362, i1363, RationalInterval.add]) (by norm_num [i1364, i1362, i1363, RationalInterval.add])

def n1365 (b : ℝ) : ℝ := (n1172 b) * (n680 b)
def i1365 : RationalInterval := ⟨(-4725105600648486841297758253 / 200000000000000000000000000000 : ℚ), (-2362550628457975958028225927 / 100000000000000000000000000000 : ℚ)⟩
theorem b1365 (b : ℝ) (hb : rootInterval.Contains b) : i1365.Contains (n1365 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1172 b hb) (b680 b hb))
    (by norm_num [i1365, i1172, i680, RationalInterval.mul]) (by norm_num [i1365, i1172, i680, RationalInterval.mul])

def n1366 (b : ℝ) : ℝ := (n1364 b) + (n1365 b)
def i1366 : RationalInterval := ⟨(2243391671267834153892599969371 / 1000000000000000000000000000000 : ℚ), (1121696133867643693179059825453 / 500000000000000000000000000000 : ℚ)⟩
theorem b1366 (b : ℝ) (hb : rootInterval.Contains b) : i1366.Contains (n1366 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1364 b hb) (b1365 b hb))
    (by norm_num [i1366, i1364, i1365, RationalInterval.add]) (by norm_num [i1366, i1364, i1365, RationalInterval.add])

def n1367 (b : ℝ) : ℝ := (n1255 b) * (n681 b)
def i1367 : RationalInterval := ⟨(-292225790549389482881440133091 / 1000000000000000000000000000000 : ℚ), (-292225666426518722114726502189 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1367 (b : ℝ) (hb : rootInterval.Contains b) : i1367.Contains (n1367 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1255 b hb) (b681 b hb))
    (by norm_num [i1367, i1255, i681, RationalInterval.mul]) (by norm_num [i1367, i1255, i681, RationalInterval.mul])

def n1368 (b : ℝ) : ℝ := (n1366 b) + (n1367 b)
def i1368 : RationalInterval := ⟨(48779147017961116775278995907 / 25000000000000000000000000000 : ℚ), (1951166601308768664243393148717 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1368 (b : ℝ) (hb : rootInterval.Contains b) : i1368.Contains (n1368 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1366 b hb) (b1367 b hb))
    (by norm_num [i1368, i1366, i1367, RationalInterval.add]) (by norm_num [i1368, i1366, i1367, RationalInterval.add])

def n1369 (b : ℝ) : ℝ := (n1319 b) * (n683 b)
def i1369 : RationalInterval := ⟨(-568044089887689326239083589279 / 1000000000000000000000000000000 : ℚ), (-284021944902990678060776013213 / 500000000000000000000000000000 : ℚ)⟩
theorem b1369 (b : ℝ) (hb : rootInterval.Contains b) : i1369.Contains (n1369 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1319 b hb) (b683 b hb))
    (by norm_num [i1369, i1319, i683, RationalInterval.mul]) (by norm_num [i1369, i1319, i683, RationalInterval.mul])

def n1370 (b : ℝ) : ℝ := (n1368 b) + (n1369 b)
def i1370 : RationalInterval := ⟨(1383121790830755344772076247001 / 1000000000000000000000000000000 : ℚ), (1383122711502787308121841122291 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1370 (b : ℝ) (hb : rootInterval.Contains b) : i1370.Contains (n1370 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1368 b hb) (b1369 b hb))
    (by norm_num [i1370, i1368, i1369, RationalInterval.add]) (by norm_num [i1370, i1368, i1369, RationalInterval.add])

def n1371 (b : ℝ) : ℝ := (n1044 b) * (n689 b)
def i1371 : RationalInterval := ⟨(1508727817980364538313213781969 / 500000000000000000000000000000 : ℚ), (1508728182643173858808937047187 / 500000000000000000000000000000 : ℚ)⟩
theorem b1371 (b : ℝ) (hb : rootInterval.Contains b) : i1371.Contains (n1371 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1044 b hb) (b689 b hb))
    (by norm_num [i1371, i1044, i689, RationalInterval.mul]) (by norm_num [i1371, i1044, i689, RationalInterval.mul])

def n1372 (b : ℝ) : ℝ := (n1155 b) * (n691 b)
def i1372 : RationalInterval := ⟨(-3941521149266225999372943214831 / 1000000000000000000000000000000 : ℚ), (-3941520099990363507371447932933 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1372 (b : ℝ) (hb : rootInterval.Contains b) : i1372.Contains (n1372 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1155 b hb) (b691 b hb))
    (by norm_num [i1372, i1155, i691, RationalInterval.mul]) (by norm_num [i1372, i1155, i691, RationalInterval.mul])

def n1373 (b : ℝ) : ℝ := (n1371 b) + (n1372 b)
def i1373 : RationalInterval := ⟨(-924065513305496922746515650893 / 1000000000000000000000000000000 : ℚ), (-924063734704015789753573838559 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1373 (b : ℝ) (hb : rootInterval.Contains b) : i1373.Contains (n1373 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1371 b hb) (b1372 b hb))
    (by norm_num [i1373, i1371, i1372, RationalInterval.add]) (by norm_num [i1373, i1371, i1372, RationalInterval.add])

def n1374 (b : ℝ) : ℝ := (n1172 b) * (n776 b)
def i1374 : RationalInterval := ⟨(97401453754956581129622312041 / 200000000000000000000000000000 : ℚ), (15218978183279231453782928539 / 31250000000000000000000000000 : ℚ)⟩
theorem b1374 (b : ℝ) (hb : rootInterval.Contains b) : i1374.Contains (n1374 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1172 b hb) (b776 b hb))
    (by norm_num [i1374, i1172, i776, RationalInterval.mul]) (by norm_num [i1374, i1172, i776, RationalInterval.mul])

def n1375 (b : ℝ) : ℝ := (n1373 b) + (n1374 b)
def i1375 : RationalInterval := ⟨(-6829035070792406517162563917 / 15625000000000000000000000000 : ℚ), (-437056432839080383232520125311 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1375 (b : ℝ) (hb : rootInterval.Contains b) : i1375.Contains (n1375 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1373 b hb) (b1374 b hb))
    (by norm_num [i1375, i1373, i1374, RationalInterval.add]) (by norm_num [i1375, i1373, i1374, RationalInterval.add])

def n1376 (b : ℝ) : ℝ := (n1255 b) * (n777 b)
def i1376 : RationalInterval := ⟨(2019215776074515212916542918491 / 1000000000000000000000000000000 : ℚ), (50480405822351550960661738061 / 25000000000000000000000000000 : ℚ)⟩
theorem b1376 (b : ℝ) (hb : rootInterval.Contains b) : i1376.Contains (n1376 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1255 b hb) (b777 b hb))
    (by norm_num [i1376, i1255, i777, RationalInterval.mul]) (by norm_num [i1376, i1255, i777, RationalInterval.mul])

def n1377 (b : ℝ) : ℝ := (n1375 b) + (n1376 b)
def i1377 : RationalInterval := ⟨(1582157531543801195818138827803 / 1000000000000000000000000000000 : ℚ), (1582159800054981655193949397129 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1377 (b : ℝ) (hb : rootInterval.Contains b) : i1377.Contains (n1377 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1375 b hb) (b1376 b hb))
    (by norm_num [i1377, i1375, i1376, RationalInterval.add]) (by norm_num [i1377, i1375, i1376, RationalInterval.add])

def n1378 (b : ℝ) : ℝ := (n1319 b) * (n779 b)
def i1378 : RationalInterval := ⟨(482181117973516663565053278061 / 200000000000000000000000000000 : ℚ), (2410906234999778378663666588179 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1378 (b : ℝ) (hb : rootInterval.Contains b) : i1378.Contains (n1378 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1319 b hb) (b779 b hb))
    (by norm_num [i1378, i1319, i779, RationalInterval.mul]) (by norm_num [i1378, i1319, i779, RationalInterval.mul])

def n1379 (b : ℝ) : ℝ := (n1377 b) + (n1378 b)
def i1379 : RationalInterval := ⟨(998265780352846128410851304527 / 250000000000000000000000000000 : ℚ), (998266508763690008464403996327 / 250000000000000000000000000000 : ℚ)⟩
theorem b1379 (b : ℝ) (hb : rootInterval.Contains b) : i1379.Contains (n1379 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1377 b hb) (b1378 b hb))
    (by norm_num [i1379, i1377, i1378, RationalInterval.add]) (by norm_num [i1379, i1377, i1378, RationalInterval.add])

def n1380 (b : ℝ) : ℝ := (n1044 b) * (n16 b)
def i1380 : RationalInterval := ⟨(-16638343583542555303806858491 / 3125000000000000000000000000 : ℚ), (-1331067167575843869730133552077 / 250000000000000000000000000000 : ℚ)⟩
theorem b1380 (b : ℝ) (hb : rootInterval.Contains b) : i1380.Contains (n1380 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1044 b hb) (b16 b hb))
    (by norm_num [i1380, i1044, i16, RationalInterval.mul]) (by norm_num [i1380, i1044, i16, RationalInterval.mul])

def n1381 (b : ℝ) : ℝ := (n1172 b) * (n839 b)
def i1381 : RationalInterval := ⟨(-455014875664765939141496241811 / 500000000000000000000000000000 : ℚ), (-910029733388924933826366114317 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1381 (b : ℝ) (hb : rootInterval.Contains b) : i1381.Contains (n1381 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1172 b hb) (b839 b hb))
    (by norm_num [i1381, i1172, i839, RationalInterval.mul]) (by norm_num [i1381, i1172, i839, RationalInterval.mul])

def n1382 (b : ℝ) : ℝ := (n1380 b) + (n1381 b)
def i1382 : RationalInterval := ⟨(-3117149849031574787750593600371 / 500000000000000000000000000000 : ℚ), (-49874387229538403301975202581 / 8000000000000000000000000000 : ℚ)⟩
theorem b1382 (b : ℝ) (hb : rootInterval.Contains b) : i1382.Contains (n1382 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1380 b hb) (b1381 b hb))
    (by norm_num [i1382, i1380, i1381, RationalInterval.add]) (by norm_num [i1382, i1380, i1381, RationalInterval.add])

def n1383 (b : ℝ) : ℝ := (n1255 b) * (n840 b)
def i1383 : RationalInterval := ⟨(-4313910374821702331658783152087 / 1000000000000000000000000000000 : ℚ), (-4313909567586922163796899467899 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1383 (b : ℝ) (hb : rootInterval.Contains b) : i1383.Contains (n1383 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1255 b hb) (b840 b hb))
    (by norm_num [i1383, i1255, i840, RationalInterval.mul]) (by norm_num [i1383, i1255, i840, RationalInterval.mul])

def n1384 (b : ℝ) : ℝ := (n1382 b) + (n1383 b)
def i1384 : RationalInterval := ⟨(-10548210072884851907159970352829 / 1000000000000000000000000000000 : ℚ), (-2637051992819805644135949947631 / 250000000000000000000000000000 : ℚ)⟩
theorem b1384 (b : ℝ) (hb : rootInterval.Contains b) : i1384.Contains (n1384 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1382 b hb) (b1383 b hb))
    (by norm_num [i1384, i1382, i1383, RationalInterval.add]) (by norm_num [i1384, i1382, i1383, RationalInterval.add])

def n1385 (b : ℝ) : ℝ := (n1319 b) * (n836 b)
def i1385 : RationalInterval := ⟨(-5399373382345815715882730719389 / 1000000000000000000000000000000 : ℚ), (-539937210856864851061990244709 / 100000000000000000000000000000 : ℚ)⟩
theorem b1385 (b : ℝ) (hb : rootInterval.Contains b) : i1385.Contains (n1385 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1319 b hb) (b836 b hb))
    (by norm_num [i1385, i1319, i836, RationalInterval.mul]) (by norm_num [i1385, i1319, i836, RationalInterval.mul])

def n1386 (b : ℝ) : ℝ := (n1384 b) + (n1385 b)
def i1386 : RationalInterval := ⟨(-7973791727615333811521350536109 / 500000000000000000000000000000 : ℚ), (-7973790039923935543581851118807 / 500000000000000000000000000000 : ℚ)⟩
theorem b1386 (b : ℝ) (hb : rootInterval.Contains b) : i1386.Contains (n1386 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1384 b hb) (b1385 b hb))
    (by norm_num [i1386, i1384, i1385, RationalInterval.add]) (by norm_num [i1386, i1384, i1385, RationalInterval.add])

def n1387 (b : ℝ) : ℝ := (n1155 b) * (n16 b)
def i1387 : RationalInterval := ⟨(1628252123590168359971676034291 / 500000000000000000000000000000 : ℚ), (3256505112392413138284581844113 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1387 (b : ℝ) (hb : rootInterval.Contains b) : i1387.Contains (n1387 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1155 b hb) (b16 b hb))
    (by norm_num [i1387, i1155, i16, RationalInterval.mul]) (by norm_num [i1387, i1155, i16, RationalInterval.mul])

def n1388 (b : ℝ) : ℝ := (n1172 b) * (n896 b)
def i1388 : RationalInterval := ⟨(57745167816283733634433932759 / 125000000000000000000000000000 : ℚ), (230980676083909219543846315287 / 500000000000000000000000000000 : ℚ)⟩
theorem b1388 (b : ℝ) (hb : rootInterval.Contains b) : i1388.Contains (n1388 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1172 b hb) (b896 b hb))
    (by norm_num [i1388, i1172, i896, RationalInterval.mul]) (by norm_num [i1388, i1172, i896, RationalInterval.mul])

def n1389 (b : ℝ) : ℝ := (n1387 b) + (n1388 b)
def i1389 : RationalInterval := ⟨(1859232794855303294509411765327 / 500000000000000000000000000000 : ℚ), (3718466464560231577372274474687 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1389 (b : ℝ) (hb : rootInterval.Contains b) : i1389.Contains (n1389 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1387 b hb) (b1388 b hb))
    (by norm_num [i1389, i1387, i1388, RationalInterval.add]) (by norm_num [i1389, i1387, i1388, RationalInterval.add])

def n1390 (b : ℝ) : ℝ := (n1255 b) * (n900 b)
def i1390 : RationalInterval := ⟨(1208529731438874828154429526561 / 500000000000000000000000000000 : ℚ), (4720820148154102330119861059 / 1953125000000000000000000000 : ℚ)⟩
theorem b1390 (b : ℝ) (hb : rootInterval.Contains b) : i1390.Contains (n1390 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1255 b hb) (b900 b hb))
    (by norm_num [i1390, i1255, i900, RationalInterval.mul]) (by norm_num [i1390, i1255, i900, RationalInterval.mul])

def n1391 (b : ℝ) : ℝ := (n1389 b) + (n1390 b)
def i1391 : RationalInterval := ⟨(191735157893386132666490080743 / 31250000000000000000000000000 : ℚ), (1227105276083026394078728667379 / 200000000000000000000000000000 : ℚ)⟩
theorem b1391 (b : ℝ) (hb : rootInterval.Contains b) : i1391.Contains (n1391 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1389 b hb) (b1390 b hb))
    (by norm_num [i1391, i1389, i1390, RationalInterval.add]) (by norm_num [i1391, i1389, i1390, RationalInterval.add])

def n1392 (b : ℝ) : ℝ := (n1319 b) * (n902 b)
def i1392 : RationalInterval := ⟨(2201126297933059650116358989049 / 1000000000000000000000000000000 : ℚ), (17196303287713124141708355069 / 7812500000000000000000000000 : ℚ)⟩
theorem b1392 (b : ℝ) (hb : rootInterval.Contains b) : i1392.Contains (n1392 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1319 b hb) (b902 b hb))
    (by norm_num [i1392, i1319, i902, RationalInterval.mul]) (by norm_num [i1392, i1319, i902, RationalInterval.mul])

def n1393 (b : ℝ) : ℝ := (n1391 b) + (n1392 b)
def i1393 : RationalInterval := ⟨(333466054020856635817761662913 / 40000000000000000000000000000 : ℚ), (8336653201242411860532312785727 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1393 (b : ℝ) (hb : rootInterval.Contains b) : i1393.Contains (n1393 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1391 b hb) (b1392 b hb))
    (by norm_num [i1393, i1391, i1392, RationalInterval.add]) (by norm_num [i1393, i1391, i1392, RationalInterval.add])

def n1394 (b : ℝ) : ℝ := (n1172 b) * (n57 b)
def i1394 : RationalInterval := ⟨(263450226734869715371473061 / 500000000000000000000000000 : ℚ), (65862557545208964247290374439 / 125000000000000000000000000000 : ℚ)⟩
theorem b1394 (b : ℝ) (hb : rootInterval.Contains b) : i1394.Contains (n1394 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1172 b hb) (b57 b hb))
    (by norm_num [i1394, i1172, i57, RationalInterval.mul]) (by norm_num [i1394, i1172, i57, RationalInterval.mul])

def n1395 (b : ℝ) : ℝ := (n1255 b) * (n57 b)
def i1395 : RationalInterval := ⟨(223017830601004992365911776641 / 62500000000000000000000000000 : ℚ), (223017871297639938075626898977 / 62500000000000000000000000000 : ℚ)⟩
theorem b1395 (b : ℝ) (hb : rootInterval.Contains b) : i1395.Contains (n1395 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1255 b hb) (b57 b hb))
    (by norm_num [i1395, i1255, i57, RationalInterval.mul]) (by norm_num [i1395, i1255, i57, RationalInterval.mul])

def n1396 (b : ℝ) : ℝ := (n1394 b) + (n1395 b)
def i1396 : RationalInterval := ⟨(127974554471431853393672954633 / 31250000000000000000000000000 : ℚ), (511898300140488840398544172393 / 125000000000000000000000000000 : ℚ)⟩
theorem b1396 (b : ℝ) (hb : rootInterval.Contains b) : i1396.Contains (n1396 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1394 b hb) (b1395 b hb))
    (by norm_num [i1396, i1394, i1395, RationalInterval.add]) (by norm_num [i1396, i1394, i1395, RationalInterval.add])

def n1397 (b : ℝ) : ℝ := (n1319 b) * (n57 b)
def i1397 : RationalInterval := ⟨(1760127899288447714648462118877 / 250000000000000000000000000000 : ℚ), (1760128308220523190068415437627 / 250000000000000000000000000000 : ℚ)⟩
theorem b1397 (b : ℝ) (hb : rootInterval.Contains b) : i1397.Contains (n1397 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1319 b hb) (b57 b hb))
    (by norm_num [i1397, i1319, i57, RationalInterval.mul]) (by norm_num [i1397, i1319, i57, RationalInterval.mul])

def n1398 (b : ℝ) : ℝ := (n1396 b) + (n1397 b)
def i1398 : RationalInterval := ⟨(2783924335059902541797845755941 / 250000000000000000000000000000 : ℚ), (2783924908501500870865503782413 / 250000000000000000000000000000 : ℚ)⟩
theorem b1398 (b : ℝ) (hb : rootInterval.Contains b) : i1398.Contains (n1398 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1396 b hb) (b1397 b hb))
    (by norm_num [i1398, i1396, i1397, RationalInterval.add]) (by norm_num [i1398, i1396, i1397, RationalInterval.add])

def n1399 (b : ℝ) : ℝ := (n1045 b) * (n583 b)
def i1399 : RationalInterval := ⟨(936152731059133863499874543477 / 1000000000000000000000000000000 : ℚ), (3744611779821439493881053307 / 4000000000000000000000000000 : ℚ)⟩
theorem b1399 (b : ℝ) (hb : rootInterval.Contains b) : i1399.Contains (n1399 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1045 b hb) (b583 b hb))
    (by norm_num [i1399, i1045, i583, RationalInterval.mul]) (by norm_num [i1399, i1045, i583, RationalInterval.mul])

def n1400 (b : ℝ) : ℝ := (n1156 b) * (n582 b)
def i1400 : RationalInterval := ⟨(626401745746871177686993625557 / 1000000000000000000000000000000 : ℚ), (5011215198392593097333912487 / 8000000000000000000000000000 : ℚ)⟩
theorem b1400 (b : ℝ) (hb : rootInterval.Contains b) : i1400.Contains (n1400 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1156 b hb) (b582 b hb))
    (by norm_num [i1400, i1156, i582, RationalInterval.mul]) (by norm_num [i1400, i1156, i582, RationalInterval.mul])

def n1401 (b : ℝ) : ℝ := (n1399 b) + (n1400 b)
def i1401 : RationalInterval := ⟨(781277238403002520593434084517 / 500000000000000000000000000000 : ℚ), (12500438758035472085096019101 / 8000000000000000000000000000 : ℚ)⟩
theorem b1401 (b : ℝ) (hb : rootInterval.Contains b) : i1401.Contains (n1401 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1399 b hb) (b1400 b hb))
    (by norm_num [i1401, i1399, i1400, RationalInterval.add]) (by norm_num [i1401, i1399, i1400, RationalInterval.add])

def n1402 (b : ℝ) : ℝ := (n1173 b) * (n680 b)
def i1402 : RationalInterval := ⟨(5368986247206084086787531537 / 200000000000000000000000000000 : ℚ), (1342247785127512632588702701 / 50000000000000000000000000000 : ℚ)⟩
theorem b1402 (b : ℝ) (hb : rootInterval.Contains b) : i1402.Contains (n1402 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1173 b hb) (b680 b hb))
    (by norm_num [i1402, i1173, i680, RationalInterval.mul]) (by norm_num [i1402, i1173, i680, RationalInterval.mul])

def n1403 (b : ℝ) : ℝ := (n1401 b) + (n1402 b)
def i1403 : RationalInterval := ⟨(1589399408042035461620805826719 / 1000000000000000000000000000000 : ℚ), (317879960091396852657755288329 / 200000000000000000000000000000 : ℚ)⟩
theorem b1403 (b : ℝ) (hb : rootInterval.Contains b) : i1403.Contains (n1403 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1401 b hb) (b1402 b hb))
    (by norm_num [i1403, i1401, i1402, RationalInterval.add]) (by norm_num [i1403, i1401, i1402, RationalInterval.add])

def n1404 (b : ℝ) : ℝ := (n1256 b) * (n681 b)
def i1404 : RationalInterval := ⟨(-161541134401997047531919675701 / 500000000000000000000000000000 : ℚ), (-323082157441359926538757976489 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1404 (b : ℝ) (hb : rootInterval.Contains b) : i1404.Contains (n1404 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1256 b hb) (b681 b hb))
    (by norm_num [i1404, i1256, i681, RationalInterval.mul]) (by norm_num [i1404, i1256, i681, RationalInterval.mul])

def n1405 (b : ℝ) : ℝ := (n1403 b) + (n1404 b)
def i1405 : RationalInterval := ⟨(1266317139238041366556966475317 / 1000000000000000000000000000000 : ℚ), (316579410753906084187504616289 / 250000000000000000000000000000 : ℚ)⟩
theorem b1405 (b : ℝ) (hb : rootInterval.Contains b) : i1405.Contains (n1405 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1403 b hb) (b1404 b hb))
    (by norm_num [i1405, i1403, i1404, RationalInterval.add]) (by norm_num [i1405, i1403, i1404, RationalInterval.add])

def n1406 (b : ℝ) : ℝ := (n1326 b) * (n683 b)
def i1406 : RationalInterval := ⟨(-393890288298088324862428190603 / 1000000000000000000000000000000 : ℚ), (-3938901553004952832479379121 / 10000000000000000000000000000 : ℚ)⟩
theorem b1406 (b : ℝ) (hb : rootInterval.Contains b) : i1406.Contains (n1406 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1326 b hb) (b683 b hb))
    (by norm_num [i1406, i1326, i683, RationalInterval.mul]) (by norm_num [i1406, i1326, i683, RationalInterval.mul])

def n1407 (b : ℝ) : ℝ := (n1405 b) + (n1406 b)
def i1407 : RationalInterval := ⟨(436213425469976520847269142357 / 500000000000000000000000000000 : ℚ), (27263358991097782921940017283 / 31250000000000000000000000000 : ℚ)⟩
theorem b1407 (b : ℝ) (hb : rootInterval.Contains b) : i1407.Contains (n1407 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1405 b hb) (b1406 b hb))
    (by norm_num [i1407, i1405, i1406, RationalInterval.add]) (by norm_num [i1407, i1405, i1406, RationalInterval.add])

def n1408 (b : ℝ) : ℝ := (n1045 b) * (n689 b)
def i1408 : RationalInterval := ⟨(2063206176895119145483359579139 / 1000000000000000000000000000000 : ℚ), (2063206643476740181063488850959 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1408 (b : ℝ) (hb : rootInterval.Contains b) : i1408.Contains (n1408 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1045 b hb) (b689 b hb))
    (by norm_num [i1408, i1045, i689, RationalInterval.mul]) (by norm_num [i1408, i1045, i689, RationalInterval.mul])

def n1409 (b : ℝ) : ℝ := (n1156 b) * (n691 b)
def i1409 : RationalInterval := ⟨(-2749764288054623130918176942651 / 1000000000000000000000000000000 : ℚ), (-2749763616685846947964046310769 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1409 (b : ℝ) (hb : rootInterval.Contains b) : i1409.Contains (n1409 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1156 b hb) (b691 b hb))
    (by norm_num [i1409, i1156, i691, RationalInterval.mul]) (by norm_num [i1409, i1156, i691, RationalInterval.mul])

def n1410 (b : ℝ) : ℝ := (n1408 b) + (n1409 b)
def i1410 : RationalInterval := ⟨(-85819763894937998179352170439 / 125000000000000000000000000000 : ℚ), (-68655697320910676690055745981 / 100000000000000000000000000000 : ℚ)⟩
theorem b1410 (b : ℝ) (hb : rootInterval.Contains b) : i1410.Contains (n1410 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1408 b hb) (b1409 b hb))
    (by norm_num [i1410, i1408, i1409, RationalInterval.add]) (by norm_num [i1410, i1408, i1409, RationalInterval.add])

def n1411 (b : ℝ) : ℝ := (n1173 b) * (n776 b)
def i1411 : RationalInterval := ⟨(-138342828185558857786252712393 / 250000000000000000000000000000 : ℚ), (-553371279507315795250000114041 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1411 (b : ℝ) (hb : rootInterval.Contains b) : i1411.Contains (n1411 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1173 b hb) (b776 b hb))
    (by norm_num [i1411, i1173, i776, RationalInterval.mul]) (by norm_num [i1411, i1173, i776, RationalInterval.mul])

def n1412 (b : ℝ) : ℝ := (n1410 b) + (n1411 b)
def i1412 : RationalInterval := ⟨(-309982355975434854144957053271 / 250000000000000000000000000000 : ℚ), (-1239928252716422562150557573851 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1412 (b : ℝ) (hb : rootInterval.Contains b) : i1412.Contains (n1412 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1410 b hb) (b1411 b hb))
    (by norm_num [i1412, i1410, i1411, RationalInterval.add]) (by norm_num [i1412, i1410, i1411, RationalInterval.add])

def n1413 (b : ℝ) : ℝ := (n1256 b) * (n777 b)
def i1413 : RationalInterval := ⟨(2232427415604254986265073220071 / 1000000000000000000000000000000 : ℚ), (2232427741927895454755911336403 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1413 (b : ℝ) (hb : rootInterval.Contains b) : i1413.Contains (n1413 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1256 b hb) (b777 b hb))
    (by norm_num [i1413, i1256, i777, RationalInterval.mul]) (by norm_num [i1413, i1256, i777, RationalInterval.mul])

def n1414 (b : ℝ) : ℝ := (n1412 b) + (n1413 b)
def i1414 : RationalInterval := ⟨(992497991702515569685245006987 / 1000000000000000000000000000000 : ℚ), (124062436151434111575669220319 / 125000000000000000000000000000 : ℚ)⟩
theorem b1414 (b : ℝ) (hb : rootInterval.Contains b) : i1414.Contains (n1414 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1412 b hb) (b1413 b hb))
    (by norm_num [i1414, i1412, i1413, RationalInterval.add]) (by norm_num [i1414, i1412, i1413, RationalInterval.add])

def n1415 (b : ℝ) : ℝ := (n1326 b) * (n779 b)
def i1415 : RationalInterval := ⟨(417939526438761105773139048689 / 250000000000000000000000000000 : ℚ), (334351705745755655419831826373 / 200000000000000000000000000000 : ℚ)⟩
theorem b1415 (b : ℝ) (hb : rootInterval.Contains b) : i1415.Contains (n1415 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1326 b hb) (b779 b hb))
    (by norm_num [i1415, i1326, i779, RationalInterval.mul]) (by norm_num [i1415, i1326, i779, RationalInterval.mul])

def n1416 (b : ℝ) : ℝ := (n1414 b) + (n1415 b)
def i1416 : RationalInterval := ⟨(2664256097457559992777801201743 / 1000000000000000000000000000000 : ℚ), (2664258017940251169704512894417 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1416 (b : ℝ) (hb : rootInterval.Contains b) : i1416.Contains (n1416 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1414 b hb) (b1415 b hb))
    (by norm_num [i1416, i1414, i1415, RationalInterval.add]) (by norm_num [i1416, i1414, i1415, RationalInterval.add])

def n1417 (b : ℝ) : ℝ := (n1045 b) * (n16 b)
def i1417 : RationalInterval := ⟨(-3640506372234449498691245406357 / 1000000000000000000000000000000 : ℚ), (-1820252778053114169957012253959 / 500000000000000000000000000000 : ℚ)⟩
theorem b1417 (b : ℝ) (hb : rootInterval.Contains b) : i1417.Contains (n1417 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1045 b hb) (b16 b hb))
    (by norm_num [i1417, i1045, i16, RationalInterval.mul]) (by norm_num [i1417, i1045, i16, RationalInterval.mul])

def n1418 (b : ℝ) : ℝ := (n1173 b) * (n839 b)
def i1418 : RationalInterval := ⟨(41361544292515602969245791541 / 40000000000000000000000000000 : ℚ), (1034038619542864945491584886207 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1418 (b : ℝ) (hb : rootInterval.Contains b) : i1418.Contains (n1418 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1173 b hb) (b839 b hb))
    (by norm_num [i1418, i1173, i839, RationalInterval.mul]) (by norm_num [i1418, i1173, i839, RationalInterval.mul])

def n1419 (b : ℝ) : ℝ := (n1417 b) + (n1418 b)
def i1419 : RationalInterval := ⟨(-325808470615194928057512577229 / 125000000000000000000000000000 : ℚ), (-2606466936563363394422439621711 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1419 (b : ℝ) (hb : rootInterval.Contains b) : i1419.Contains (n1419 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1417 b hb) (b1418 b hb))
    (by norm_num [i1419, i1417, i1418, RationalInterval.add]) (by norm_num [i1419, i1417, i1418, RationalInterval.add])

def n1420 (b : ℝ) : ℝ := (n1256 b) * (n840 b)
def i1420 : RationalInterval := ⟨(-596177680234098337680235028811 / 125000000000000000000000000000 : ℚ), (-4769420931249274958250755238741 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1420 (b : ℝ) (hb : rootInterval.Contains b) : i1420.Contains (n1420 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1256 b hb) (b840 b hb))
    (by norm_num [i1420, i1256, i840, RationalInterval.mul]) (by norm_num [i1420, i1256, i840, RationalInterval.mul])

def n1421 (b : ℝ) : ℝ := (n1419 b) + (n1420 b)
def i1421 : RationalInterval := ⟨(-23049653771232331643443690151 / 3125000000000000000000000000 : ℚ), (-1843971966953159588168298715113 / 250000000000000000000000000000 : ℚ)⟩
theorem b1421 (b : ℝ) (hb : rootInterval.Contains b) : i1421.Contains (n1421 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1419 b hb) (b1420 b hb))
    (by norm_num [i1421, i1419, i1420, RationalInterval.add]) (by norm_num [i1421, i1419, i1420, RationalInterval.add])

def n1422 (b : ℝ) : ℝ := (n1326 b) * (n836 b)
def i1422 : RationalInterval := ⟨(-1872003226564428759473884399251 / 500000000000000000000000000000 : ℚ), (-468000703056517898432863814641 / 125000000000000000000000000000 : ℚ)⟩
theorem b1422 (b : ℝ) (hb : rootInterval.Contains b) : i1422.Contains (n1422 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1326 b hb) (b836 b hb))
    (by norm_num [i1422, i1326, i836, RationalInterval.mul]) (by norm_num [i1422, i1326, i836, RationalInterval.mul])

def n1423 (b : ℝ) : ℝ := (n1421 b) + (n1422 b)
def i1423 : RationalInterval := ⟨(-5559947829961601822424874823411 / 500000000000000000000000000000 : ℚ), (-555994674613239077006805268879 / 50000000000000000000000000000 : ℚ)⟩
theorem b1423 (b : ℝ) (hb : rootInterval.Contains b) : i1423.Contains (n1423 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1421 b hb) (b1422 b hb))
    (by norm_num [i1423, i1421, i1422, RationalInterval.add]) (by norm_num [i1423, i1421, i1422, RationalInterval.add])

def n1424 (b : ℝ) : ℝ := (n1156 b) * (n16 b)
def i1424 : RationalInterval := ⟨(2271868890507831445514134200017 / 1000000000000000000000000000000 : ℚ), (2271869444006663043205542194133 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1424 (b : ℝ) (hb : rootInterval.Contains b) : i1424.Contains (n1424 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1156 b hb) (b16 b hb))
    (by norm_num [i1424, i1156, i16, RationalInterval.mul]) (by norm_num [i1424, i1156, i16, RationalInterval.mul])

def n1425 (b : ℝ) : ℝ := (n1173 b) * (n896 b)
def i1425 : RationalInterval := ⟨(-262456187932250853471359496303 / 500000000000000000000000000000 : ℚ), (-52491236905359631926474353477 / 100000000000000000000000000000 : ℚ)⟩
theorem b1425 (b : ℝ) (hb : rootInterval.Contains b) : i1425.Contains (n1425 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1173 b hb) (b896 b hb))
    (by norm_num [i1425, i1173, i896, RationalInterval.mul]) (by norm_num [i1425, i1173, i896, RationalInterval.mul])

def n1426 (b : ℝ) : ℝ := (n1424 b) + (n1425 b)
def i1426 : RationalInterval := ⟨(1746956514643329738571415207411 / 1000000000000000000000000000000 : ℚ), (1746957074953066723940798659363 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1426 (b : ℝ) (hb : rootInterval.Contains b) : i1426.Contains (n1426 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1424 b hb) (b1425 b hb))
    (by norm_num [i1426, i1424, i1425, RationalInterval.add]) (by norm_num [i1426, i1424, i1425, RationalInterval.add])

def n1427 (b : ℝ) : ℝ := (n1256 b) * (n900 b)
def i1427 : RationalInterval := ⟨(2672279938582877756892919185083 / 1000000000000000000000000000000 : ℚ), (1336140112721518567002294912897 / 500000000000000000000000000000 : ℚ)⟩
theorem b1427 (b : ℝ) (hb : rootInterval.Contains b) : i1427.Contains (n1427 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1256 b hb) (b900 b hb))
    (by norm_num [i1427, i1256, i900, RationalInterval.mul]) (by norm_num [i1427, i1256, i900, RationalInterval.mul])

def n1428 (b : ℝ) : ℝ := (n1426 b) + (n1427 b)
def i1428 : RationalInterval := ⟨(2209618226613103747732167196247 / 500000000000000000000000000000 : ℚ), (4419237300396103857945388485157 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1428 (b : ℝ) (hb : rootInterval.Contains b) : i1428.Contains (n1428 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1426 b hb) (b1427 b hb))
    (by norm_num [i1428, i1426, i1427, RationalInterval.add]) (by norm_num [i1428, i1426, i1427, RationalInterval.add])

def n1429 (b : ℝ) : ℝ := (n1326 b) * (n902 b)
def i1429 : RationalInterval := ⟨(1526293997502528558357900817443 / 1000000000000000000000000000000 : ℚ), (763147168917584396004572836757 / 500000000000000000000000000000 : ℚ)⟩
theorem b1429 (b : ℝ) (hb : rootInterval.Contains b) : i1429.Contains (n1429 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1326 b hb) (b902 b hb))
    (by norm_num [i1429, i1326, i902, RationalInterval.mul]) (by norm_num [i1429, i1326, i902, RationalInterval.mul])

def n1430 (b : ℝ) : ℝ := (n1428 b) + (n1429 b)
def i1430 : RationalInterval := ⟨(5945530450728736053822235209937 / 1000000000000000000000000000000 : ℚ), (5945531638231272649954534158671 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1430 (b : ℝ) (hb : rootInterval.Contains b) : i1430.Contains (n1430 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1428 b hb) (b1429 b hb))
    (by norm_num [i1430, i1428, i1429, RationalInterval.add]) (by norm_num [i1430, i1428, i1429, RationalInterval.add])

def n1431 (b : ℝ) : ℝ := (n1173 b) * (n57 b)
def i1431 : RationalInterval := ⟨(-149675168276886392697950549157 / 250000000000000000000000000000 : ℚ), (-37418791874897590650759664567 / 62500000000000000000000000000 : ℚ)⟩
theorem b1431 (b : ℝ) (hb : rootInterval.Contains b) : i1431.Contains (n1431 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1173 b hb) (b57 b hb))
    (by norm_num [i1431, i1173, i57, RationalInterval.mul]) (by norm_num [i1431, i1173, i57, RationalInterval.mul])

def n1432 (b : ℝ) : ℝ := (n1256 b) * (n57 b)
def i1432 : RationalInterval := ⟨(246566575549524701614171699591 / 62500000000000000000000000000 : ℚ), (19725328064225287863051181113 / 5000000000000000000000000000 : ℚ)⟩
theorem b1432 (b : ℝ) (hb : rootInterval.Contains b) : i1432.Contains (n1432 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1256 b hb) (b57 b hb))
    (by norm_num [i1432, i1256, i57, RationalInterval.mul]) (by norm_num [i1432, i1256, i57, RationalInterval.mul])

def n1433 (b : ℝ) : ℝ := (n1431 b) + (n1432 b)
def i1433 : RationalInterval := ⟨(836591133921212413758736249207 / 250000000000000000000000000000 : ℚ), (418295617855837015274760198691 / 125000000000000000000000000000 : ℚ)⟩
theorem b1433 (b : ℝ) (hb : rootInterval.Contains b) : i1433.Contains (n1433 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1431 b hb) (b1432 b hb))
    (by norm_num [i1433, i1431, i1432, RationalInterval.add]) (by norm_num [i1433, i1431, i1432, RationalInterval.add])

def n1434 (b : ℝ) : ℝ := (n1326 b) * (n57 b)
def i1434 : RationalInterval := ⟨(244099818356029063290732604519 / 50000000000000000000000000000 : ℚ), (610249678773775686107440588983 / 125000000000000000000000000000 : ℚ)⟩
theorem b1434 (b : ℝ) (hb : rootInterval.Contains b) : i1434.Contains (n1434 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1326 b hb) (b57 b hb))
    (by norm_num [i1434, i1326, i57, RationalInterval.mul]) (by norm_num [i1434, i1326, i57, RationalInterval.mul])

def n1435 (b : ℝ) : ℝ := (n1433 b) + (n1434 b)
def i1435 : RationalInterval := ⟨(1028545112850678865106199635901 / 125000000000000000000000000000 : ℚ), (514272648314806350691100393837 / 62500000000000000000000000000 : ℚ)⟩
theorem b1435 (b : ℝ) (hb : rootInterval.Contains b) : i1435.Contains (n1435 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1433 b hb) (b1434 b hb))
    (by norm_num [i1435, i1433, i1434, RationalInterval.add]) (by norm_num [i1435, i1433, i1434, RationalInterval.add])

def n1436 (b : ℝ) : ℝ := (n1047 b) * (n583 b)
def i1436 : RationalInterval := ⟨(630765034908335338155956959681 / 1000000000000000000000000000000 : ℚ), (630765171791422974514343952563 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1436 (b : ℝ) (hb : rootInterval.Contains b) : i1436.Contains (n1436 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1047 b hb) (b583 b hb))
    (by norm_num [i1436, i1047, i583, RationalInterval.mul]) (by norm_num [i1436, i1047, i583, RationalInterval.mul])

def n1437 (b : ℝ) : ℝ := (n1158 b) * (n582 b)
def i1437 : RationalInterval := ⟨(108159700611626053272562160133 / 250000000000000000000000000000 : ℚ), (216319450530173269152458629373 / 500000000000000000000000000000 : ℚ)⟩
theorem b1437 (b : ℝ) (hb : rootInterval.Contains b) : i1437.Contains (n1437 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1158 b hb) (b582 b hb))
    (by norm_num [i1437, i1158, i582, RationalInterval.mul]) (by norm_num [i1437, i1158, i582, RationalInterval.mul])

def n1438 (b : ℝ) : ℝ := (n1436 b) + (n1437 b)
def i1438 : RationalInterval := ⟨(1063403837354839551246205600213 / 1000000000000000000000000000000 : ℚ), (1063404072851769512819261211309 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1438 (b : ℝ) (hb : rootInterval.Contains b) : i1438.Contains (n1438 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1436 b hb) (b1437 b hb))
    (by norm_num [i1438, i1436, i1437, RationalInterval.add]) (by norm_num [i1438, i1436, i1437, RationalInterval.add])

def n1439 (b : ℝ) : ℝ := (n1171 b) * (n680 b)
def i1439 : RationalInterval := ⟨(-1525154587321082671745262547 / 50000000000000000000000000000 : ℚ), (-15251532026826797966483962701 / 500000000000000000000000000000 : ℚ)⟩
theorem b1439 (b : ℝ) (hb : rootInterval.Contains b) : i1439.Contains (n1439 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1171 b hb) (b680 b hb))
    (by norm_num [i1439, i1171, i680, RationalInterval.mul]) (by norm_num [i1439, i1171, i680, RationalInterval.mul])

