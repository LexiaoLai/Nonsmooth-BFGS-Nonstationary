import BFGS.Counterexample.Certificates.IntervalTrace25

/-! Generated arithmetic proofs. Each bound is checked by the Lean kernel. -/
namespace BFGS.Counterexample.Trace
noncomputable section
open BFGS RationalInterval
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false

def n2340 (b : ℝ) : ℝ := (n232 b) * (n2335 b)
def i2340 : RationalInterval := ⟨(834354310169010760696541074573 / 1000000000000000000000000000000 : ℚ), (8343543116683220991275130721 / 10000000000000000000000000000 : ℚ)⟩
theorem b2340 (b : ℝ) (hb : rootInterval.Contains b) : i2340.Contains (n2340 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b232 b hb) (b2335 b hb))
    (by norm_num [i2340, i232, i2335, RationalInterval.mul]) (by norm_num [i2340, i232, i2335, RationalInterval.mul])

def n2341 (b : ℝ) : ℝ := (n2339 b) + (n2340 b)
def i2341 : RationalInterval := ⟨(965358068800499512769794643607 / 1000000000000000000000000000000 : ℚ), (19307161439933288112029644149 / 20000000000000000000000000000 : ℚ)⟩
theorem b2341 (b : ℝ) (hb : rootInterval.Contains b) : i2341.Contains (n2341 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2339 b hb) (b2340 b hb))
    (by norm_num [i2341, i2339, i2340, RationalInterval.add]) (by norm_num [i2341, i2339, i2340, RationalInterval.add])

def n2342 (b : ℝ) : ℝ := -(n225 b)
def i2342 : RationalInterval := ⟨(-47109131716218335954434337871 / 1000000000000000000000000000000 : ℚ), (-2944320702957190077038693799 / 62500000000000000000000000000 : ℚ)⟩
theorem b2342 (b : ℝ) (hb : rootInterval.Contains b) : i2342.Contains (n2342 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b225 b hb))
    (by norm_num [i2342, i225, RationalInterval.neg]) (by norm_num [i2342, i225, RationalInterval.neg])

def n2343 (b : ℝ) : ℝ := -(n227 b)
def i2343 : RationalInterval := ⟨(-5895777650030349157036835989 / 500000000000000000000000000000 : ℚ), (-11791555133961309053995509269 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2343 (b : ℝ) (hb : rootInterval.Contains b) : i2343.Contains (n2343 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b227 b hb))
    (by norm_num [i2343, i227, RationalInterval.neg]) (by norm_num [i2343, i227, RationalInterval.neg])

def n2344 (b : ℝ) : ℝ := (n2338 b) + (n2342 b)
def i2344 : RationalInterval := ⟨(-656227357757454701688505363323 / 500000000000000000000000000000 : ℚ), (-328113677781293997155908739541 / 250000000000000000000000000000 : ℚ)⟩
theorem b2344 (b : ℝ) (hb : rootInterval.Contains b) : i2344.Contains (n2344 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2338 b hb) (b2342 b hb))
    (by norm_num [i2344, i2338, i2342, RationalInterval.add]) (by norm_num [i2344, i2338, i2342, RationalInterval.add])

def n2345 (b : ℝ) : ℝ := (n2341 b) + (n2343 b)
def i2345 : RationalInterval := ⟨(953566513500438814455720971629 / 1000000000000000000000000000000 : ℚ), (953566516862703096547486698181 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2345 (b : ℝ) (hb : rootInterval.Contains b) : i2345.Contains (n2345 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2341 b hb) (b2343 b hb))
    (by norm_num [i2345, i2341, i2343, RationalInterval.add]) (by norm_num [i2345, i2341, i2343, RationalInterval.add])

def n2346 (b : ℝ) : ℝ := (n2333 b) * (n332 b)
def i2346 : RationalInterval := ⟨(-237578478161754940095740374733 / 1000000000000000000000000000000 : ℚ), (-237578475243114652179926123001 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2346 (b : ℝ) (hb : rootInterval.Contains b) : i2346.Contains (n2346 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2333 b hb) (b332 b hb))
    (by norm_num [i2346, i2333, i332, RationalInterval.mul]) (by norm_num [i2346, i2333, i332, RationalInterval.mul])

def n2347 (b : ℝ) : ℝ := (n2334 b) * (n331 b)
def i2347 : RationalInterval := ⟨(59407795321915610613734174243 / 1000000000000000000000000000000 : ℚ), (232061703497523101421327623 / 3906250000000000000000000000 : ℚ)⟩
theorem b2347 (b : ℝ) (hb : rootInterval.Contains b) : i2347.Contains (n2347 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2334 b hb) (b331 b hb))
    (by norm_num [i2347, i2334, i331, RationalInterval.mul]) (by norm_num [i2347, i2334, i331, RationalInterval.mul])

def n2348 (b : ℝ) : ℝ := (n2346 b) + (n2347 b)
def i2348 : RationalInterval := ⟨(-17817068283983932948200620049 / 100000000000000000000000000000 : ℚ), (-178170679147748738216066251513 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2348 (b : ℝ) (hb : rootInterval.Contains b) : i2348.Contains (n2348 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2346 b hb) (b2347 b hb))
    (by norm_num [i2348, i2346, i2347, RationalInterval.add]) (by norm_num [i2348, i2346, i2347, RationalInterval.add])

def n2349 (b : ℝ) : ℝ := (n318 b) * (n2344 b)
def i2349 : RationalInterval := ⟨(-409893364232658238250126622407 / 250000000000000000000000000000 : ℚ), (-65582937607778992382877953353 / 40000000000000000000000000000 : ℚ)⟩
theorem b2349 (b : ℝ) (hb : rootInterval.Contains b) : i2349.Contains (n2349 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b318 b hb) (b2344 b hb))
    (by norm_num [i2349, i318, i2344, RationalInterval.mul]) (by norm_num [i2349, i318, i2344, RationalInterval.mul])

def n2350 (b : ℝ) : ℝ := (n319 b) * (n2345 b)
def i2350 : RationalInterval := ⟨(513466092014725543882748388957 / 1000000000000000000000000000000 : ℚ), (128366524765065024195917960177 / 250000000000000000000000000000 : ℚ)⟩
theorem b2350 (b : ℝ) (hb : rootInterval.Contains b) : i2350.Contains (n2350 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b319 b hb) (b2345 b hb))
    (by norm_num [i2350, i319, i2345, RationalInterval.mul]) (by norm_num [i2350, i319, i2345, RationalInterval.mul])

def n2351 (b : ℝ) : ℝ := (n2349 b) + (n2350 b)
def i2351 : RationalInterval := ⟨(-1126107364915907409117758100671 / 1000000000000000000000000000000 : ℚ), (-1126107341134214712788276993117 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2351 (b : ℝ) (hb : rootInterval.Contains b) : i2351.Contains (n2351 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2349 b hb) (b2350 b hb))
    (by norm_num [i2351, i2349, i2350, RationalInterval.add]) (by norm_num [i2351, i2349, i2350, RationalInterval.add])

def n2352 (b : ℝ) : ℝ := (n2348 b) + (n2351 b)
def i2352 : RationalInterval := ⟨(-1304278047755746738599764301161 / 1000000000000000000000000000000 : ℚ), (-130427802028196345100434324463 / 100000000000000000000000000000 : ℚ)⟩
theorem b2352 (b : ℝ) (hb : rootInterval.Contains b) : i2352.Contains (n2352 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2348 b hb) (b2351 b hb))
    (by norm_num [i2352, i2348, i2351, RationalInterval.add]) (by norm_num [i2352, i2348, i2351, RationalInterval.add])

def n2353 (b : ℝ) : ℝ := (n118 b) * (n2344 b)
def i2353 : RationalInterval := ⟨(-2799950576962897453159129850731 / 1000000000000000000000000000000 : ℚ), (-2799950563433201700363192850521 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2353 (b : ℝ) (hb : rootInterval.Contains b) : i2353.Contains (n2353 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b118 b hb) (b2344 b hb))
    (by norm_num [i2353, i118, i2344, RationalInterval.mul]) (by norm_num [i2353, i118, i2344, RationalInterval.mul])

def n2354 (b : ℝ) : ℝ := (n119 b) * (n2345 b)
def i2354 : RationalInterval := ⟨(126048030039384332564048284179 / 125000000000000000000000000000 : ℚ), (504192123757633529131434469607 / 500000000000000000000000000000 : ℚ)⟩
theorem b2354 (b : ℝ) (hb : rootInterval.Contains b) : i2354.Contains (n2354 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b119 b hb) (b2345 b hb))
    (by norm_num [i2354, i119, i2345, RationalInterval.mul]) (by norm_num [i2354, i119, i2345, RationalInterval.mul])

def n2355 (b : ℝ) : ℝ := (n2353 b) + (n2354 b)
def i2355 : RationalInterval := ⟨(-1791566336647822792646743577299 / 1000000000000000000000000000000 : ℚ), (-1791566315917934642100323911307 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2355 (b : ℝ) (hb : rootInterval.Contains b) : i2355.Contains (n2355 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2353 b hb) (b2354 b hb))
    (by norm_num [i2355, i2353, i2354, RationalInterval.add]) (by norm_num [i2355, i2353, i2354, RationalInterval.add])

def n2356 (b : ℝ) : ℝ := (n120 b) * (n2344 b)
def i2356 : RationalInterval := ⟨(-2710749747121948731743609883 / 1953125000000000000000000000 : ℚ), (-346975965816961030025018100351 / 250000000000000000000000000000 : ℚ)⟩
theorem b2356 (b : ℝ) (hb : rootInterval.Contains b) : i2356.Contains (n2356 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b120 b hb) (b2344 b hb))
    (by norm_num [i2356, i120, i2344, RationalInterval.mul]) (by norm_num [i2356, i120, i2344, RationalInterval.mul])

def n2357 (b : ℝ) : ℝ := (n121 b) * (n2345 b)
def i2357 : RationalInterval := ⟨(286811531030789527380956567859 / 500000000000000000000000000000 : ℚ), (573623066573308869724922135031 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2357 (b : ℝ) (hb : rootInterval.Contains b) : i2357.Contains (n2357 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b121 b hb) (b2345 b hb))
    (by norm_num [i2357, i121, i2345, RationalInterval.mul]) (by norm_num [i2357, i121, i2345, RationalInterval.mul])

def n2358 (b : ℝ) : ℝ := (n2356 b) + (n2357 b)
def i2358 : RationalInterval := ⟨(-407140404232429347945407562189 / 500000000000000000000000000000 : ℚ), (-814280796694535250375150266373 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2358 (b : ℝ) (hb : rootInterval.Contains b) : i2358.Contains (n2358 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2356 b hb) (b2357 b hb))
    (by norm_num [i2358, i2356, i2357, RationalInterval.add]) (by norm_num [i2358, i2356, i2357, RationalInterval.add])

def n2359 (b : ℝ) : ℝ := (n2344 b) * (n2210 b)
def i2359 : RationalInterval := ⟨(-4439524033893530406159636340359 / 1000000000000000000000000000000 : ℚ), (-4439524003627676509935141684347 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2359 (b : ℝ) (hb : rootInterval.Contains b) : i2359.Contains (n2359 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2344 b hb) (b2210 b hb))
    (by norm_num [i2359, i2344, i2210, RationalInterval.mul]) (by norm_num [i2359, i2344, i2210, RationalInterval.mul])

def n2360 (b : ℝ) : ℝ := (n2345 b) * (n2213 b)
def i2360 : RationalInterval := ⟨(152185033320160667523524381341 / 100000000000000000000000000000 : ℚ), (1521850345703720681082946499339 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2360 (b : ℝ) (hb : rootInterval.Contains b) : i2360.Contains (n2360 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2345 b hb) (b2213 b hb))
    (by norm_num [i2360, i2345, i2213, RationalInterval.mul]) (by norm_num [i2360, i2345, i2213, RationalInterval.mul])

def n2361 (b : ℝ) : ℝ := (n2359 b) + (n2360 b)
def i2361 : RationalInterval := ⟨(-2917673700691923730924392526949 / 1000000000000000000000000000000 : ℚ), (-182354603620247239303262199063 / 62500000000000000000000000000 : ℚ)⟩
theorem b2361 (b : ℝ) (hb : rootInterval.Contains b) : i2361.Contains (n2361 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2359 b hb) (b2360 b hb))
    (by norm_num [i2361, i2359, i2360, RationalInterval.add]) (by norm_num [i2361, i2359, i2360, RationalInterval.add])

def n2362 (b : ℝ) : ℝ := (n2361 b) * (n13 b)
def i2362 : RationalInterval := ⟨(-2917673700691923730924392526949 / 500000000000000000000000000000 : ℚ), (-182354603620247239303262199063 / 31250000000000000000000000000 : ℚ)⟩
theorem b2362 (b : ℝ) (hb : rootInterval.Contains b) : i2362.Contains (n2362 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2361 b hb) (b13 b hb))
    (by norm_num [i2362, i2361, i13, RationalInterval.mul]) (by norm_num [i2362, i2361, i13, RationalInterval.mul])

def n2363 (b : ℝ) : ℝ := (n2333 b) * (n318 b)
def i2363 : RationalInterval := ⟨(-70563799789097185736368102643 / 500000000000000000000000000000 : ℚ), (-35281899224373203403949665121 / 250000000000000000000000000000 : ℚ)⟩
theorem b2363 (b : ℝ) (hb : rootInterval.Contains b) : i2363.Contains (n2363 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2333 b hb) (b318 b hb))
    (by norm_num [i2363, i2333, i318, RationalInterval.mul]) (by norm_num [i2363, i2333, i318, RationalInterval.mul])

def n2364 (b : ℝ) : ℝ := (n2333 b) * (n319 b)
def i2364 : RationalInterval := ⟨(-30415586118019537523885632737 / 500000000000000000000000000000 : ℚ), (-60831170877833922559643399471 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2364 (b : ℝ) (hb : rootInterval.Contains b) : i2364.Contains (n2364 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2333 b hb) (b319 b hb))
    (by norm_num [i2364, i2333, i319, RationalInterval.mul]) (by norm_num [i2364, i2333, i319, RationalInterval.mul])

def n2365 (b : ℝ) : ℝ := (n2334 b) * (n318 b)
def i2365 : RationalInterval := ⟨(-35547535306861605439218902241 / 500000000000000000000000000000 : ℚ), (-7109506922575472841028858091 / 100000000000000000000000000000 : ℚ)⟩
theorem b2365 (b : ℝ) (hb : rootInterval.Contains b) : i2365.Contains (n2365 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2334 b hb) (b318 b hb))
    (by norm_num [i2365, i2334, i318, RationalInterval.mul]) (by norm_num [i2365, i2334, i318, RationalInterval.mul])

def n2366 (b : ℝ) : ℝ := (n2334 b) * (n319 b)
def i2366 : RationalInterval := ⟨(-239410807276691372876056517 / 7812500000000000000000000000 : ℚ), (-7661145657756448050958412549 / 250000000000000000000000000000 : ℚ)⟩
theorem b2366 (b : ℝ) (hb : rootInterval.Contains b) : i2366.Contains (n2366 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2334 b hb) (b319 b hb))
    (by norm_num [i2366, i2334, i319, RationalInterval.mul]) (by norm_num [i2366, i2334, i319, RationalInterval.mul])

def n2367 (b : ℝ) : ℝ := (n318 b) * (n2333 b)
def i2367 : RationalInterval := ⟨(-70563799789097185736368102643 / 500000000000000000000000000000 : ℚ), (-35281899224373203403949665121 / 250000000000000000000000000000 : ℚ)⟩
theorem b2367 (b : ℝ) (hb : rootInterval.Contains b) : i2367.Contains (n2367 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b318 b hb) (b2333 b hb))
    (by norm_num [i2367, i318, i2333, RationalInterval.mul]) (by norm_num [i2367, i318, i2333, RationalInterval.mul])

def n2368 (b : ℝ) : ℝ := (n318 b) * (n2334 b)
def i2368 : RationalInterval := ⟨(-35547535306861605439218902241 / 500000000000000000000000000000 : ℚ), (-7109506922575472841028858091 / 100000000000000000000000000000 : ℚ)⟩
theorem b2368 (b : ℝ) (hb : rootInterval.Contains b) : i2368.Contains (n2368 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b318 b hb) (b2334 b hb))
    (by norm_num [i2368, i318, i2334, RationalInterval.mul]) (by norm_num [i2368, i318, i2334, RationalInterval.mul])

def n2369 (b : ℝ) : ℝ := (n319 b) * (n2333 b)
def i2369 : RationalInterval := ⟨(-30415586118019537523885632737 / 500000000000000000000000000000 : ℚ), (-60831170877833922559643399471 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2369 (b : ℝ) (hb : rootInterval.Contains b) : i2369.Contains (n2369 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b319 b hb) (b2333 b hb))
    (by norm_num [i2369, i319, i2333, RationalInterval.mul]) (by norm_num [i2369, i319, i2333, RationalInterval.mul])

def n2370 (b : ℝ) : ℝ := (n319 b) * (n2334 b)
def i2370 : RationalInterval := ⟨(-239410807276691372876056517 / 7812500000000000000000000000 : ℚ), (-7661145657756448050958412549 / 250000000000000000000000000000 : ℚ)⟩
theorem b2370 (b : ℝ) (hb : rootInterval.Contains b) : i2370.Contains (n2370 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b319 b hb) (b2334 b hb))
    (by norm_num [i2370, i319, i2334, RationalInterval.mul]) (by norm_num [i2370, i319, i2334, RationalInterval.mul])

def n2371 (b : ℝ) : ℝ := (n2363 b) + (n2367 b)
def i2371 : RationalInterval := ⟨(-70563799789097185736368102643 / 250000000000000000000000000000 : ℚ), (-35281899224373203403949665121 / 125000000000000000000000000000 : ℚ)⟩
theorem b2371 (b : ℝ) (hb : rootInterval.Contains b) : i2371.Contains (n2371 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2363 b hb) (b2367 b hb))
    (by norm_num [i2371, i2363, i2367, RationalInterval.add]) (by norm_num [i2371, i2363, i2367, RationalInterval.add])

def n2372 (b : ℝ) : ℝ := (n2364 b) + (n2368 b)
def i2372 : RationalInterval := ⟨(-32981560712440571481552267489 / 250000000000000000000000000000 : ℚ), (-131926240103588650969931980381 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2372 (b : ℝ) (hb : rootInterval.Contains b) : i2372.Contains (n2372 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2364 b hb) (b2368 b hb))
    (by norm_num [i2372, i2364, i2368, RationalInterval.add]) (by norm_num [i2372, i2364, i2368, RationalInterval.add])

def n2373 (b : ℝ) : ℝ := (n2365 b) + (n2369 b)
def i2373 : RationalInterval := ⟨(-32981560712440571481552267489 / 250000000000000000000000000000 : ℚ), (-131926240103588650969931980381 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2373 (b : ℝ) (hb : rootInterval.Contains b) : i2373.Contains (n2373 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2365 b hb) (b2369 b hb))
    (by norm_num [i2373, i2365, i2369, RationalInterval.add]) (by norm_num [i2373, i2365, i2369, RationalInterval.add])

def n2374 (b : ℝ) : ℝ := (n2366 b) + (n2370 b)
def i2374 : RationalInterval := ⟨(-239410807276691372876056517 / 3906250000000000000000000000 : ℚ), (-7661145657756448050958412549 / 125000000000000000000000000000 : ℚ)⟩
theorem b2374 (b : ℝ) (hb : rootInterval.Contains b) : i2374.Contains (n2374 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2366 b hb) (b2370 b hb))
    (by norm_num [i2374, i2366, i2370, RationalInterval.add]) (by norm_num [i2374, i2366, i2370, RationalInterval.add])

def n2375 (b : ℝ) : ℝ := (n2355 b) * (n318 b)
def i2375 : RationalInterval := ⟨(-2238099781405259623182240807417 / 1000000000000000000000000000000 : ℚ), (-223809974014863590165881858077 / 100000000000000000000000000000 : ℚ)⟩
theorem b2375 (b : ℝ) (hb : rootInterval.Contains b) : i2375.Contains (n2375 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2355 b hb) (b318 b hb))
    (by norm_num [i2375, i2355, i318, RationalInterval.mul]) (by norm_num [i2375, i2355, i318, RationalInterval.mul])

def n2376 (b : ℝ) : ℝ := (n2355 b) * (n319 b)
def i2376 : RationalInterval := ⟨(-120587887921127716131308443147 / 125000000000000000000000000000 : ℚ), (-24117577059273950587835749467 / 25000000000000000000000000000 : ℚ)⟩
theorem b2376 (b : ℝ) (hb : rootInterval.Contains b) : i2376.Contains (n2376 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2355 b hb) (b319 b hb))
    (by norm_num [i2376, i2355, i319, RationalInterval.mul]) (by norm_num [i2376, i2355, i319, RationalInterval.mul])

def n2377 (b : ℝ) : ℝ := (n2358 b) * (n318 b)
def i2377 : RationalInterval := ⟨(-813786980542465890195852029 / 800000000000000000000000000 : ℚ), (-1017233703992871459909385940409 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2377 (b : ℝ) (hb : rootInterval.Contains b) : i2377.Contains (n2377 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2358 b hb) (b318 b hb))
    (by norm_num [i2377, i2358, i318, RationalInterval.mul]) (by norm_num [i2377, i2358, i318, RationalInterval.mul])

def n2378 (b : ℝ) : ℝ := (n2358 b) * (n319 b)
def i2378 : RationalInterval := ⟨(-438465049756236047763982563579 / 1000000000000000000000000000000 : ℚ), (-17538601557915880215043060791 / 40000000000000000000000000000 : ℚ)⟩
theorem b2378 (b : ℝ) (hb : rootInterval.Contains b) : i2378.Contains (n2378 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2358 b hb) (b319 b hb))
    (by norm_num [i2378, i2358, i319, RationalInterval.mul]) (by norm_num [i2378, i2358, i319, RationalInterval.mul])

def n2379 (b : ℝ) : ℝ := (n2210 b) * (n2333 b)
def i2379 : RationalInterval := ⟨(-382135589914959201303897834357 / 1000000000000000000000000000000 : ℚ), (-191067791975940525458800936003 / 500000000000000000000000000000 : ℚ)⟩
theorem b2379 (b : ℝ) (hb : rootInterval.Contains b) : i2379.Contains (n2379 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2210 b hb) (b2333 b hb))
    (by norm_num [i2379, i2210, i2333, RationalInterval.mul]) (by norm_num [i2379, i2210, i2333, RationalInterval.mul])

def n2380 (b : ℝ) : ℝ := (n2210 b) * (n2334 b)
def i2380 : RationalInterval := ⟨(-192506333489842204434436545607 / 1000000000000000000000000000000 : ℚ), (-7700253215369768750354254299 / 40000000000000000000000000000 : ℚ)⟩
theorem b2380 (b : ℝ) (hb : rootInterval.Contains b) : i2380.Contains (n2380 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2210 b hb) (b2334 b hb))
    (by norm_num [i2380, i2210, i2334, RationalInterval.mul]) (by norm_num [i2380, i2210, i2334, RationalInterval.mul])

def n2381 (b : ℝ) : ℝ := (n2213 b) * (n2333 b)
def i2381 : RationalInterval := ⟨(-180296110427562970788976089477 / 1000000000000000000000000000000 : ℚ), (-360592214789600826206478129 / 2000000000000000000000000000 : ℚ)⟩
theorem b2381 (b : ℝ) (hb : rootInterval.Contains b) : i2381.Contains (n2381 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2213 b hb) (b2333 b hb))
    (by norm_num [i2381, i2213, i2333, RationalInterval.mul]) (by norm_num [i2381, i2213, i2333, RationalInterval.mul])

def n2382 (b : ℝ) : ℝ := (n2213 b) * (n2334 b)
def i2382 : RationalInterval := ⟨(-90826774780684089870572682807 / 1000000000000000000000000000000 : ℚ), (-11353346650618093974511175033 / 125000000000000000000000000000 : ℚ)⟩
theorem b2382 (b : ℝ) (hb : rootInterval.Contains b) : i2382.Contains (n2382 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2213 b hb) (b2334 b hb))
    (by norm_num [i2382, i2213, i2334, RationalInterval.mul]) (by norm_num [i2382, i2213, i2334, RationalInterval.mul])

def n2383 (b : ℝ) : ℝ := (n2375 b) + (n2379 b)
def i2383 : RationalInterval := ⟨(-1310117685660109412243069320887 / 500000000000000000000000000000 : ℚ), (-327529415512564619072052556597 / 125000000000000000000000000000 : ℚ)⟩
theorem b2383 (b : ℝ) (hb : rootInterval.Contains b) : i2383.Contains (n2383 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2375 b hb) (b2379 b hb))
    (by norm_num [i2383, i2375, i2379, RationalInterval.add]) (by norm_num [i2383, i2375, i2379, RationalInterval.add])

def n2384 (b : ℝ) : ℝ := (n2376 b) + (n2380 b)
def i2384 : RationalInterval := ⟨(-1157209436858863933484904090783 / 1000000000000000000000000000000 : ℚ), (-231441882551040448454457267231 / 200000000000000000000000000000 : ℚ)⟩
theorem b2384 (b : ℝ) (hb : rootInterval.Contains b) : i2384.Contains (n2384 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2376 b hb) (b2380 b hb))
    (by norm_num [i2384, i2376, i2380, RationalInterval.add]) (by norm_num [i2384, i2376, i2380, RationalInterval.add])

def n2385 (b : ℝ) : ℝ := (n2377 b) + (n2381 b)
def i2385 : RationalInterval := ⟨(-1197529836105645333533791125727 / 1000000000000000000000000000000 : ℚ), (-1197529811387671873012625004909 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2385 (b : ℝ) (hb : rootInterval.Contains b) : i2385.Contains (n2385 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2377 b hb) (b2381 b hb))
    (by norm_num [i2385, i2377, i2381, RationalInterval.add]) (by norm_num [i2385, i2377, i2381, RationalInterval.add])

def n2386 (b : ℝ) : ℝ := (n2378 b) + (n2382 b)
def i2386 : RationalInterval := ⟨(-264645912268460068817277623193 / 500000000000000000000000000000 : ℚ), (-529291812152841757172165920039 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2386 (b : ℝ) (hb : rootInterval.Contains b) : i2386.Contains (n2386 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2378 b hb) (b2382 b hb))
    (by norm_num [i2386, i2378, i2382, RationalInterval.add]) (by norm_num [i2386, i2378, i2382, RationalInterval.add])

def n2387 (b : ℝ) : ℝ := (n2333 b) * (n2210 b)
def i2387 : RationalInterval := ⟨(-382135589914959201303897834357 / 1000000000000000000000000000000 : ℚ), (-191067791975940525458800936003 / 500000000000000000000000000000 : ℚ)⟩
theorem b2387 (b : ℝ) (hb : rootInterval.Contains b) : i2387.Contains (n2387 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2333 b hb) (b2210 b hb))
    (by norm_num [i2387, i2333, i2210, RationalInterval.mul]) (by norm_num [i2387, i2333, i2210, RationalInterval.mul])

def n2388 (b : ℝ) : ℝ := (n2333 b) * (n2213 b)
def i2388 : RationalInterval := ⟨(-180296110427562970788976089477 / 1000000000000000000000000000000 : ℚ), (-360592214789600826206478129 / 2000000000000000000000000000 : ℚ)⟩
theorem b2388 (b : ℝ) (hb : rootInterval.Contains b) : i2388.Contains (n2388 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2333 b hb) (b2213 b hb))
    (by norm_num [i2388, i2333, i2213, RationalInterval.mul]) (by norm_num [i2388, i2333, i2213, RationalInterval.mul])

def n2389 (b : ℝ) : ℝ := (n2334 b) * (n2210 b)
def i2389 : RationalInterval := ⟨(-192506333489842204434436545607 / 1000000000000000000000000000000 : ℚ), (-7700253215369768750354254299 / 40000000000000000000000000000 : ℚ)⟩
theorem b2389 (b : ℝ) (hb : rootInterval.Contains b) : i2389.Contains (n2389 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2334 b hb) (b2210 b hb))
    (by norm_num [i2389, i2334, i2210, RationalInterval.mul]) (by norm_num [i2389, i2334, i2210, RationalInterval.mul])

def n2390 (b : ℝ) : ℝ := (n2334 b) * (n2213 b)
def i2390 : RationalInterval := ⟨(-90826774780684089870572682807 / 1000000000000000000000000000000 : ℚ), (-11353346650618093974511175033 / 125000000000000000000000000000 : ℚ)⟩
theorem b2390 (b : ℝ) (hb : rootInterval.Contains b) : i2390.Contains (n2390 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2334 b hb) (b2213 b hb))
    (by norm_num [i2390, i2334, i2213, RationalInterval.mul]) (by norm_num [i2390, i2334, i2213, RationalInterval.mul])

def n2391 (b : ℝ) : ℝ := (n318 b) * (n2355 b)
def i2391 : RationalInterval := ⟨(-2238099781405259623182240807417 / 1000000000000000000000000000000 : ℚ), (-223809974014863590165881858077 / 100000000000000000000000000000 : ℚ)⟩
theorem b2391 (b : ℝ) (hb : rootInterval.Contains b) : i2391.Contains (n2391 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b318 b hb) (b2355 b hb))
    (by norm_num [i2391, i318, i2355, RationalInterval.mul]) (by norm_num [i2391, i318, i2355, RationalInterval.mul])

def n2392 (b : ℝ) : ℝ := (n318 b) * (n2358 b)
def i2392 : RationalInterval := ⟨(-813786980542465890195852029 / 800000000000000000000000000 : ℚ), (-1017233703992871459909385940409 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2392 (b : ℝ) (hb : rootInterval.Contains b) : i2392.Contains (n2392 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b318 b hb) (b2358 b hb))
    (by norm_num [i2392, i318, i2358, RationalInterval.mul]) (by norm_num [i2392, i318, i2358, RationalInterval.mul])

def n2393 (b : ℝ) : ℝ := (n319 b) * (n2355 b)
def i2393 : RationalInterval := ⟨(-120587887921127716131308443147 / 125000000000000000000000000000 : ℚ), (-24117577059273950587835749467 / 25000000000000000000000000000 : ℚ)⟩
theorem b2393 (b : ℝ) (hb : rootInterval.Contains b) : i2393.Contains (n2393 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b319 b hb) (b2355 b hb))
    (by norm_num [i2393, i319, i2355, RationalInterval.mul]) (by norm_num [i2393, i319, i2355, RationalInterval.mul])

def n2394 (b : ℝ) : ℝ := (n319 b) * (n2358 b)
def i2394 : RationalInterval := ⟨(-438465049756236047763982563579 / 1000000000000000000000000000000 : ℚ), (-17538601557915880215043060791 / 40000000000000000000000000000 : ℚ)⟩
theorem b2394 (b : ℝ) (hb : rootInterval.Contains b) : i2394.Contains (n2394 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b319 b hb) (b2358 b hb))
    (by norm_num [i2394, i319, i2358, RationalInterval.mul]) (by norm_num [i2394, i319, i2358, RationalInterval.mul])

def n2395 (b : ℝ) : ℝ := (n2387 b) + (n2391 b)
def i2395 : RationalInterval := ⟨(-1310117685660109412243069320887 / 500000000000000000000000000000 : ℚ), (-327529415512564619072052556597 / 125000000000000000000000000000 : ℚ)⟩
theorem b2395 (b : ℝ) (hb : rootInterval.Contains b) : i2395.Contains (n2395 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2387 b hb) (b2391 b hb))
    (by norm_num [i2395, i2387, i2391, RationalInterval.add]) (by norm_num [i2395, i2387, i2391, RationalInterval.add])

def n2396 (b : ℝ) : ℝ := (n2388 b) + (n2392 b)
def i2396 : RationalInterval := ⟨(-1197529836105645333533791125727 / 1000000000000000000000000000000 : ℚ), (-1197529811387671873012625004909 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2396 (b : ℝ) (hb : rootInterval.Contains b) : i2396.Contains (n2396 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2388 b hb) (b2392 b hb))
    (by norm_num [i2396, i2388, i2392, RationalInterval.add]) (by norm_num [i2396, i2388, i2392, RationalInterval.add])

def n2397 (b : ℝ) : ℝ := (n2389 b) + (n2393 b)
def i2397 : RationalInterval := ⟨(-1157209436858863933484904090783 / 1000000000000000000000000000000 : ℚ), (-231441882551040448454457267231 / 200000000000000000000000000000 : ℚ)⟩
theorem b2397 (b : ℝ) (hb : rootInterval.Contains b) : i2397.Contains (n2397 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2389 b hb) (b2393 b hb))
    (by norm_num [i2397, i2389, i2393, RationalInterval.add]) (by norm_num [i2397, i2389, i2393, RationalInterval.add])

def n2398 (b : ℝ) : ℝ := (n2390 b) + (n2394 b)
def i2398 : RationalInterval := ⟨(-264645912268460068817277623193 / 500000000000000000000000000000 : ℚ), (-529291812152841757172165920039 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2398 (b : ℝ) (hb : rootInterval.Contains b) : i2398.Contains (n2398 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2390 b hb) (b2394 b hb))
    (by norm_num [i2398, i2390, i2394, RationalInterval.add]) (by norm_num [i2398, i2390, i2394, RationalInterval.add])

def n2399 (b : ℝ) : ℝ := (n2383 b) + (n2395 b)
def i2399 : RationalInterval := ⟨(-1310117685660109412243069320887 / 250000000000000000000000000000 : ℚ), (-327529415512564619072052556597 / 62500000000000000000000000000 : ℚ)⟩
theorem b2399 (b : ℝ) (hb : rootInterval.Contains b) : i2399.Contains (n2399 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2383 b hb) (b2395 b hb))
    (by norm_num [i2399, i2383, i2395, RationalInterval.add]) (by norm_num [i2399, i2383, i2395, RationalInterval.add])

def n2400 (b : ℝ) : ℝ := (n2384 b) + (n2396 b)
def i2400 : RationalInterval := ⟨(-235473927296450926701869521651 / 100000000000000000000000000000 : ℚ), (-294342403017859264410613917633 / 125000000000000000000000000000 : ℚ)⟩
theorem b2400 (b : ℝ) (hb : rootInterval.Contains b) : i2400.Contains (n2400 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2384 b hb) (b2396 b hb))
    (by norm_num [i2400, i2384, i2396, RationalInterval.add]) (by norm_num [i2400, i2384, i2396, RationalInterval.add])

def n2401 (b : ℝ) : ℝ := (n2385 b) + (n2397 b)
def i2401 : RationalInterval := ⟨(-235473927296450926701869521651 / 100000000000000000000000000000 : ℚ), (-294342403017859264410613917633 / 125000000000000000000000000000 : ℚ)⟩
theorem b2401 (b : ℝ) (hb : rootInterval.Contains b) : i2401.Contains (n2401 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2385 b hb) (b2397 b hb))
    (by norm_num [i2401, i2385, i2397, RationalInterval.add]) (by norm_num [i2401, i2385, i2397, RationalInterval.add])

def n2402 (b : ℝ) : ℝ := (n2386 b) + (n2398 b)
def i2402 : RationalInterval := ⟨(-264645912268460068817277623193 / 250000000000000000000000000000 : ℚ), (-529291812152841757172165920039 / 500000000000000000000000000000 : ℚ)⟩
theorem b2402 (b : ℝ) (hb : rootInterval.Contains b) : i2402.Contains (n2402 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2386 b hb) (b2398 b hb))
    (by norm_num [i2402, i2386, i2398, RationalInterval.add]) (by norm_num [i2402, i2386, i2398, RationalInterval.add])

def n2403 (b : ℝ) : ℝ := (n2284 b) * (n2399 b)
def i2403 : RationalInterval := ⟨(1268833995188040882309827699497 / 500000000000000000000000000000 : ℚ), (2537668066049013117167072539137 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2403 (b : ℝ) (hb : rootInterval.Contains b) : i2403.Contains (n2403 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2284 b hb) (b2399 b hb))
    (by norm_num [i2403, i2284, i2399, RationalInterval.mul]) (by norm_num [i2403, i2284, i2399, RationalInterval.mul])

def n2404 (b : ℝ) : ℝ := (n2284 b) * (n2400 b)
def i2404 : RationalInterval := ⟨(1140269024661303393801658542373 / 1000000000000000000000000000000 : ℚ), (1140269061756596330034601988213 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2404 (b : ℝ) (hb : rootInterval.Contains b) : i2404.Contains (n2404 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2284 b hb) (b2400 b hb))
    (by norm_num [i2404, i2284, i2400, RationalInterval.mul]) (by norm_num [i2404, i2284, i2400, RationalInterval.mul])

def n2405 (b : ℝ) : ℝ := (n2284 b) * (n2401 b)
def i2405 : RationalInterval := ⟨(1140269024661303393801658542373 / 1000000000000000000000000000000 : ℚ), (1140269061756596330034601988213 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2405 (b : ℝ) (hb : rootInterval.Contains b) : i2405.Contains (n2405 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2284 b hb) (b2401 b hb))
    (by norm_num [i2405, i2284, i2401, RationalInterval.mul]) (by norm_num [i2405, i2284, i2401, RationalInterval.mul])

def n2406 (b : ℝ) : ℝ := (n2284 b) * (n2402 b)
def i2406 : RationalInterval := ⟨(64076634497013320986374454671 / 125000000000000000000000000000 : ℚ), (512613094018114203640545502427 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2406 (b : ℝ) (hb : rootInterval.Contains b) : i2406.Contains (n2406 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2284 b hb) (b2402 b hb))
    (by norm_num [i2406, i2284, i2402, RationalInterval.mul]) (by norm_num [i2406, i2284, i2402, RationalInterval.mul])

def n2407 (b : ℝ) : ℝ := (n2352 b) * (n2290 b)
def i2407 : RationalInterval := ⟨(-152921735042716499938835841529 / 500000000000000000000000000000 : ℚ), (-152921728212962043145765946351 / 500000000000000000000000000000 : ℚ)⟩
theorem b2407 (b : ℝ) (hb : rootInterval.Contains b) : i2407.Contains (n2407 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2352 b hb) (b2290 b hb))
    (by norm_num [i2407, i2352, i2290, RationalInterval.mul]) (by norm_num [i2407, i2352, i2290, RationalInterval.mul])

def n2408 (b : ℝ) : ℝ := (n2407 b) * (n2225 b)
def i2408 : RationalInterval := ⟨(-1292402673334484839810060359723 / 500000000000000000000000000000 : ℚ), (-4135688327218195721794862289 / 1600000000000000000000000000 : ℚ)⟩
theorem b2408 (b : ℝ) (hb : rootInterval.Contains b) : i2408.Contains (n2408 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2407 b hb) (b2225 b hb))
    (by norm_num [i2408, i2407, i2225, RationalInterval.mul]) (by norm_num [i2408, i2407, i2225, RationalInterval.mul])

def n2409 (b : ℝ) : ℝ := (n2407 b) * (n2226 b)
def i2409 : RationalInterval := ⟨(-233368778533734927211809117081 / 200000000000000000000000000000 : ℚ), (-1166843825897073354114598205141 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2409 (b : ℝ) (hb : rootInterval.Contains b) : i2409.Contains (n2409 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2407 b hb) (b2226 b hb))
    (by norm_num [i2409, i2407, i2226, RationalInterval.mul]) (by norm_num [i2409, i2407, i2226, RationalInterval.mul])

def n2410 (b : ℝ) : ℝ := (n2407 b) * (n2227 b)
def i2410 : RationalInterval := ⟨(-233368778533734927211809117081 / 200000000000000000000000000000 : ℚ), (-1166843825897073354114598205141 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2410 (b : ℝ) (hb : rootInterval.Contains b) : i2410.Contains (n2410 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2407 b hb) (b2227 b hb))
    (by norm_num [i2410, i2407, i2227, RationalInterval.mul]) (by norm_num [i2410, i2407, i2227, RationalInterval.mul])

def n2411 (b : ℝ) : ℝ := (n2407 b) * (n2228 b)
def i2411 : RationalInterval := ⟨(-262833639535703702907648483159 / 500000000000000000000000000000 : ℚ), (-262833623884911918493756514119 / 500000000000000000000000000000 : ℚ)⟩
theorem b2411 (b : ℝ) (hb : rootInterval.Contains b) : i2411.Contains (n2411 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2407 b hb) (b2228 b hb))
    (by norm_num [i2411, i2407, i2228, RationalInterval.mul]) (by norm_num [i2411, i2407, i2228, RationalInterval.mul])

def n2412 (b : ℝ) : ℝ := (n2403 b) + (n2408 b)
def i2412 : RationalInterval := ⟨(-11784339073221978750116330113 / 250000000000000000000000000000 : ℚ), (-736517788474362639917443617 / 15625000000000000000000000000 : ℚ)⟩
theorem b2412 (b : ℝ) (hb : rootInterval.Contains b) : i2412.Contains (n2412 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2403 b hb) (b2408 b hb))
    (by norm_num [i2412, i2403, i2408, RationalInterval.add]) (by norm_num [i2412, i2403, i2408, RationalInterval.add])

def n2413 (b : ℝ) : ℝ := (n2404 b) + (n2409 b)
def i2413 : RationalInterval := ⟨(-3321858500921405282173380379 / 125000000000000000000000000000 : ℚ), (-830461379389907002499881779 / 31250000000000000000000000000 : ℚ)⟩
theorem b2413 (b : ℝ) (hb : rootInterval.Contains b) : i2413.Contains (n2413 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2404 b hb) (b2409 b hb))
    (by norm_num [i2413, i2404, i2409, RationalInterval.add]) (by norm_num [i2413, i2404, i2409, RationalInterval.add])

def n2414 (b : ℝ) : ℝ := (n2405 b) + (n2410 b)
def i2414 : RationalInterval := ⟨(-3321858500921405282173380379 / 125000000000000000000000000000 : ℚ), (-830461379389907002499881779 / 31250000000000000000000000000 : ℚ)⟩
theorem b2414 (b : ℝ) (hb : rootInterval.Contains b) : i2414.Contains (n2414 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2405 b hb) (b2410 b hb))
    (by norm_num [i2414, i2405, i2410, RationalInterval.add]) (by norm_num [i2414, i2405, i2410, RationalInterval.add])

def n2415 (b : ℝ) : ℝ := (n2406 b) + (n2411 b)
def i2415 : RationalInterval := ⟨(-261084061906016758486026579 / 20000000000000000000000000000 : ℚ), (-13054153751709633346967525811 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2415 (b : ℝ) (hb : rootInterval.Contains b) : i2415.Contains (n2415 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2406 b hb) (b2411 b hb))
    (by norm_num [i2415, i2406, i2411, RationalInterval.add]) (by norm_num [i2415, i2406, i2411, RationalInterval.add])

def n2416 (b : ℝ) : ℝ := (n2352 b) + (n2362 b)
def i2416 : RationalInterval := ⟨(-7139625449139594200448549355059 / 1000000000000000000000000000000 : ℚ), (-3569812668064937554354366807323 / 500000000000000000000000000000 : ℚ)⟩
theorem b2416 (b : ℝ) (hb : rootInterval.Contains b) : i2416.Contains (n2416 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2352 b hb) (b2362 b hb))
    (by norm_num [i2416, i2352, i2362, RationalInterval.add]) (by norm_num [i2416, i2352, i2362, RationalInterval.add])

def n2417 (b : ℝ) : ℝ := (n2416 b) * (n2290 b)
def i2417 : RationalInterval := ⟨(-1674188894179753704160697031237 / 1000000000000000000000000000000 : ℚ), (-334837765634661390096289446173 / 200000000000000000000000000000 : ℚ)⟩
theorem b2417 (b : ℝ) (hb : rootInterval.Contains b) : i2417.Contains (n2417 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2416 b hb) (b2290 b hb))
    (by norm_num [i2417, i2416, i2290, RationalInterval.mul]) (by norm_num [i2417, i2416, i2290, RationalInterval.mul])

def n2418 (b : ℝ) : ℝ := (n2303 b) * (n2352 b)
def i2418 : RationalInterval := ⟨(-4899362666323545209970578675749 / 250000000000000000000000000000 : ℚ), (-19597450099707508570535305237177 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2418 (b : ℝ) (hb : rootInterval.Contains b) : i2418.Contains (n2418 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2303 b hb) (b2352 b hb))
    (by norm_num [i2418, i2303, i2352, RationalInterval.mul]) (by norm_num [i2418, i2303, i2352, RationalInterval.mul])

def n2419 (b : ℝ) : ℝ := (n2418 b) * (n2306 b)
def i2419 : RationalInterval := ⟨(-1112661666142642340269998313353 / 500000000000000000000000000000 : ℚ), (-2225323189294193771784386337889 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2419 (b : ℝ) (hb : rootInterval.Contains b) : i2419.Contains (n2419 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2418 b hb) (b2306 b hb))
    (by norm_num [i2419, i2418, i2306, RationalInterval.mul]) (by norm_num [i2419, i2418, i2306, RationalInterval.mul])

def n2420 (b : ℝ) : ℝ := -(n2419 b)
def i2420 : RationalInterval := ⟨(2225323189294193771784386337889 / 1000000000000000000000000000000 : ℚ), (1112661666142642340269998313353 / 500000000000000000000000000000 : ℚ)⟩
theorem b2420 (b : ℝ) (hb : rootInterval.Contains b) : i2420.Contains (n2420 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b2419 b hb))
    (by norm_num [i2420, i2419, RationalInterval.neg]) (by norm_num [i2420, i2419, RationalInterval.neg])

def n2421 (b : ℝ) : ℝ := (n2417 b) + (n2420 b)
def i2421 : RationalInterval := ⟨(137783573778610016905922326663 / 250000000000000000000000000000 : ℚ), (551134504111977730058549395841 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2421 (b : ℝ) (hb : rootInterval.Contains b) : i2421.Contains (n2421 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2417 b hb) (b2420 b hb))
    (by norm_num [i2421, i2417, i2420, RationalInterval.add]) (by norm_num [i2421, i2417, i2420, RationalInterval.add])

def n2422 (b : ℝ) : ℝ := (n2421 b) * (n2229 b)
def i2422 : RationalInterval := ⟨(215025784983666600544932019277 / 250000000000000000000000000000 : ℚ), (34404139116121958625669292877 / 40000000000000000000000000000 : ℚ)⟩
theorem b2422 (b : ℝ) (hb : rootInterval.Contains b) : i2422.Contains (n2422 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2421 b hb) (b2229 b hb))
    (by norm_num [i2422, i2421, i2229, RationalInterval.mul]) (by norm_num [i2422, i2421, i2229, RationalInterval.mul])

def n2423 (b : ℝ) : ℝ := (n2421 b) * (n2230 b)
def i2423 : RationalInterval := ⟨(370736002228751180527744452431 / 1000000000000000000000000000000 : ℚ), (92684037285256737040078339793 / 250000000000000000000000000000 : ℚ)⟩
theorem b2423 (b : ℝ) (hb : rootInterval.Contains b) : i2423.Contains (n2423 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2421 b hb) (b2230 b hb))
    (by norm_num [i2423, i2421, i2230, RationalInterval.mul]) (by norm_num [i2423, i2421, i2230, RationalInterval.mul])

def n2424 (b : ℝ) : ℝ := (n2421 b) * (n2231 b)
def i2424 : RationalInterval := ⟨(370736002228751180527744452431 / 1000000000000000000000000000000 : ℚ), (92684037285256737040078339793 / 250000000000000000000000000000 : ℚ)⟩
theorem b2424 (b : ℝ) (hb : rootInterval.Contains b) : i2424.Contains (n2424 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2421 b hb) (b2231 b hb))
    (by norm_num [i2424, i2421, i2231, RationalInterval.mul]) (by norm_num [i2424, i2421, i2231, RationalInterval.mul])

def n2425 (b : ℝ) : ℝ := (n2421 b) * (n2232 b)
def i2425 : RationalInterval := ⟨(79900407850503232972710988273 / 500000000000000000000000000000 : ℚ), (159800879558134558452239066007 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2425 (b : ℝ) (hb : rootInterval.Contains b) : i2425.Contains (n2425 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2421 b hb) (b2232 b hb))
    (by norm_num [i2425, i2421, i2232, RationalInterval.mul]) (by norm_num [i2425, i2421, i2232, RationalInterval.mul])

def n2426 (b : ℝ) : ℝ := (n2412 b) + (n2422 b)
def i2426 : RationalInterval := ⟨(50810361477611155448703922291 / 62500000000000000000000000000 : ℚ), (812966339440689756687015930437 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2426 (b : ℝ) (hb : rootInterval.Contains b) : i2426.Contains (n2426 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2412 b hb) (b2422 b hb))
    (by norm_num [i2426, i2412, i2422, RationalInterval.add]) (by norm_num [i2426, i2412, i2422, RationalInterval.add])

def n2427 (b : ℝ) : ℝ := (n2413 b) + (n2423 b)
def i2427 : RationalInterval := ⟨(344161134221379938270357409399 / 1000000000000000000000000000000 : ℚ), (86040346250137481020079285561 / 250000000000000000000000000000 : ℚ)⟩
theorem b2427 (b : ℝ) (hb : rootInterval.Contains b) : i2427.Contains (n2427 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2413 b hb) (b2423 b hb))
    (by norm_num [i2427, i2413, i2423, RationalInterval.add]) (by norm_num [i2427, i2413, i2423, RationalInterval.add])

def n2428 (b : ℝ) : ℝ := (n2414 b) + (n2424 b)
def i2428 : RationalInterval := ⟨(344161134221379938270357409399 / 1000000000000000000000000000000 : ℚ), (86040346250137481020079285561 / 250000000000000000000000000000 : ℚ)⟩
theorem b2428 (b : ℝ) (hb : rootInterval.Contains b) : i2428.Contains (n2428 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2414 b hb) (b2424 b hb))
    (by norm_num [i2428, i2414, i2424, RationalInterval.add]) (by norm_num [i2428, i2414, i2424, RationalInterval.add])

def n2429 (b : ℝ) : ℝ := (n2415 b) + (n2425 b)
def i2429 : RationalInterval := ⟨(36686653151426407005280161899 / 250000000000000000000000000000 : ℚ), (36686681451606231276317885049 / 250000000000000000000000000000 : ℚ)⟩
theorem b2429 (b : ℝ) (hb : rootInterval.Contains b) : i2429.Contains (n2429 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2415 b hb) (b2425 b hb))
    (by norm_num [i2429, i2415, i2425, RationalInterval.add]) (by norm_num [i2429, i2415, i2425, RationalInterval.add])

