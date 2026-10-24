import BFGS.Counterexample.Certificates.IntervalTrace26

/-! Generated arithmetic proofs. Each bound is checked by the Lean kernel. -/
namespace BFGS.Counterexample.Trace
noncomputable section
open BFGS RationalInterval
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false

def n2430 (b : ℝ) : ℝ := (n2318 b) * (n2371 b)
def i2430 : RationalInterval := ⟨(-2486224729635500557256804211 / 5000000000000000000000000000 : ℚ), (-31077807554490842630011519493 / 62500000000000000000000000000 : ℚ)⟩
theorem b2430 (b : ℝ) (hb : rootInterval.Contains b) : i2430.Contains (n2430 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2318 b hb) (b2371 b hb))
    (by norm_num [i2430, i2318, i2371, RationalInterval.mul]) (by norm_num [i2430, i2318, i2371, RationalInterval.mul])

def n2431 (b : ℝ) : ℝ := (n2318 b) * (n2372 b)
def i2431 : RationalInterval := ⟨(-58103143616363303207439579611 / 250000000000000000000000000000 : ℚ), (-116206281165685117501106340989 / 500000000000000000000000000000 : ℚ)⟩
theorem b2431 (b : ℝ) (hb : rootInterval.Contains b) : i2431.Contains (n2431 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2318 b hb) (b2372 b hb))
    (by norm_num [i2431, i2318, i2372, RationalInterval.mul]) (by norm_num [i2431, i2318, i2372, RationalInterval.mul])

def n2432 (b : ℝ) : ℝ := (n2318 b) * (n2373 b)
def i2432 : RationalInterval := ⟨(-58103143616363303207439579611 / 250000000000000000000000000000 : ℚ), (-116206281165685117501106340989 / 500000000000000000000000000000 : ℚ)⟩
theorem b2432 (b : ℝ) (hb : rootInterval.Contains b) : i2432.Contains (n2432 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2318 b hb) (b2373 b hb))
    (by norm_num [i2432, i2318, i2373, RationalInterval.mul]) (by norm_num [i2432, i2318, i2373, RationalInterval.mul])

def n2433 (b : ℝ) : ℝ := (n2318 b) * (n2374 b)
def i2433 : RationalInterval := ⟨(-53986124001017556963932324727 / 500000000000000000000000000000 : ℚ), (-107972242144697797029253719083 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2433 (b : ℝ) (hb : rootInterval.Contains b) : i2433.Contains (n2433 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2318 b hb) (b2374 b hb))
    (by norm_num [i2433, i2318, i2374, RationalInterval.mul]) (by norm_num [i2433, i2318, i2374, RationalInterval.mul])

def n2434 (b : ℝ) : ℝ := (n2426 b) + (n2430 b)
def i2434 : RationalInterval := ⟨(39465104714334796965987739307 / 125000000000000000000000000000 : ℚ), (315721418568836274606831618549 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2434 (b : ℝ) (hb : rootInterval.Contains b) : i2434.Contains (n2434 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2426 b hb) (b2430 b hb))
    (by norm_num [i2434, i2426, i2430, RationalInterval.add]) (by norm_num [i2434, i2426, i2430, RationalInterval.add])

def n2435 (b : ℝ) : ℝ := (n2427 b) + (n2431 b)
def i2435 : RationalInterval := ⟨(22349711951185345088119818191 / 200000000000000000000000000000 : ℚ), (55874411334589844539052230133 / 500000000000000000000000000000 : ℚ)⟩
theorem b2435 (b : ℝ) (hb : rootInterval.Contains b) : i2435.Contains (n2435 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2427 b hb) (b2431 b hb))
    (by norm_num [i2435, i2427, i2431, RationalInterval.add]) (by norm_num [i2435, i2427, i2431, RationalInterval.add])

def n2436 (b : ℝ) : ℝ := (n2428 b) + (n2432 b)
def i2436 : RationalInterval := ⟨(22349711951185345088119818191 / 200000000000000000000000000000 : ℚ), (55874411334589844539052230133 / 500000000000000000000000000000 : ℚ)⟩
theorem b2436 (b : ℝ) (hb : rootInterval.Contains b) : i2436.Contains (n2436 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2428 b hb) (b2432 b hb))
    (by norm_num [i2436, i2428, i2432, RationalInterval.add]) (by norm_num [i2436, i2428, i2432, RationalInterval.add])

def n2437 (b : ℝ) : ℝ := (n2429 b) + (n2433 b)
def i2437 : RationalInterval := ⟨(19387182301835257046627999071 / 500000000000000000000000000000 : ℚ), (38774483661727128076017821113 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2437 (b : ℝ) (hb : rootInterval.Contains b) : i2437.Contains (n2437 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2429 b hb) (b2433 b hb))
    (by norm_num [i2437, i2429, i2433, RationalInterval.add]) (by norm_num [i2437, i2429, i2433, RationalInterval.add])

def n2438 (b : ℝ) : ℝ := (n229 b) * (n330 b)
def i2438 : RationalInterval := ⟨(83828020331612932631442196177 / 50000000000000000000000000000 : ℚ), (838280204070847446241209206037 / 500000000000000000000000000000 : ℚ)⟩
theorem b2438 (b : ℝ) (hb : rootInterval.Contains b) : i2438.Contains (n2438 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b229 b hb) (b330 b hb))
    (by norm_num [i2438, i229, i330, RationalInterval.mul]) (by norm_num [i2438, i229, i330, RationalInterval.mul])

def n2439 (b : ℝ) : ℝ := (n231 b) * (n330 b)
def i2439 : RationalInterval := ⟨(-639541143507518673487774838631 / 500000000000000000000000000000 : ℚ), (-639541142795995417547297859577 / 500000000000000000000000000000 : ℚ)⟩
theorem b2439 (b : ℝ) (hb : rootInterval.Contains b) : i2439.Contains (n2439 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b231 b hb) (b330 b hb))
    (by norm_num [i2439, i231, i330, RationalInterval.mul]) (by norm_num [i2439, i231, i330, RationalInterval.mul])

def n2440 (b : ℝ) : ℝ := (n330 b) * (n332 b)
def i2440 : RationalInterval := ⟨(1159823284064082280863623427723 / 500000000000000000000000000000 : ℚ), (2319646569159934875142870553883 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2440 (b : ℝ) (hb : rootInterval.Contains b) : i2440.Contains (n2440 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b330 b hb) (b332 b hb))
    (by norm_num [i2440, i330, i332, RationalInterval.mul]) (by norm_num [i2440, i330, i332, RationalInterval.mul])

def n2441 (b : ℝ) : ℝ := (n318 b) * (n2438 b)
def i2441 : RationalInterval := ⟨(261803692186004848353059524043 / 125000000000000000000000000000 : ℚ), (2094429553747665971196726273299 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2441 (b : ℝ) (hb : rootInterval.Contains b) : i2441.Contains (n2441 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b318 b hb) (b2438 b hb))
    (by norm_num [i2441, i318, i2438, RationalInterval.mul]) (by norm_num [i2441, i318, i2438, RationalInterval.mul])

def n2442 (b : ℝ) : ℝ := (n319 b) * (n2439 b)
def i2442 : RationalInterval := ⟨(-688746281120994871260772501839 / 1000000000000000000000000000000 : ℚ), (-172186568333148684730136340029 / 250000000000000000000000000000 : ℚ)⟩
theorem b2442 (b : ℝ) (hb : rootInterval.Contains b) : i2442.Contains (n2442 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b319 b hb) (b2439 b hb))
    (by norm_num [i2442, i319, i2439, RationalInterval.mul]) (by norm_num [i2442, i319, i2439, RationalInterval.mul])

def n2443 (b : ℝ) : ℝ := (n2441 b) + (n2442 b)
def i2443 : RationalInterval := ⟨(281136651273408783112740738101 / 200000000000000000000000000000 : ℚ), (1405683280415071232276180913183 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2443 (b : ℝ) (hb : rootInterval.Contains b) : i2443.Contains (n2443 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2441 b hb) (b2442 b hb))
    (by norm_num [i2443, i2441, i2442, RationalInterval.add]) (by norm_num [i2443, i2441, i2442, RationalInterval.add])

def n2444 (b : ℝ) : ℝ := (n2440 b) + (n2443 b)
def i2444 : RationalInterval := ⟨(3725329824495208477290950545951 / 1000000000000000000000000000000 : ℚ), (1862664924787503053709525733533 / 500000000000000000000000000000 : ℚ)⟩
theorem b2444 (b : ℝ) (hb : rootInterval.Contains b) : i2444.Contains (n2444 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2440 b hb) (b2443 b hb))
    (by norm_num [i2444, i2440, i2443, RationalInterval.add]) (by norm_num [i2444, i2440, i2443, RationalInterval.add])

def n2445 (b : ℝ) : ℝ := (n118 b) * (n2438 b)
def i2445 : RationalInterval := ⟨(3576722469269319111904424125049 / 1000000000000000000000000000000 : ℚ), (1788361238904841533444964380871 / 500000000000000000000000000000 : ℚ)⟩
theorem b2445 (b : ℝ) (hb : rootInterval.Contains b) : i2445.Contains (n2445 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b118 b hb) (b2438 b hb))
    (by norm_num [i2445, i118, i2438, RationalInterval.mul]) (by norm_num [i2445, i118, i2438, RationalInterval.mul])

def n2446 (b : ℝ) : ℝ := (n119 b) * (n2439 b)
def i2446 : RationalInterval := ⟨(-1352612960599029560067052384239 / 1000000000000000000000000000000 : ℚ), (-676306477102687970552791481607 / 500000000000000000000000000000 : ℚ)⟩
theorem b2446 (b : ℝ) (hb : rootInterval.Contains b) : i2446.Contains (n2446 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b119 b hb) (b2439 b hb))
    (by norm_num [i2446, i119, i2439, RationalInterval.mul]) (by norm_num [i2446, i119, i2439, RationalInterval.mul])

def n2447 (b : ℝ) : ℝ := (n2445 b) + (n2446 b)
def i2447 : RationalInterval := ⟨(222410950867028955183737174081 / 100000000000000000000000000000 : ℚ), (17375855653158649420190201551 / 7812500000000000000000000000 : ℚ)⟩
theorem b2447 (b : ℝ) (hb : rootInterval.Contains b) : i2447.Contains (n2447 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2445 b hb) (b2446 b hb))
    (by norm_num [i2447, i2445, i2446, RationalInterval.add]) (by norm_num [i2447, i2445, i2446, RationalInterval.add])

def n2448 (b : ℝ) : ℝ := (n120 b) * (n2438 b)
def i2448 : RationalInterval := ⟨(1772940921802893218956801517843 / 1000000000000000000000000000000 : ℚ), (1772940926741490341569591637617 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2448 (b : ℝ) (hb : rootInterval.Contains b) : i2448.Contains (n2448 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b120 b hb) (b2438 b hb))
    (by norm_num [i2448, i120, i2438, RationalInterval.mul]) (by norm_num [i2448, i120, i2438, RationalInterval.mul])

def n2449 (b : ℝ) : ℝ := (n121 b) * (n2439 b)
def i2449 : RationalInterval := ⟨(-384719414378728914573930947767 / 500000000000000000000000000000 : ℚ), (-769438824562565034676367408513 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2449 (b : ℝ) (hb : rootInterval.Contains b) : i2449.Contains (n2449 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b121 b hb) (b2439 b hb))
    (by norm_num [i2449, i121, i2439, RationalInterval.mul]) (by norm_num [i2449, i121, i2439, RationalInterval.mul])

def n2450 (b : ℝ) : ℝ := (n2448 b) + (n2449 b)
def i2450 : RationalInterval := ⟨(1003502093045435389808939622309 / 1000000000000000000000000000000 : ℚ), (62718881386182831680826514319 / 62500000000000000000000000000 : ℚ)⟩
theorem b2450 (b : ℝ) (hb : rootInterval.Contains b) : i2450.Contains (n2450 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2448 b hb) (b2449 b hb))
    (by norm_num [i2450, i2448, i2449, RationalInterval.add]) (by norm_num [i2450, i2448, i2449, RationalInterval.add])

def n2451 (b : ℝ) : ℝ := (n332 b) + (n2447 b)
def i2451 : RationalInterval := ⟨(4327121226696132481366904661679 / 1000000000000000000000000000000 : ℚ), (865424248390394500835982775427 / 200000000000000000000000000000 : ℚ)⟩
theorem b2451 (b : ℝ) (hb : rootInterval.Contains b) : i2451.Contains (n2451 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b332 b hb) (b2447 b hb))
    (by norm_num [i2451, i332, i2447, RationalInterval.add]) (by norm_num [i2451, i332, i2447, RationalInterval.add])

def n2452 (b : ℝ) : ℝ := (n2438 b) * (n2210 b)
def i2452 : RationalInterval := ⟨(2835576003378678949364450158697 / 500000000000000000000000000000 : ℚ), (35444700197233431488041593969 / 6250000000000000000000000000 : ℚ)⟩
theorem b2452 (b : ℝ) (hb : rootInterval.Contains b) : i2452.Contains (n2452 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2438 b hb) (b2210 b hb))
    (by norm_num [i2452, i2438, i2210, RationalInterval.mul]) (by norm_num [i2452, i2438, i2210, RationalInterval.mul])

def n2453 (b : ℝ) : ℝ := (n2439 b) * (n2213 b)
def i2453 : RationalInterval := ⟨(-204135924055061233596539256281 / 100000000000000000000000000000 : ℚ), (-40827184574147655480422451779 / 20000000000000000000000000000 : ℚ)⟩
theorem b2453 (b : ℝ) (hb : rootInterval.Contains b) : i2453.Contains (n2453 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2439 b hb) (b2213 b hb))
    (by norm_num [i2453, i2439, i2213, RationalInterval.mul]) (by norm_num [i2453, i2439, i2213, RationalInterval.mul])

def n2454 (b : ℝ) : ℝ := (n2452 b) + (n2453 b)
def i2454 : RationalInterval := ⟨(453724095775843195345438469323 / 125000000000000000000000000000 : ℚ), (362979280284996626406553244609 / 100000000000000000000000000000 : ℚ)⟩
theorem b2454 (b : ℝ) (hb : rootInterval.Contains b) : i2454.Contains (n2454 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2452 b hb) (b2453 b hb))
    (by norm_num [i2454, i2452, i2453, RationalInterval.add]) (by norm_num [i2454, i2452, i2453, RationalInterval.add])

def n2455 (b : ℝ) : ℝ := (n2454 b) * (n13 b)
def i2455 : RationalInterval := ⟨(453724095775843195345438469323 / 62500000000000000000000000000 : ℚ), (362979280284996626406553244609 / 50000000000000000000000000000 : ℚ)⟩
theorem b2455 (b : ℝ) (hb : rootInterval.Contains b) : i2455.Contains (n2455 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2454 b hb) (b13 b hb))
    (by norm_num [i2455, i2454, i13, RationalInterval.mul]) (by norm_num [i2455, i2454, i13, RationalInterval.mul])

def n2456 (b : ℝ) : ℝ := (n332 b) * (n332 b)
def i2456 : RationalInterval := ⟨(884531657230801498251355955263 / 200000000000000000000000000000 : ℚ), (442265828750760025353843863249 / 100000000000000000000000000000 : ℚ)⟩
theorem b2456 (b : ℝ) (hb : rootInterval.Contains b) : i2456.Contains (n2456 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b332 b hb) (b332 b hb))
    (by norm_num [i2456, i332, i332, RationalInterval.mul]) (by norm_num [i2456, i332, i332, RationalInterval.mul])

def n2457 (b : ℝ) : ℝ := (n2455 b) + (n2456 b)
def i2457 : RationalInterval := ⟨(11682243818567498616783795285483 / 1000000000000000000000000000000 : ℚ), (1168224389320753278166950352467 / 100000000000000000000000000000 : ℚ)⟩
theorem b2457 (b : ℝ) (hb : rootInterval.Contains b) : i2457.Contains (n2457 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2455 b hb) (b2456 b hb))
    (by norm_num [i2457, i2455, i2456, RationalInterval.add]) (by norm_num [i2457, i2455, i2456, RationalInterval.add])

def n2458 (b : ℝ) : ℝ := (n330 b) * (n318 b)
def i2458 : RationalInterval := ⟨(344482118462593894358050825353 / 250000000000000000000000000000 : ℚ), (1377928483709071099786321557683 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2458 (b : ℝ) (hb : rootInterval.Contains b) : i2458.Contains (n2458 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b330 b hb) (b318 b hb))
    (by norm_num [i2458, i330, i318, RationalInterval.mul]) (by norm_num [i2458, i330, i318, RationalInterval.mul])

def n2459 (b : ℝ) : ℝ := (n330 b) * (n319 b)
def i2459 : RationalInterval := ⟨(593937715180596411571783638183 / 1000000000000000000000000000000 : ℚ), (593937721409397883143622968433 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2459 (b : ℝ) (hb : rootInterval.Contains b) : i2459.Contains (n2459 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b330 b hb) (b319 b hb))
    (by norm_num [i2459, i330, i319, RationalInterval.mul]) (by norm_num [i2459, i330, i319, RationalInterval.mul])

def n2460 (b : ℝ) : ℝ := (n318 b) * (n330 b)
def i2460 : RationalInterval := ⟨(344482118462593894358050825353 / 250000000000000000000000000000 : ℚ), (1377928483709071099786321557683 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2460 (b : ℝ) (hb : rootInterval.Contains b) : i2460.Contains (n2460 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b318 b hb) (b330 b hb))
    (by norm_num [i2460, i318, i330, RationalInterval.mul]) (by norm_num [i2460, i318, i330, RationalInterval.mul])

def n2461 (b : ℝ) : ℝ := (n319 b) * (n330 b)
def i2461 : RationalInterval := ⟨(593937715180596411571783638183 / 1000000000000000000000000000000 : ℚ), (593937721409397883143622968433 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2461 (b : ℝ) (hb : rootInterval.Contains b) : i2461.Contains (n2461 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b319 b hb) (b330 b hb))
    (by norm_num [i2461, i319, i330, RationalInterval.mul]) (by norm_num [i2461, i319, i330, RationalInterval.mul])

def n2462 (b : ℝ) : ℝ := (n2458 b) + (n2460 b)
def i2462 : RationalInterval := ⟨(344482118462593894358050825353 / 125000000000000000000000000000 : ℚ), (1377928483709071099786321557683 / 500000000000000000000000000000 : ℚ)⟩
theorem b2462 (b : ℝ) (hb : rootInterval.Contains b) : i2462.Contains (n2462 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2458 b hb) (b2460 b hb))
    (by norm_num [i2462, i2458, i2460, RationalInterval.add]) (by norm_num [i2462, i2458, i2460, RationalInterval.add])

def n2463 (b : ℝ) : ℝ := (n2451 b) * (n318 b)
def i2463 : RationalInterval := ⟨(2702810609636365526169983273891 / 500000000000000000000000000000 : ℚ), (1351405318857375612055067793303 / 250000000000000000000000000000 : ℚ)⟩
theorem b2463 (b : ℝ) (hb : rootInterval.Contains b) : i2463.Contains (n2463 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2451 b hb) (b318 b hb))
    (by norm_num [i2463, i2451, i318, RationalInterval.mul]) (by norm_num [i2463, i2451, i318, RationalInterval.mul])

def n2464 (b : ℝ) : ℝ := (n2451 b) * (n319 b)
def i2464 : RationalInterval := ⟨(233002102579035875856934931783 / 100000000000000000000000000000 : ℚ), (466004211552191463560157452129 / 200000000000000000000000000000 : ℚ)⟩
theorem b2464 (b : ℝ) (hb : rootInterval.Contains b) : i2464.Contains (n2464 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2451 b hb) (b319 b hb))
    (by norm_num [i2464, i2451, i319, RationalInterval.mul]) (by norm_num [i2464, i2451, i319, RationalInterval.mul])

def n2465 (b : ℝ) : ℝ := (n2450 b) * (n318 b)
def i2465 : RationalInterval := ⟨(125361687911221016190836045319 / 100000000000000000000000000000 : ℚ), (156702112390708152060854058853 / 125000000000000000000000000000 : ℚ)⟩
theorem b2465 (b : ℝ) (hb : rootInterval.Contains b) : i2465.Contains (n2465 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2450 b hb) (b318 b hb))
    (by norm_num [i2465, i2450, i318, RationalInterval.mul]) (by norm_num [i2465, i2450, i318, RationalInterval.mul])

def n2466 (b : ℝ) : ℝ := (n2450 b) * (n319 b)
def i2466 : RationalInterval := ⟨(270177429025458372825049646813 / 500000000000000000000000000000 : ℚ), (135088717119555793230078351331 / 250000000000000000000000000000 : ℚ)⟩
theorem b2466 (b : ℝ) (hb : rootInterval.Contains b) : i2466.Contains (n2466 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2450 b hb) (b319 b hb))
    (by norm_num [i2466, i2450, i319, RationalInterval.mul]) (by norm_num [i2466, i2450, i319, RationalInterval.mul])

def n2467 (b : ℝ) : ℝ := (n2210 b) * (n330 b)
def i2467 : RationalInterval := ⟨(932764947420591968097793409643 / 250000000000000000000000000000 : ℚ), (186552990186389182503023408809 / 50000000000000000000000000000 : ℚ)⟩
theorem b2467 (b : ℝ) (hb : rootInterval.Contains b) : i2467.Contains (n2467 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2210 b hb) (b330 b hb))
    (by norm_num [i2467, i2210, i330, RationalInterval.mul]) (by norm_num [i2467, i2210, i330, RationalInterval.mul])

def n2468 (b : ℝ) : ℝ := (n2213 b) * (n330 b)
def i2468 : RationalInterval := ⟨(1760358325127084299029975454487 / 1000000000000000000000000000000 : ℚ), (440089583473792760055713432481 / 250000000000000000000000000000 : ℚ)⟩
theorem b2468 (b : ℝ) (hb : rootInterval.Contains b) : i2468.Contains (n2468 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2213 b hb) (b330 b hb))
    (by norm_num [i2468, i2213, i330, RationalInterval.mul]) (by norm_num [i2468, i2213, i330, RationalInterval.mul])

def n2469 (b : ℝ) : ℝ := (n2463 b) + (n2467 b)
def i2469 : RationalInterval := ⟨(4568340504477549462365570093177 / 500000000000000000000000000000 : ℚ), (571042567447330381142546209337 / 62500000000000000000000000000 : ℚ)⟩
theorem b2469 (b : ℝ) (hb : rootInterval.Contains b) : i2469.Contains (n2469 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2463 b hb) (b2467 b hb))
    (by norm_num [i2469, i2463, i2467, RationalInterval.add]) (by norm_num [i2469, i2463, i2467, RationalInterval.add])

def n2470 (b : ℝ) : ℝ := (n2465 b) + (n2468 b)
def i2470 : RationalInterval := ⟨(3013975204239294460938335907677 / 1000000000000000000000000000000 : ℚ), (753493808255209064177421550187 / 250000000000000000000000000000 : ℚ)⟩
theorem b2470 (b : ℝ) (hb : rootInterval.Contains b) : i2470.Contains (n2470 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2465 b hb) (b2468 b hb))
    (by norm_num [i2470, i2465, i2468, RationalInterval.add]) (by norm_num [i2470, i2465, i2468, RationalInterval.add])

def n2471 (b : ℝ) : ℝ := (n330 b) * (n2210 b)
def i2471 : RationalInterval := ⟨(932764947420591968097793409643 / 250000000000000000000000000000 : ℚ), (186552990186389182503023408809 / 50000000000000000000000000000 : ℚ)⟩
theorem b2471 (b : ℝ) (hb : rootInterval.Contains b) : i2471.Contains (n2471 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b330 b hb) (b2210 b hb))
    (by norm_num [i2471, i330, i2210, RationalInterval.mul]) (by norm_num [i2471, i330, i2210, RationalInterval.mul])

def n2472 (b : ℝ) : ℝ := (n330 b) * (n2213 b)
def i2472 : RationalInterval := ⟨(1760358325127084299029975454487 / 1000000000000000000000000000000 : ℚ), (440089583473792760055713432481 / 250000000000000000000000000000 : ℚ)⟩
theorem b2472 (b : ℝ) (hb : rootInterval.Contains b) : i2472.Contains (n2472 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b330 b hb) (b2213 b hb))
    (by norm_num [i2472, i330, i2213, RationalInterval.mul]) (by norm_num [i2472, i330, i2213, RationalInterval.mul])

def n2473 (b : ℝ) : ℝ := (n318 b) * (n2451 b)
def i2473 : RationalInterval := ⟨(2702810609636365526169983273891 / 500000000000000000000000000000 : ℚ), (1351405318857375612055067793303 / 250000000000000000000000000000 : ℚ)⟩
theorem b2473 (b : ℝ) (hb : rootInterval.Contains b) : i2473.Contains (n2473 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b318 b hb) (b2451 b hb))
    (by norm_num [i2473, i318, i2451, RationalInterval.mul]) (by norm_num [i2473, i318, i2451, RationalInterval.mul])

def n2474 (b : ℝ) : ℝ := (n318 b) * (n2450 b)
def i2474 : RationalInterval := ⟨(125361687911221016190836045319 / 100000000000000000000000000000 : ℚ), (156702112390708152060854058853 / 125000000000000000000000000000 : ℚ)⟩
theorem b2474 (b : ℝ) (hb : rootInterval.Contains b) : i2474.Contains (n2474 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b318 b hb) (b2450 b hb))
    (by norm_num [i2474, i318, i2450, RationalInterval.mul]) (by norm_num [i2474, i318, i2450, RationalInterval.mul])

def n2475 (b : ℝ) : ℝ := (n319 b) * (n2451 b)
def i2475 : RationalInterval := ⟨(233002102579035875856934931783 / 100000000000000000000000000000 : ℚ), (466004211552191463560157452129 / 200000000000000000000000000000 : ℚ)⟩
theorem b2475 (b : ℝ) (hb : rootInterval.Contains b) : i2475.Contains (n2475 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b319 b hb) (b2451 b hb))
    (by norm_num [i2475, i319, i2451, RationalInterval.mul]) (by norm_num [i2475, i319, i2451, RationalInterval.mul])

def n2476 (b : ℝ) : ℝ := (n319 b) * (n2450 b)
def i2476 : RationalInterval := ⟨(270177429025458372825049646813 / 500000000000000000000000000000 : ℚ), (135088717119555793230078351331 / 250000000000000000000000000000 : ℚ)⟩
theorem b2476 (b : ℝ) (hb : rootInterval.Contains b) : i2476.Contains (n2476 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b319 b hb) (b2450 b hb))
    (by norm_num [i2476, i319, i2450, RationalInterval.mul]) (by norm_num [i2476, i319, i2450, RationalInterval.mul])

def n2477 (b : ℝ) : ℝ := (n2471 b) + (n2473 b)
def i2477 : RationalInterval := ⟨(4568340504477549462365570093177 / 500000000000000000000000000000 : ℚ), (571042567447330381142546209337 / 62500000000000000000000000000 : ℚ)⟩
theorem b2477 (b : ℝ) (hb : rootInterval.Contains b) : i2477.Contains (n2477 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2471 b hb) (b2473 b hb))
    (by norm_num [i2477, i2471, i2473, RationalInterval.add]) (by norm_num [i2477, i2471, i2473, RationalInterval.add])

def n2478 (b : ℝ) : ℝ := (n2472 b) + (n2474 b)
def i2478 : RationalInterval := ⟨(3013975204239294460938335907677 / 1000000000000000000000000000000 : ℚ), (753493808255209064177421550187 / 250000000000000000000000000000 : ℚ)⟩
theorem b2478 (b : ℝ) (hb : rootInterval.Contains b) : i2478.Contains (n2478 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2472 b hb) (b2474 b hb))
    (by norm_num [i2478, i2472, i2474, RationalInterval.add]) (by norm_num [i2478, i2472, i2474, RationalInterval.add])

def n2479 (b : ℝ) : ℝ := (n2469 b) + (n2477 b)
def i2479 : RationalInterval := ⟨(4568340504477549462365570093177 / 250000000000000000000000000000 : ℚ), (571042567447330381142546209337 / 31250000000000000000000000000 : ℚ)⟩
theorem b2479 (b : ℝ) (hb : rootInterval.Contains b) : i2479.Contains (n2479 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2469 b hb) (b2477 b hb))
    (by norm_num [i2479, i2469, i2477, RationalInterval.add]) (by norm_num [i2479, i2469, i2477, RationalInterval.add])

def n2480 (b : ℝ) : ℝ := (n2464 b) + (n2478 b)
def i2480 : RationalInterval := ⟨(5343996230029653219507685225507 / 1000000000000000000000000000000 : ℚ), (5343996290781793574510473461393 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2480 (b : ℝ) (hb : rootInterval.Contains b) : i2480.Contains (n2480 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2464 b hb) (b2478 b hb))
    (by norm_num [i2480, i2464, i2478, RationalInterval.add]) (by norm_num [i2480, i2464, i2478, RationalInterval.add])

def n2481 (b : ℝ) : ℝ := (n2470 b) + (n2475 b)
def i2481 : RationalInterval := ⟨(5343996230029653219507685225507 / 1000000000000000000000000000000 : ℚ), (5343996290781793574510473461393 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2481 (b : ℝ) (hb : rootInterval.Contains b) : i2481.Contains (n2481 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2470 b hb) (b2475 b hb))
    (by norm_num [i2481, i2470, i2475, RationalInterval.add]) (by norm_num [i2481, i2470, i2475, RationalInterval.add])

def n2482 (b : ℝ) : ℝ := (n2466 b) + (n2476 b)
def i2482 : RationalInterval := ⟨(270177429025458372825049646813 / 250000000000000000000000000000 : ℚ), (135088717119555793230078351331 / 125000000000000000000000000000 : ℚ)⟩
theorem b2482 (b : ℝ) (hb : rootInterval.Contains b) : i2482.Contains (n2482 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2466 b hb) (b2476 b hb))
    (by norm_num [i2482, i2466, i2476, RationalInterval.add]) (by norm_num [i2482, i2466, i2476, RationalInterval.add])

def n2483 (b : ℝ) : ℝ := (n2284 b) * (n2479 b)
def i2483 : RationalInterval := ⟨(-8848771395895386975349510168069 / 1000000000000000000000000000000 : ℚ), (-4424385611750676766266677767963 / 500000000000000000000000000000 : ℚ)⟩
theorem b2483 (b : ℝ) (hb : rootInterval.Contains b) : i2483.Contains (n2483 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2284 b hb) (b2479 b hb))
    (by norm_num [i2483, i2284, i2479, RationalInterval.mul]) (by norm_num [i2483, i2284, i2479, RationalInterval.mul])

def n2484 (b : ℝ) : ℝ := (n2284 b) * (n2480 b)
def i2484 : RationalInterval := ⟨(-2587799722238008303426281578607 / 1000000000000000000000000000000 : ℚ), (-517559932457290686704473480371 / 200000000000000000000000000000 : ℚ)⟩
theorem b2484 (b : ℝ) (hb : rootInterval.Contains b) : i2484.Contains (n2484 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2284 b hb) (b2480 b hb))
    (by norm_num [i2484, i2284, i2480, RationalInterval.mul]) (by norm_num [i2484, i2284, i2480, RationalInterval.mul])

def n2485 (b : ℝ) : ℝ := (n2284 b) * (n2481 b)
def i2485 : RationalInterval := ⟨(-2587799722238008303426281578607 / 1000000000000000000000000000000 : ℚ), (-517559932457290686704473480371 / 200000000000000000000000000000 : ℚ)⟩
theorem b2485 (b : ℝ) (hb : rootInterval.Contains b) : i2485.Contains (n2485 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2284 b hb) (b2481 b hb))
    (by norm_num [i2485, i2284, i2481, RationalInterval.mul]) (by norm_num [i2485, i2284, i2481, RationalInterval.mul])

def n2486 (b : ℝ) : ℝ := (n2284 b) * (n2482 b)
def i2486 : RationalInterval := ⟨(-130831881467617409862271817521 / 250000000000000000000000000000 : ℚ), (-65415938699644613373651093783 / 125000000000000000000000000000 : ℚ)⟩
theorem b2486 (b : ℝ) (hb : rootInterval.Contains b) : i2486.Contains (n2486 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2284 b hb) (b2482 b hb))
    (by norm_num [i2486, i2284, i2482, RationalInterval.mul]) (by norm_num [i2486, i2284, i2482, RationalInterval.mul])

def n2487 (b : ℝ) : ℝ := (n2483 b) + (n15 b)
def i2487 : RationalInterval := ⟨(-7848771395895386975349510168069 / 1000000000000000000000000000000 : ℚ), (-3924385611750676766266677767963 / 500000000000000000000000000000 : ℚ)⟩
theorem b2487 (b : ℝ) (hb : rootInterval.Contains b) : i2487.Contains (n2487 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2483 b hb) (b15 b hb))
    (by norm_num [i2487, i2483, i15, RationalInterval.add]) (by norm_num [i2487, i2483, i15, RationalInterval.add])

def n2488 (b : ℝ) : ℝ := (n2444 b) * (n2290 b)
def i2488 : RationalInterval := ⟨(873562025988817287784795810477 / 1000000000000000000000000000000 : ℚ), (436781026241819557980430079581 / 500000000000000000000000000000 : ℚ)⟩
theorem b2488 (b : ℝ) (hb : rootInterval.Contains b) : i2488.Contains (n2488 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2444 b hb) (b2290 b hb))
    (by norm_num [i2488, i2444, i2290, RationalInterval.mul]) (by norm_num [i2488, i2444, i2290, RationalInterval.mul])

def n2489 (b : ℝ) : ℝ := (n2488 b) * (n2225 b)
def i2489 : RationalInterval := ⟨(3691410791694153625040786349467 / 500000000000000000000000000000 : ℚ), (7382821883612858792666232883291 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2489 (b : ℝ) (hb : rootInterval.Contains b) : i2489.Contains (n2489 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2488 b hb) (b2225 b hb))
    (by norm_num [i2489, i2488, i2225, RationalInterval.mul]) (by norm_num [i2489, i2488, i2225, RationalInterval.mul])

def n2490 (b : ℝ) : ℝ := (n2488 b) * (n2226 b)
def i2490 : RationalInterval := ⟨(166639245526913745729882389161 / 50000000000000000000000000000 : ℚ), (833196263372009131700400709969 / 250000000000000000000000000000 : ℚ)⟩
theorem b2490 (b : ℝ) (hb : rootInterval.Contains b) : i2490.Contains (n2490 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2488 b hb) (b2226 b hb))
    (by norm_num [i2490, i2488, i2226, RationalInterval.mul]) (by norm_num [i2490, i2488, i2226, RationalInterval.mul])

def n2491 (b : ℝ) : ℝ := (n2488 b) * (n2227 b)
def i2491 : RationalInterval := ⟨(166639245526913745729882389161 / 50000000000000000000000000000 : ℚ), (833196263372009131700400709969 / 250000000000000000000000000000 : ℚ)⟩
theorem b2491 (b : ℝ) (hb : rootInterval.Contains b) : i2491.Contains (n2491 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2488 b hb) (b2227 b hb))
    (by norm_num [i2491, i2488, i2227, RationalInterval.mul]) (by norm_num [i2491, i2488, i2227, RationalInterval.mul])

def n2492 (b : ℝ) : ℝ := (n2488 b) * (n2228 b)
def i2492 : RationalInterval := ⟨(187678915597869266659850177529 / 125000000000000000000000000000 : ℚ), (750715696334528211613322778703 / 500000000000000000000000000000 : ℚ)⟩
theorem b2492 (b : ℝ) (hb : rootInterval.Contains b) : i2492.Contains (n2492 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2488 b hb) (b2228 b hb))
    (by norm_num [i2492, i2488, i2228, RationalInterval.mul]) (by norm_num [i2492, i2488, i2228, RationalInterval.mul])

def n2493 (b : ℝ) : ℝ := (n2487 b) + (n2489 b)
def i2493 : RationalInterval := ⟨(-93189962501415945053587493827 / 200000000000000000000000000000 : ℚ), (-93189867977698947973424530527 / 200000000000000000000000000000 : ℚ)⟩
theorem b2493 (b : ℝ) (hb : rootInterval.Contains b) : i2493.Contains (n2493 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2487 b hb) (b2489 b hb))
    (by norm_num [i2493, i2487, i2489, RationalInterval.add]) (by norm_num [i2493, i2487, i2489, RationalInterval.add])

def n2494 (b : ℝ) : ℝ := (n2484 b) + (n2490 b)
def i2494 : RationalInterval := ⟨(744985188300266611171366204613 / 1000000000000000000000000000000 : ℚ), (744985391201583093279235438021 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2494 (b : ℝ) (hb : rootInterval.Contains b) : i2494.Contains (n2494 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2484 b hb) (b2490 b hb))
    (by norm_num [i2494, i2484, i2490, RationalInterval.add]) (by norm_num [i2494, i2484, i2490, RationalInterval.add])

def n2495 (b : ℝ) : ℝ := (n2485 b) + (n2491 b)
def i2495 : RationalInterval := ⟨(744985188300266611171366204613 / 1000000000000000000000000000000 : ℚ), (744985391201583093279235438021 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2495 (b : ℝ) (hb : rootInterval.Contains b) : i2495.Contains (n2495 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2485 b hb) (b2491 b hb))
    (by norm_num [i2495, i2485, i2491, RationalInterval.add]) (by norm_num [i2495, i2485, i2491, RationalInterval.add])

def n2496 (b : ℝ) : ℝ := (n2486 b) + (n2492 b)
def i2496 : RationalInterval := ⟨(244525949728121123457428537537 / 250000000000000000000000000000 : ℚ), (489051941535949758118718403571 / 500000000000000000000000000000 : ℚ)⟩
theorem b2496 (b : ℝ) (hb : rootInterval.Contains b) : i2496.Contains (n2496 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2486 b hb) (b2492 b hb))
    (by norm_num [i2496, i2486, i2492, RationalInterval.add]) (by norm_num [i2496, i2486, i2492, RationalInterval.add])

def n2497 (b : ℝ) : ℝ := (n2444 b) + (n2457 b)
def i2497 : RationalInterval := ⟨(7703786821531353547037372915717 / 500000000000000000000000000000 : ℚ), (1925946717847817361136069373967 / 125000000000000000000000000000 : ℚ)⟩
theorem b2497 (b : ℝ) (hb : rootInterval.Contains b) : i2497.Contains (n2497 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2444 b hb) (b2457 b hb))
    (by norm_num [i2497, i2444, i2457, RationalInterval.add]) (by norm_num [i2497, i2444, i2457, RationalInterval.add])

def n2498 (b : ℝ) : ℝ := (n2497 b) * (n2290 b)
def i2498 : RationalInterval := ⟨(3612960967564678077991364589089 / 1000000000000000000000000000000 : ℚ), (3612961076204735695364750227857 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2498 (b : ℝ) (hb : rootInterval.Contains b) : i2498.Contains (n2498 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2497 b hb) (b2290 b hb))
    (by norm_num [i2498, i2497, i2290, RationalInterval.mul]) (by norm_num [i2498, i2497, i2290, RationalInterval.mul])

def n2499 (b : ℝ) : ℝ := (n2303 b) * (n2444 b)
def i2499 : RationalInterval := ⟨(11195000483825384702126442892397 / 200000000000000000000000000000 : ℚ), (5597500323233689138007496765231 / 100000000000000000000000000000 : ℚ)⟩
theorem b2499 (b : ℝ) (hb : rootInterval.Contains b) : i2499.Contains (n2499 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2303 b hb) (b2444 b hb))
    (by norm_num [i2499, i2303, i2444, RationalInterval.mul]) (by norm_num [i2499, i2303, i2444, RationalInterval.mul])

def n2500 (b : ℝ) : ℝ := (n2499 b) * (n2306 b)
def i2500 : RationalInterval := ⟨(3178027505372773693798344081389 / 500000000000000000000000000000 : ℚ), (6356055328066503005687956856997 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2500 (b : ℝ) (hb : rootInterval.Contains b) : i2500.Contains (n2500 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2499 b hb) (b2306 b hb))
    (by norm_num [i2500, i2499, i2306, RationalInterval.mul]) (by norm_num [i2500, i2499, i2306, RationalInterval.mul])

def n2501 (b : ℝ) : ℝ := -(n2500 b)
def i2501 : RationalInterval := ⟨(-6356055328066503005687956856997 / 1000000000000000000000000000000 : ℚ), (-3178027505372773693798344081389 / 500000000000000000000000000000 : ℚ)⟩
theorem b2501 (b : ℝ) (hb : rootInterval.Contains b) : i2501.Contains (n2501 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b2500 b hb))
    (by norm_num [i2501, i2500, RationalInterval.neg]) (by norm_num [i2501, i2500, RationalInterval.neg])

def n2502 (b : ℝ) : ℝ := (n2498 b) + (n2501 b)
def i2502 : RationalInterval := ⟨(-685773590125456231924148066977 / 250000000000000000000000000000 : ℚ), (-2743093934540811692231937934921 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2502 (b : ℝ) (hb : rootInterval.Contains b) : i2502.Contains (n2502 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2498 b hb) (b2501 b hb))
    (by norm_num [i2502, i2498, i2501, RationalInterval.add]) (by norm_num [i2502, i2498, i2501, RationalInterval.add])

def n2503 (b : ℝ) : ℝ := (n2502 b) * (n2229 b)
def i2503 : RationalInterval := ⟨(-4280887845128447095980106417439 / 1000000000000000000000000000000 : ℚ), (-4280887121612320254990105669 / 1000000000000000000000000000 : ℚ)⟩
theorem b2503 (b : ℝ) (hb : rootInterval.Contains b) : i2503.Contains (n2503 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2502 b hb) (b2229 b hb))
    (by norm_num [i2503, i2502, i2229, RationalInterval.mul]) (by norm_num [i2503, i2502, i2229, RationalInterval.mul])

def n2504 (b : ℝ) : ℝ := (n2502 b) * (n2230 b)
def i2504 : RationalInterval := ⟨(-922609846013461529502847462871 / 500000000000000000000000000000 : ℚ), (-461304843503900069625835123813 / 250000000000000000000000000000 : ℚ)⟩
theorem b2504 (b : ℝ) (hb : rootInterval.Contains b) : i2504.Contains (n2504 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2502 b hb) (b2230 b hb))
    (by norm_num [i2504, i2502, i2230, RationalInterval.mul]) (by norm_num [i2504, i2502, i2230, RationalInterval.mul])

def n2505 (b : ℝ) : ℝ := (n2502 b) * (n2231 b)
def i2505 : RationalInterval := ⟨(-922609846013461529502847462871 / 500000000000000000000000000000 : ℚ), (-461304843503900069625835123813 / 250000000000000000000000000000 : ℚ)⟩
theorem b2505 (b : ℝ) (hb : rootInterval.Contains b) : i2505.Contains (n2505 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2502 b hb) (b2231 b hb))
    (by norm_num [i2505, i2502, i2231, RationalInterval.mul]) (by norm_num [i2505, i2502, i2231, RationalInterval.mul])

def n2506 (b : ℝ) : ℝ := (n2502 b) * (n2232 b)
def i2506 : RationalInterval := ⟨(-795357373288477600007721499873 / 1000000000000000000000000000000 : ℚ), (-397678616781672249587544128701 / 500000000000000000000000000000 : ℚ)⟩
theorem b2506 (b : ℝ) (hb : rootInterval.Contains b) : i2506.Contains (n2506 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2502 b hb) (b2232 b hb))
    (by norm_num [i2506, i2502, i2232, RationalInterval.mul]) (by norm_num [i2506, i2502, i2232, RationalInterval.mul])

def n2507 (b : ℝ) : ℝ := (n2493 b) + (n2503 b)
def i2507 : RationalInterval := ⟨(-2373418828817763410624021943287 / 500000000000000000000000000000 : ℚ), (-949367292300162998971445664327 / 200000000000000000000000000000 : ℚ)⟩
theorem b2507 (b : ℝ) (hb : rootInterval.Contains b) : i2507.Contains (n2507 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2493 b hb) (b2503 b hb))
    (by norm_num [i2507, i2493, i2503, RationalInterval.add]) (by norm_num [i2507, i2493, i2503, RationalInterval.add])

def n2508 (b : ℝ) : ℝ := (n2494 b) + (n2504 b)
def i2508 : RationalInterval := ⟨(-1100234503726656447834328721129 / 1000000000000000000000000000000 : ℚ), (-1100233982814017185224105057231 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2508 (b : ℝ) (hb : rootInterval.Contains b) : i2508.Contains (n2508 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2494 b hb) (b2504 b hb))
    (by norm_num [i2508, i2494, i2504, RationalInterval.add]) (by norm_num [i2508, i2494, i2504, RationalInterval.add])

def n2509 (b : ℝ) : ℝ := (n2495 b) + (n2505 b)
def i2509 : RationalInterval := ⟨(-1100234503726656447834328721129 / 1000000000000000000000000000000 : ℚ), (-1100233982814017185224105057231 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2509 (b : ℝ) (hb : rootInterval.Contains b) : i2509.Contains (n2509 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2495 b hb) (b2505 b hb))
    (by norm_num [i2509, i2495, i2505, RationalInterval.add]) (by norm_num [i2509, i2495, i2505, RationalInterval.add])

def n2510 (b : ℝ) : ℝ := (n2496 b) + (n2506 b)
def i2510 : RationalInterval := ⟨(7309857024960275752879706011 / 40000000000000000000000000000 : ℚ), (9137332475427750853117427487 / 50000000000000000000000000000 : ℚ)⟩
theorem b2510 (b : ℝ) (hb : rootInterval.Contains b) : i2510.Contains (n2510 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2496 b hb) (b2506 b hb))
    (by norm_num [i2510, i2496, i2506, RationalInterval.add]) (by norm_num [i2510, i2496, i2506, RationalInterval.add])

def n2511 (b : ℝ) : ℝ := (n2318 b) * (n2462 b)
def i2511 : RationalInterval := ⟨(606869200292264123716742425267 / 125000000000000000000000000000 : ℚ), (1213738447371695792457175589279 / 250000000000000000000000000000 : ℚ)⟩
theorem b2511 (b : ℝ) (hb : rootInterval.Contains b) : i2511.Contains (n2511 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2318 b hb) (b2462 b hb))
    (by norm_num [i2511, i2318, i2462, RationalInterval.mul]) (by norm_num [i2511, i2318, i2462, RationalInterval.mul])

def n2512 (b : ℝ) : ℝ := (n2318 b) * (n2459 b)
def i2512 : RationalInterval := ⟨(523165771047419800809085238933 / 500000000000000000000000000000 : ℚ), (523165792957894495993277539073 / 500000000000000000000000000000 : ℚ)⟩
theorem b2512 (b : ℝ) (hb : rootInterval.Contains b) : i2512.Contains (n2512 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2318 b hb) (b2459 b hb))
    (by norm_num [i2512, i2318, i2459, RationalInterval.mul]) (by norm_num [i2512, i2318, i2459, RationalInterval.mul])

def n2513 (b : ℝ) : ℝ := (n2318 b) * (n2461 b)
def i2513 : RationalInterval := ⟨(523165771047419800809085238933 / 500000000000000000000000000000 : ℚ), (523165792957894495993277539073 / 500000000000000000000000000000 : ℚ)⟩
theorem b2513 (b : ℝ) (hb : rootInterval.Contains b) : i2513.Contains (n2513 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2318 b hb) (b2461 b hb))
    (by norm_num [i2513, i2318, i2461, RationalInterval.mul]) (by norm_num [i2513, i2318, i2461, RationalInterval.mul])

def n2514 (b : ℝ) : ℝ := (n2507 b) + (n2511 b)
def i2514 : RationalInterval := ⟨(54057972351293084242947757781 / 500000000000000000000000000000 : ℚ), (108117327985968174971474035481 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2514 (b : ℝ) (hb : rootInterval.Contains b) : i2514.Contains (n2514 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2507 b hb) (b2511 b hb))
    (by norm_num [i2514, i2507, i2511, RationalInterval.add]) (by norm_num [i2514, i2507, i2511, RationalInterval.add])

def n2515 (b : ℝ) : ℝ := (n2508 b) + (n2512 b)
def i2515 : RationalInterval := ⟨(-53902961631816846216158243263 / 1000000000000000000000000000000 : ℚ), (-10780479379645638647509995817 / 200000000000000000000000000000 : ℚ)⟩
theorem b2515 (b : ℝ) (hb : rootInterval.Contains b) : i2515.Contains (n2515 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2508 b hb) (b2512 b hb))
    (by norm_num [i2515, i2508, i2512, RationalInterval.add]) (by norm_num [i2515, i2508, i2512, RationalInterval.add])

def n2516 (b : ℝ) : ℝ := (n2509 b) + (n2513 b)
def i2516 : RationalInterval := ⟨(-53902961631816846216158243263 / 1000000000000000000000000000000 : ℚ), (-10780479379645638647509995817 / 200000000000000000000000000000 : ℚ)⟩
theorem b2516 (b : ℝ) (hb : rootInterval.Contains b) : i2516.Contains (n2516 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2509 b hb) (b2513 b hb))
    (by norm_num [i2516, i2509, i2513, RationalInterval.add]) (by norm_num [i2516, i2509, i2513, RationalInterval.add])

def n2517 (b : ℝ) : ℝ := (n229 b) * (n331 b)
def i2517 : RationalInterval := ⟨(-198335107260793418608787405711 / 125000000000000000000000000000 : ℚ), (-793340428275113097142080692411 / 500000000000000000000000000000 : ℚ)⟩
theorem b2517 (b : ℝ) (hb : rootInterval.Contains b) : i2517.Contains (n2517 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b229 b hb) (b331 b hb))
    (by norm_num [i2517, i229, i331, RationalInterval.mul]) (by norm_num [i2517, i229, i331, RationalInterval.mul])

def n2518 (b : ℝ) : ℝ := (n230 b) * (n330 b)
def i2518 : RationalInterval := ⟨(-639541143507518673487774838631 / 500000000000000000000000000000 : ℚ), (-639541142795995417547297859577 / 500000000000000000000000000000 : ℚ)⟩
theorem b2518 (b : ℝ) (hb : rootInterval.Contains b) : i2518.Contains (n2518 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b230 b hb) (b330 b hb))
    (by norm_num [i2518, i230, i330, RationalInterval.mul]) (by norm_num [i2518, i230, i330, RationalInterval.mul])

def n2519 (b : ℝ) : ℝ := (n2517 b) + (n2518 b)
def i2519 : RationalInterval := ⟨(-57315262902027693916916978459 / 20000000000000000000000000000 : ℚ), (-358220392767777128672344637997 / 125000000000000000000000000000 : ℚ)⟩
theorem b2519 (b : ℝ) (hb : rootInterval.Contains b) : i2519.Contains (n2519 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2517 b hb) (b2518 b hb))
    (by norm_num [i2519, i2517, i2518, RationalInterval.add]) (by norm_num [i2519, i2517, i2518, RationalInterval.add])

