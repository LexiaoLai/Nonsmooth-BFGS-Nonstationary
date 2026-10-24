import BFGS.Counterexample.Certificates.IntervalTrace4

/-! Generated arithmetic proofs. Each bound is checked by the Lean kernel. -/
namespace BFGS.Counterexample.Trace
noncomputable section
open BFGS RationalInterval
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false

def n450 (b : ℝ) : ℝ := (n430 b) + (n449 b)
def i450 : RationalInterval := ⟨(31785466930824525674825661777 / 250000000000000000000000000000 : ℚ), (127141867759219642357357882659 / 1000000000000000000000000000000 : ℚ)⟩
theorem b450 (b : ℝ) (hb : rootInterval.Contains b) : i450.Contains (n450 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b430 b hb) (b449 b hb))
    (by norm_num [i450, i430, i449, RationalInterval.add]) (by norm_num [i450, i430, i449, RationalInterval.add])

def n451 (b : ℝ) : ℝ := -(n433 b)
def i451 : RationalInterval := ⟨(-271439137249573411878118854547 / 62500000000000000000000000000 : ℚ), (-135719568324427222618913612827 / 31250000000000000000000000000 : ℚ)⟩
theorem b451 (b : ℝ) (hb : rootInterval.Contains b) : i451.Contains (n451 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b433 b hb))
    (by norm_num [i451, i433, RationalInterval.neg]) (by norm_num [i451, i433, RationalInterval.neg])

def n452 (b : ℝ) : ℝ := ((2256 : ℚ) : ℝ)
def i452 : RationalInterval := ⟨(2256 : ℚ), (2256 : ℚ)⟩
theorem b452 (b : ℝ) (hb : rootInterval.Contains b) : i452.Contains (n452 b) := by
  exact RationalInterval.contains_point (2256 : ℚ)

def n453 (b : ℝ) : ℝ := ((1 / 2256 : ℚ) : ℝ)
def i453 : RationalInterval := ⟨(1 / 2256 : ℚ), (1 / 2256 : ℚ)⟩
theorem b453 (b : ℝ) (hb : rootInterval.Contains b) : i453.Contains (n453 b) := by
  exact RationalInterval.contains_point (1 / 2256 : ℚ)

def n454 (b : ℝ) : ℝ := (n451 b) * (n453 b)
def i454 : RationalInterval := ⟨(-1925100264181371715447651451 / 1000000000000000000000000000000 : ℚ), (-240637532490119189040626973 / 125000000000000000000000000000 : ℚ)⟩
theorem b454 (b : ℝ) (hb : rootInterval.Contains b) : i454.Contains (n454 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b451 b hb) (b453 b hb))
    (by norm_num [i454, i451, i453, RationalInterval.mul]) (by norm_num [i454, i451, i453, RationalInterval.mul])

def n455 (b : ℝ) : ℝ := (n450 b) + (n454 b)
def i455 : RationalInterval := ⟨(125216767459116730983854995657 / 1000000000000000000000000000000 : ℚ), (200346827998877902152052587 / 1600000000000000000000000000 : ℚ)⟩
theorem b455 (b : ℝ) (hb : rootInterval.Contains b) : i455.Contains (n455 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b450 b hb) (b454 b hb))
    (by norm_num [i455, i450, i454, RationalInterval.add]) (by norm_num [i455, i450, i454, RationalInterval.add])

def n456 (b : ℝ) : ℝ := -(n455 b)
def i456 : RationalInterval := ⟨(-200346827998877902152052587 / 1600000000000000000000000000 : ℚ), (-125216767459116730983854995657 / 1000000000000000000000000000000 : ℚ)⟩
theorem b456 (b : ℝ) (hb : rootInterval.Contains b) : i456.Contains (n456 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b455 b hb))
    (by norm_num [i456, i455, RationalInterval.neg]) (by norm_num [i456, i455, RationalInterval.neg])

def n457 (b : ℝ) : ℝ := (n384 b) + (n456 b)
def i457 : RationalInterval := ⟨(1944917280395557572475756019361 / 1000000000000000000000000000000 : ℚ), (1944917281164941412597271804327 / 1000000000000000000000000000000 : ℚ)⟩
theorem b457 (b : ℝ) (hb : rootInterval.Contains b) : i457.Contains (n457 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b384 b hb) (b456 b hb))
    (by norm_num [i457, i384, i456, RationalInterval.add]) (by norm_num [i457, i384, i456, RationalInterval.add])

def n458 (b : ℝ) : ℝ := (n388 b) * (n415 b)
def i458 : RationalInterval := ⟨(8423707648748781822399913979 / 250000000000000000000000000000 : ℚ), (33694830690505624419914974797 / 1000000000000000000000000000000 : ℚ)⟩
theorem b458 (b : ℝ) (hb : rootInterval.Contains b) : i458.Contains (n458 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b388 b hb) (b415 b hb))
    (by norm_num [i458, i388, i415, RationalInterval.mul]) (by norm_num [i458, i388, i415, RationalInterval.mul])

def n459 (b : ℝ) : ℝ := (n388 b) * (n241 b)
def i459 : RationalInterval := ⟨(168474152974975636447998279581 / 1000000000000000000000000000000 : ℚ), (33694830690505624419914974797 / 200000000000000000000000000000 : ℚ)⟩
theorem b459 (b : ℝ) (hb : rootInterval.Contains b) : i459.Contains (n459 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b388 b hb) (b241 b hb))
    (by norm_num [i459, i388, i241, RationalInterval.mul]) (by norm_num [i459, i388, i241, RationalInterval.mul])

def n460 (b : ℝ) : ℝ := (n388 b) * (n388 b)
def i460 : RationalInterval := ⟨(5676708044127098418610219233393 / 500000000000000000000000000000 : ℚ), (5676708076309198672718923680069 / 500000000000000000000000000000 : ℚ)⟩
theorem b460 (b : ℝ) (hb : rootInterval.Contains b) : i460.Contains (n460 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b388 b hb) (b388 b hb))
    (by norm_num [i460, i388, i388, RationalInterval.mul]) (by norm_num [i460, i388, i388, RationalInterval.mul])

def n461 (b : ℝ) : ℝ := (n460 b) * (n254 b)
def i461 : RationalInterval := ⟨(4270677641699358446136739657763 / 500000000000000000000000000000 : ℚ), (1067669418255584969303928164061 / 125000000000000000000000000000 : ℚ)⟩
theorem b461 (b : ℝ) (hb : rootInterval.Contains b) : i461.Contains (n461 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b460 b hb) (b254 b hb))
    (by norm_num [i461, i460, i254, RationalInterval.mul]) (by norm_num [i461, i460, i254, RationalInterval.mul])

def n462 (b : ℝ) : ℝ := (n460 b) * (n266 b)
def i462 : RationalInterval := ⟨(192426958374276289861694414423 / 1000000000000000000000000000000 : ℚ), (192426960958614970939043432919 / 1000000000000000000000000000000 : ℚ)⟩
theorem b462 (b : ℝ) (hb : rootInterval.Contains b) : i462.Contains (n462 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b460 b hb) (b266 b hb))
    (by norm_num [i462, i460, i266, RationalInterval.mul]) (by norm_num [i462, i460, i266, RationalInterval.mul])

def n463 (b : ℝ) : ℝ := -(n458 b)
def i463 : RationalInterval := ⟨(-33694830690505624419914974797 / 1000000000000000000000000000000 : ℚ), (-8423707648748781822399913979 / 250000000000000000000000000000 : ℚ)⟩
theorem b463 (b : ℝ) (hb : rootInterval.Contains b) : i463.Contains (n463 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b458 b hb))
    (by norm_num [i463, i458, RationalInterval.neg]) (by norm_num [i463, i458, RationalInterval.neg])

def n464 (b : ℝ) : ℝ := (n459 b) + (n463 b)
def i464 : RationalInterval := ⟨(8423707642779375751755206549 / 62500000000000000000000000000 : ℚ), (134779322857532994809975218069 / 1000000000000000000000000000000 : ℚ)⟩
theorem b464 (b : ℝ) (hb : rootInterval.Contains b) : i464.Contains (n464 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b459 b hb) (b463 b hb))
    (by norm_num [i464, i459, i463, RationalInterval.add]) (by norm_num [i464, i459, i463, RationalInterval.add])

def n465 (b : ℝ) : ℝ := (n464 b) * (n13 b)
def i465 : RationalInterval := ⟨(8423707642779375751755206549 / 31250000000000000000000000000 : ℚ), (134779322857532994809975218069 / 500000000000000000000000000000 : ℚ)⟩
theorem b465 (b : ℝ) (hb : rootInterval.Contains b) : i465.Contains (n465 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b464 b hb) (b13 b hb))
    (by norm_num [i465, i464, i13, RationalInterval.mul]) (by norm_num [i465, i464, i13, RationalInterval.mul])

def n466 (b : ℝ) : ℝ := (n461 b) + (n465 b)
def i466 : RationalInterval := ⟨(4405456963983828458164822962547 / 500000000000000000000000000000 : ℚ), (4405456995879872872025687874313 / 500000000000000000000000000000 : ℚ)⟩
theorem b466 (b : ℝ) (hb : rootInterval.Contains b) : i466.Contains (n466 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b461 b hb) (b465 b hb))
    (by norm_num [i466, i461, i465, RationalInterval.add]) (by norm_num [i466, i461, i465, RationalInterval.add])

def n467 (b : ℝ) : ℝ := (n388 b) + (n463 b)
def i467 : RationalInterval := ⟨(1667894114404503552270025308413 / 500000000000000000000000000000 : ℚ), (1667894119227783657350948911891 / 500000000000000000000000000000 : ℚ)⟩
theorem b467 (b : ℝ) (hb : rootInterval.Contains b) : i467.Contains (n467 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b388 b hb) (b463 b hb))
    (by norm_num [i467, i388, i463, RationalInterval.add]) (by norm_num [i467, i388, i463, RationalInterval.add])

def n468 (b : ℝ) : ℝ := (n467 b) * (n13 b)
def i468 : RationalInterval := ⟨(1667894114404503552270025308413 / 250000000000000000000000000000 : ℚ), (1667894119227783657350948911891 / 250000000000000000000000000000 : ℚ)⟩
theorem b468 (b : ℝ) (hb : rootInterval.Contains b) : i468.Contains (n468 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b467 b hb) (b13 b hb))
    (by norm_num [i468, i467, i13, RationalInterval.mul]) (by norm_num [i468, i467, i13, RationalInterval.mul])

def n469 (b : ℝ) : ℝ := -(n468 b)
def i469 : RationalInterval := ⟨(-1667894119227783657350948911891 / 250000000000000000000000000000 : ℚ), (-1667894114404503552270025308413 / 250000000000000000000000000000 : ℚ)⟩
theorem b469 (b : ℝ) (hb : rootInterval.Contains b) : i469.Contains (n469 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b468 b hb))
    (by norm_num [i469, i468, RationalInterval.neg]) (by norm_num [i469, i468, RationalInterval.neg])

def n470 (b : ℝ) : ℝ := (n462 b) + (n469 b)
def i470 : RationalInterval := ⟨(-6479149518536858339542101233141 / 1000000000000000000000000000000 : ℚ), (-6479149496659399238141057800733 / 1000000000000000000000000000000 : ℚ)⟩
theorem b470 (b : ℝ) (hb : rootInterval.Contains b) : i470.Contains (n470 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b462 b hb) (b469 b hb))
    (by norm_num [i470, i462, i469, RationalInterval.add]) (by norm_num [i470, i462, i469, RationalInterval.add])

def n471 (b : ℝ) : ℝ := (n459 b) + (n388 b)
def i471 : RationalInterval := ⟨(884489303118622091351990967801 / 250000000000000000000000000000 : ℚ), (3537957222503090564091072353683 / 1000000000000000000000000000000 : ℚ)⟩
theorem b471 (b : ℝ) (hb : rootInterval.Contains b) : i471.Contains (n471 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b459 b hb) (b388 b hb))
    (by norm_num [i471, i459, i388, RationalInterval.add]) (by norm_num [i471, i459, i388, RationalInterval.add])

def n472 (b : ℝ) : ℝ := (n471 b) * (n64 b)
def i472 : RationalInterval := ⟨(884489303118622091351990967801 / 500000000000000000000000000000 : ℚ), (884489305625772641022768088421 / 500000000000000000000000000000 : ℚ)⟩
theorem b472 (b : ℝ) (hb : rootInterval.Contains b) : i472.Contains (n472 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b471 b hb) (b64 b hb))
    (by norm_num [i472, i471, i64, RationalInterval.mul]) (by norm_num [i472, i471, i64, RationalInterval.mul])

def n473 (b : ℝ) : ℝ := -(n462 b)
def i473 : RationalInterval := ⟨(-192426960958614970939043432919 / 1000000000000000000000000000000 : ℚ), (-192426958374276289861694414423 / 1000000000000000000000000000000 : ℚ)⟩
theorem b473 (b : ℝ) (hb : rootInterval.Contains b) : i473.Contains (n473 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b462 b hb))
    (by norm_num [i473, i462, RationalInterval.neg]) (by norm_num [i473, i462, RationalInterval.neg])

def n474 (b : ℝ) : ℝ := (n461 b) + (n473 b)
def i474 : RationalInterval := ⟨(8348928322440101921334435882607 / 1000000000000000000000000000000 : ℚ), (1669785677534080692913946179613 / 200000000000000000000000000000 : ℚ)⟩
theorem b474 (b : ℝ) (hb : rootInterval.Contains b) : i474.Contains (n474 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b461 b hb) (b473 b hb))
    (by norm_num [i474, i461, i473, RationalInterval.add]) (by norm_num [i474, i461, i473, RationalInterval.add])

def n475 (b : ℝ) : ℝ := ((12 : ℚ) : ℝ)
def i475 : RationalInterval := ⟨(12 : ℚ), (12 : ℚ)⟩
theorem b475 (b : ℝ) (hb : rootInterval.Contains b) : i475.Contains (n475 b) := by
  exact RationalInterval.contains_point (12 : ℚ)

def n476 (b : ℝ) : ℝ := ((1 / 12 : ℚ) : ℝ)
def i476 : RationalInterval := ⟨(1 / 12 : ℚ), (1 / 12 : ℚ)⟩
theorem b476 (b : ℝ) (hb : rootInterval.Contains b) : i476.Contains (n476 b) := by
  exact RationalInterval.contains_point (1 / 12 : ℚ)

def n477 (b : ℝ) : ℝ := (n474 b) * (n476 b)
def i477 : RationalInterval := ⟨(13914880537400169868890726471 / 20000000000000000000000000000 : ℚ), (695744032305866955380810908173 / 1000000000000000000000000000000 : ℚ)⟩
theorem b477 (b : ℝ) (hb : rootInterval.Contains b) : i477.Contains (n477 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b474 b hb) (b476 b hb))
    (by norm_num [i477, i474, i476, RationalInterval.mul]) (by norm_num [i477, i474, i476, RationalInterval.mul])

def n478 (b : ℝ) : ℝ := (n472 b) + (n477 b)
def i478 : RationalInterval := ⟨(154045164569203292259282391197 / 62500000000000000000000000000 : ℚ), (492944528711482447485269417003 / 200000000000000000000000000000 : ℚ)⟩
theorem b478 (b : ℝ) (hb : rootInterval.Contains b) : i478.Contains (n478 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b472 b hb) (b477 b hb))
    (by norm_num [i478, i472, i477, RationalInterval.add]) (by norm_num [i478, i472, i477, RationalInterval.add])

def n479 (b : ℝ) : ℝ := -(n478 b)
def i479 : RationalInterval := ⟨(-492944528711482447485269417003 / 200000000000000000000000000000 : ℚ), (-154045164569203292259282391197 / 62500000000000000000000000000 : ℚ)⟩
theorem b479 (b : ℝ) (hb : rootInterval.Contains b) : i479.Contains (n479 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b478 b hb))
    (by norm_num [i479, i478, RationalInterval.neg]) (by norm_num [i479, i478, RationalInterval.neg])

def n480 (b : ℝ) : ℝ := (n390 b) + (n479 b)
def i480 : RationalInterval := ⟨(61865366641811933370440156579 / 50000000000000000000000000000 : ℚ), (247461470581709056124963610913 / 200000000000000000000000000000 : ℚ)⟩
theorem b480 (b : ℝ) (hb : rootInterval.Contains b) : i480.Contains (n480 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b390 b hb) (b479 b hb))
    (by norm_num [i480, i390, i479, RationalInterval.add]) (by norm_num [i480, i390, i479, RationalInterval.add])

def n481 (b : ℝ) : ℝ := (n394 b) * (n415 b)
def i481 : RationalInterval := ⟨(3069589915223364454764687 / 250000000000000000000000000 : ℚ), (2455671949964581903167445967 / 200000000000000000000000000000 : ℚ)⟩
theorem b481 (b : ℝ) (hb : rootInterval.Contains b) : i481.Contains (n481 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b394 b hb) (b415 b hb))
    (by norm_num [i481, i394, i415, RationalInterval.mul]) (by norm_num [i481, i394, i415, RationalInterval.mul])

def n482 (b : ℝ) : ℝ := (n394 b) * (n394 b)
def i482 : RationalInterval := ⟨(12060649276980456679014663049 / 8000000000000000000000000000 : ℚ), (753790590730356505771635108677 / 500000000000000000000000000000 : ℚ)⟩
theorem b482 (b : ℝ) (hb : rootInterval.Contains b) : i482.Contains (n482 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b394 b hb) (b394 b hb))
    (by norm_num [i482, i394, i394, RationalInterval.mul]) (by norm_num [i482, i394, i394, RationalInterval.mul])

def n483 (b : ℝ) : ℝ := (n482 b) * (n266 b)
def i483 : RationalInterval := ⟨(511034308605422100275951301 / 20000000000000000000000000000 : ℚ), (5110343199742197582628378131 / 200000000000000000000000000000 : ℚ)⟩
theorem b483 (b : ℝ) (hb : rootInterval.Contains b) : i483.Contains (n483 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b482 b hb) (b266 b hb))
    (by norm_num [i483, i482, i266, RationalInterval.mul]) (by norm_num [i483, i482, i266, RationalInterval.mul])

def n484 (b : ℝ) : ℝ := -(n481 b)
def i484 : RationalInterval := ⟨(-2455671949964581903167445967 / 200000000000000000000000000000 : ℚ), (-3069589915223364454764687 / 250000000000000000000000000 : ℚ)⟩
theorem b484 (b : ℝ) (hb : rootInterval.Contains b) : i484.Contains (n484 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b481 b hb))
    (by norm_num [i484, i481, RationalInterval.neg]) (by norm_num [i484, i481, RationalInterval.neg])

def n485 (b : ℝ) : ℝ := (n394 b) + (n484 b)
def i485 : RationalInterval := ⟨(303889401584880718097509392553 / 250000000000000000000000000000 : ℚ), (1215557615321397493764664235421 / 1000000000000000000000000000000 : ℚ)⟩
theorem b485 (b : ℝ) (hb : rootInterval.Contains b) : i485.Contains (n485 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b394 b hb) (b484 b hb))
    (by norm_num [i485, i394, i484, RationalInterval.add]) (by norm_num [i485, i394, i484, RationalInterval.add])

def n486 (b : ℝ) : ℝ := (n485 b) * (n418 b)
def i486 : RationalInterval := ⟨(911668204754642154292528177659 / 250000000000000000000000000000 : ℚ), (3646672845964192481293992706263 / 1000000000000000000000000000000 : ℚ)⟩
theorem b486 (b : ℝ) (hb : rootInterval.Contains b) : i486.Contains (n486 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b485 b hb) (b418 b hb))
    (by norm_num [i486, i485, i418, RationalInterval.mul]) (by norm_num [i486, i485, i418, RationalInterval.mul])

def n487 (b : ℝ) : ℝ := (n483 b) + (n486 b)
def i487 : RationalInterval := ⟨(1836112267224419861091955137843 / 500000000000000000000000000000 : ℚ), (1836112280981451734603567298459 / 500000000000000000000000000000 : ℚ)⟩
theorem b487 (b : ℝ) (hb : rootInterval.Contains b) : i487.Contains (n487 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b483 b hb) (b486 b hb))
    (by norm_num [i487, i483, i486, RationalInterval.add]) (by norm_num [i487, i483, i486, RationalInterval.add])

def n488 (b : ℝ) : ℝ := -(n486 b)
def i488 : RationalInterval := ⟨(-3646672845964192481293992706263 / 1000000000000000000000000000000 : ℚ), (-911668204754642154292528177659 / 250000000000000000000000000000 : ℚ)⟩
theorem b488 (b : ℝ) (hb : rootInterval.Contains b) : i488.Contains (n488 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b486 b hb))
    (by norm_num [i488, i486, RationalInterval.neg]) (by norm_num [i488, i486, RationalInterval.neg])

def n489 (b : ℝ) : ℝ := (n394 b) + (n394 b)
def i489 : RationalInterval := ⟨(1227835966089345781905874800047 / 500000000000000000000000000000 : ℚ), (1227835974982290951583722983421 / 500000000000000000000000000000 : ℚ)⟩
theorem b489 (b : ℝ) (hb : rootInterval.Contains b) : i489.Contains (n489 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b394 b hb) (b394 b hb))
    (by norm_num [i489, i394, i394, RationalInterval.add]) (by norm_num [i489, i394, i394, RationalInterval.add])

def n490 (b : ℝ) : ℝ := (n481 b) * (n13 b)
def i490 : RationalInterval := ⟨(3069589915223364454764687 / 125000000000000000000000000 : ℚ), (2455671949964581903167445967 / 100000000000000000000000000000 : ℚ)⟩
theorem b490 (b : ℝ) (hb : rootInterval.Contains b) : i490.Contains (n490 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b481 b hb) (b13 b hb))
    (by norm_num [i490, i481, i13, RationalInterval.mul]) (by norm_num [i490, i481, i13, RationalInterval.mul])

def n491 (b : ℝ) : ℝ := -(n490 b)
def i491 : RationalInterval := ⟨(-2455671949964581903167445967 / 100000000000000000000000000000 : ℚ), (-3069589915223364454764687 / 125000000000000000000000000 : ℚ)⟩
theorem b491 (b : ℝ) (hb : rootInterval.Contains b) : i491.Contains (n491 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b490 b hb))
    (by norm_num [i491, i490, RationalInterval.neg]) (by norm_num [i491, i490, RationalInterval.neg])

def n492 (b : ℝ) : ℝ := (n489 b) + (n491 b)
def i492 : RationalInterval := ⟨(303889401584880718097509392553 / 125000000000000000000000000000 : ℚ), (1215557615321397493764664235421 / 500000000000000000000000000000 : ℚ)⟩
theorem b492 (b : ℝ) (hb : rootInterval.Contains b) : i492.Contains (n492 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b489 b hb) (b491 b hb))
    (by norm_num [i492, i489, i491, RationalInterval.add]) (by norm_num [i492, i489, i491, RationalInterval.add])

def n493 (b : ℝ) : ℝ := (n492 b) * (n13 b)
def i493 : RationalInterval := ⟨(303889401584880718097509392553 / 62500000000000000000000000000 : ℚ), (1215557615321397493764664235421 / 250000000000000000000000000000 : ℚ)⟩
theorem b493 (b : ℝ) (hb : rootInterval.Contains b) : i493.Contains (n493 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b492 b hb) (b13 b hb))
    (by norm_num [i493, i492, i13, RationalInterval.mul]) (by norm_num [i493, i492, i13, RationalInterval.mul])

def n494 (b : ℝ) : ℝ := (n493 b) * (n221 b)
def i494 : RationalInterval := ⟨(972446085071618297912030056169 / 1000000000000000000000000000000 : ℚ), (972446092257117995011731388337 / 1000000000000000000000000000000 : ℚ)⟩
theorem b494 (b : ℝ) (hb : rootInterval.Contains b) : i494.Contains (n494 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b493 b hb) (b221 b hb))
    (by norm_num [i494, i493, i221, RationalInterval.mul]) (by norm_num [i494, i493, i221, RationalInterval.mul])

def n495 (b : ℝ) : ℝ := (n481 b) + (n494 b)
def i495 : RationalInterval := ⟨(984724444732511755731088804169 / 1000000000000000000000000000000 : ℚ), (246181113001735226131892154543 / 250000000000000000000000000000 : ℚ)⟩
theorem b495 (b : ℝ) (hb : rootInterval.Contains b) : i495.Contains (n495 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b481 b hb) (b494 b hb))
    (by norm_num [i495, i481, i494, RationalInterval.add]) (by norm_num [i495, i481, i494, RationalInterval.add])

def n496 (b : ℝ) : ℝ := (n483 b) * (n241 b)
def i496 : RationalInterval := ⟨(319396442878388812672469563 / 250000000000000000000000000000 : ℚ), (1277585799935549395657094533 / 1000000000000000000000000000000 : ℚ)⟩
theorem b496 (b : ℝ) (hb : rootInterval.Contains b) : i496.Contains (n496 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b483 b hb) (b241 b hb))
    (by norm_num [i496, i483, i241, RationalInterval.mul]) (by norm_num [i496, i483, i241, RationalInterval.mul])

def n497 (b : ℝ) : ℝ := (n495 b) + (n496 b)
def i497 : RationalInterval := ⟨(986002030504025310981778682421 / 1000000000000000000000000000000 : ℚ), (197200407561375290784645142541 / 200000000000000000000000000000 : ℚ)⟩
theorem b497 (b : ℝ) (hb : rootInterval.Contains b) : i497.Contains (n497 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b495 b hb) (b496 b hb))
    (by norm_num [i497, i495, i496, RationalInterval.add]) (by norm_num [i497, i495, i496, RationalInterval.add])

def n498 (b : ℝ) : ℝ := -(n497 b)
def i498 : RationalInterval := ⟨(-197200407561375290784645142541 / 200000000000000000000000000000 : ℚ), (-986002030504025310981778682421 / 1000000000000000000000000000000 : ℚ)⟩
theorem b498 (b : ℝ) (hb : rootInterval.Contains b) : i498.Contains (n498 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b497 b hb))
    (by norm_num [i498, i497, RationalInterval.neg]) (by norm_num [i498, i497, RationalInterval.neg])

def n499 (b : ℝ) : ℝ := (n394 b) + (n498 b)
def i499 : RationalInterval := ⟨(120916964141234663991324543671 / 500000000000000000000000000000 : ℚ), (241833944478265640601944301 / 1000000000000000000000000000 : ℚ)⟩
theorem b499 (b : ℝ) (hb : rootInterval.Contains b) : i499.Contains (n499 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b394 b hb) (b498 b hb))
    (by norm_num [i499, i394, i498, RationalInterval.add]) (by norm_num [i499, i394, i498, RationalInterval.add])

def n500 (b : ℝ) : ℝ := ((-6 : ℚ) : ℝ)
def i500 : RationalInterval := ⟨(-6 : ℚ), (-6 : ℚ)⟩
theorem b500 (b : ℝ) (hb : rootInterval.Contains b) : i500.Contains (n500 b) := by
  exact RationalInterval.contains_point (-6 : ℚ)

def n501 (b : ℝ) : ℝ := (n397 b) * (n415 b)
def i501 : RationalInterval := ⟨(12790509714706554561260521603 / 1000000000000000000000000000000 : ℚ), (6395254866580676458085338551 / 500000000000000000000000000000 : ℚ)⟩
theorem b501 (b : ℝ) (hb : rootInterval.Contains b) : i501.Contains (n501 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b397 b hb) (b415 b hb))
    (by norm_num [i501, i397, i415, RationalInterval.mul]) (by norm_num [i501, i397, i415, RationalInterval.mul])

def n502 (b : ℝ) : ℝ := (n397 b) * (n275 b)
def i502 : RationalInterval := ⟨(37239929989313350280406012137 / 1000000000000000000000000000000 : ℚ), (37239930785428008237233078701 / 1000000000000000000000000000000 : ℚ)⟩
theorem b502 (b : ℝ) (hb : rootInterval.Contains b) : i502.Contains (n502 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b397 b hb) (b275 b hb))
    (by norm_num [i502, i397, i275, RationalInterval.mul]) (by norm_num [i502, i397, i275, RationalInterval.mul])

def n503 (b : ℝ) : ℝ := (n397 b) * (n397 b)
def i503 : RationalInterval := ⟨(817985693810013738775233193243 / 500000000000000000000000000000 : ℚ), (1635971392340953033784839918837 / 1000000000000000000000000000000 : ℚ)⟩
theorem b503 (b : ℝ) (hb : rootInterval.Contains b) : i503.Contains (n503 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b397 b hb) (b397 b hb))
    (by norm_num [i503, i397, i397, RationalInterval.mul]) (by norm_num [i503, i397, i397, RationalInterval.mul])

def n504 (b : ℝ) : ℝ := (n503 b) * (n282 b)
def i504 : RationalInterval := ⟨(-7117976929832740815237486795643 / 1000000000000000000000000000000 : ℚ), (-3558988424536589188398457637897 / 500000000000000000000000000000 : ℚ)⟩
theorem b504 (b : ℝ) (hb : rootInterval.Contains b) : i504.Contains (n504 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b503 b hb) (b282 b hb))
    (by norm_num [i504, i503, i282, RationalInterval.mul]) (by norm_num [i504, i503, i282, RationalInterval.mul])

def n505 (b : ℝ) : ℝ := -(n501 b)
def i505 : RationalInterval := ⟨(-6395254866580676458085338551 / 500000000000000000000000000000 : ℚ), (-12790509714706554561260521603 / 1000000000000000000000000000000 : ℚ)⟩
theorem b505 (b : ℝ) (hb : rootInterval.Contains b) : i505.Contains (n505 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b501 b hb))
    (by norm_num [i505, i501, RationalInterval.neg]) (by norm_num [i505, i501, RationalInterval.neg])

def n506 (b : ℝ) : ℝ := (n397 b) + (n505 b)
def i506 : RationalInterval := ⟨(1266260461737494103209881483217 / 1000000000000000000000000000000 : ℚ), (1266260463601428737055807188579 / 1000000000000000000000000000000 : ℚ)⟩
theorem b506 (b : ℝ) (hb : rootInterval.Contains b) : i506.Contains (n506 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b397 b hb) (b505 b hb))
    (by norm_num [i506, i397, i505, RationalInterval.add]) (by norm_num [i506, i397, i505, RationalInterval.add])

def n507 (b : ℝ) : ℝ := (n506 b) * (n13 b)
def i507 : RationalInterval := ⟨(1266260461737494103209881483217 / 500000000000000000000000000000 : ℚ), (1266260463601428737055807188579 / 500000000000000000000000000000 : ℚ)⟩
theorem b507 (b : ℝ) (hb : rootInterval.Contains b) : i507.Contains (n507 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b506 b hb) (b13 b hb))
    (by norm_num [i507, i506, i13, RationalInterval.mul]) (by norm_num [i507, i506, i13, RationalInterval.mul])

def n508 (b : ℝ) : ℝ := (n502 b) + (n505 b)
def i508 : RationalInterval := ⟨(4889884051230399472847067007 / 200000000000000000000000000000 : ℚ), (12224710535360726837986278549 / 500000000000000000000000000000 : ℚ)⟩
theorem b508 (b : ℝ) (hb : rootInterval.Contains b) : i508.Contains (n508 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b502 b hb) (b505 b hb))
    (by norm_num [i508, i502, i505, RationalInterval.add]) (by norm_num [i508, i502, i505, RationalInterval.add])

def n509 (b : ℝ) : ℝ := (n508 b) * (n13 b)
def i509 : RationalInterval := ⟨(4889884051230399472847067007 / 100000000000000000000000000000 : ℚ), (12224710535360726837986278549 / 250000000000000000000000000000 : ℚ)⟩
theorem b509 (b : ℝ) (hb : rootInterval.Contains b) : i509.Contains (n509 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b508 b hb) (b13 b hb))
    (by norm_num [i509, i508, i13, RationalInterval.mul]) (by norm_num [i509, i508, i13, RationalInterval.mul])

def n510 (b : ℝ) : ℝ := -(n509 b)
def i510 : RationalInterval := ⟨(-12224710535360726837986278549 / 250000000000000000000000000000 : ℚ), (-4889884051230399472847067007 / 100000000000000000000000000000 : ℚ)⟩
theorem b510 (b : ℝ) (hb : rootInterval.Contains b) : i510.Contains (n510 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b509 b hb))
    (by norm_num [i510, i509, RationalInterval.neg]) (by norm_num [i510, i509, RationalInterval.neg])

def n511 (b : ℝ) : ℝ := (n504 b) + (n510 b)
def i511 : RationalInterval := ⟨(-7166875771974183722589431909839 / 1000000000000000000000000000000 : ℚ), (-895859461198185296440673243233 / 125000000000000000000000000000 : ℚ)⟩
theorem b511 (b : ℝ) (hb : rootInterval.Contains b) : i511.Contains (n511 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b504 b hb) (b510 b hb))
    (by norm_num [i511, i504, i510, RationalInterval.add]) (by norm_num [i511, i504, i510, RationalInterval.add])

def n512 (b : ℝ) : ℝ := (n397 b) + (n502 b)
def i512 : RationalInterval := ⟨(164536362682496100800807271557 / 125000000000000000000000000000 : ℚ), (1316290904101563299854300788883 / 1000000000000000000000000000000 : ℚ)⟩
theorem b512 (b : ℝ) (hb : rootInterval.Contains b) : i512.Contains (n512 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b397 b hb) (b502 b hb))
    (by norm_num [i512, i397, i502, RationalInterval.add]) (by norm_num [i512, i397, i502, RationalInterval.add])

def n513 (b : ℝ) : ℝ := (n512 b) * (n64 b)
def i513 : RationalInterval := ⟨(164536362682496100800807271557 / 250000000000000000000000000000 : ℚ), (329072726025390824963575197221 / 500000000000000000000000000000 : ℚ)⟩
theorem b513 (b : ℝ) (hb : rootInterval.Contains b) : i513.Contains (n513 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b512 b hb) (b64 b hb))
    (by norm_num [i513, i512, i64, RationalInterval.mul]) (by norm_num [i513, i512, i64, RationalInterval.mul])

def n514 (b : ℝ) : ℝ := -(n504 b)
def i514 : RationalInterval := ⟨(3558988424536589188398457637897 / 500000000000000000000000000000 : ℚ), (7117976929832740815237486795643 / 1000000000000000000000000000000 : ℚ)⟩
theorem b514 (b : ℝ) (hb : rootInterval.Contains b) : i514.Contains (n514 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b504 b hb))
    (by norm_num [i514, i504, RationalInterval.neg]) (by norm_num [i514, i504, RationalInterval.neg])

def n515 (b : ℝ) : ℝ := (n514 b) * (n476 b)
def i515 : RationalInterval := ⟨(296582368711382432366538136491 / 500000000000000000000000000000 : ℚ), (18536398254772762539680955197 / 31250000000000000000000000000 : ℚ)⟩
theorem b515 (b : ℝ) (hb : rootInterval.Contains b) : i515.Contains (n515 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b514 b hb) (b476 b hb))
    (by norm_num [i515, i514, i476, RationalInterval.mul]) (by norm_num [i515, i514, i476, RationalInterval.mul])

def n516 (b : ℝ) : ℝ := (n513 b) + (n515 b)
def i516 : RationalInterval := ⟨(125131018815274926793630535921 / 100000000000000000000000000000 : ℚ), (625655098101755025598470480373 / 500000000000000000000000000000 : ℚ)⟩
theorem b516 (b : ℝ) (hb : rootInterval.Contains b) : i516.Contains (n516 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b513 b hb) (b515 b hb))
    (by norm_num [i516, i513, i515, RationalInterval.add]) (by norm_num [i516, i513, i515, RationalInterval.add])

def n517 (b : ℝ) : ℝ := -(n516 b)
def i517 : RationalInterval := ⟨(-625655098101755025598470480373 / 500000000000000000000000000000 : ℚ), (-125131018815274926793630535921 / 100000000000000000000000000000 : ℚ)⟩
theorem b517 (b : ℝ) (hb : rootInterval.Contains b) : i517.Contains (n517 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b516 b hb))
    (by norm_num [i517, i516, RationalInterval.neg]) (by norm_num [i517, i516, RationalInterval.neg])

def n518 (b : ℝ) : ℝ := (n398 b) + (n517 b)
def i518 : RationalInterval := ⟨(800694271127436992880774009837 / 1000000000000000000000000000000 : ℚ), (800694283118244484795617473421 / 1000000000000000000000000000000 : ℚ)⟩
theorem b518 (b : ℝ) (hb : rootInterval.Contains b) : i518.Contains (n518 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b398 b hb) (b517 b hb))
    (by norm_num [i518, i398, i517, RationalInterval.add]) (by norm_num [i518, i398, i517, RationalInterval.add])

def n519 (b : ℝ) : ℝ := (n402 b) * (n415 b)
def i519 : RationalInterval := ⟨(3813649356250403316761466883 / 125000000000000000000000000000 : ℚ), (1525459753598286256571197991 / 50000000000000000000000000000 : ℚ)⟩
theorem b519 (b : ℝ) (hb : rootInterval.Contains b) : i519.Contains (n519 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b402 b hb) (b415 b hb))
    (by norm_num [i519, i402, i415, RationalInterval.mul]) (by norm_num [i519, i402, i415, RationalInterval.mul])

def n520 (b : ℝ) : ℝ := (n402 b) * (n275 b)
def i520 : RationalInterval := ⟨(17765676358278046322287413367 / 200000000000000000000000000000 : ℚ), (11103548026055750996373849789 / 125000000000000000000000000000 : ℚ)⟩
theorem b520 (b : ℝ) (hb : rootInterval.Contains b) : i520.Contains (n520 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b402 b hb) (b275 b hb))
    (by norm_num [i520, i402, i275, RationalInterval.mul]) (by norm_num [i520, i402, i275, RationalInterval.mul])

def n521 (b : ℝ) : ℝ := (n402 b) * (n291 b)
def i521 : RationalInterval := ⟨(3016533289378532103215731468901 / 1000000000000000000000000000000 : ℚ), (754133328129727239256280253973 / 250000000000000000000000000000 : ℚ)⟩
theorem b521 (b : ℝ) (hb : rootInterval.Contains b) : i521.Contains (n521 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b402 b hb) (b291 b hb))
    (by norm_num [i521, i402, i291, RationalInterval.mul]) (by norm_num [i521, i402, i291, RationalInterval.mul])

def n522 (b : ℝ) : ℝ := (n402 b) * (n402 b)
def i522 : RationalInterval := ⟨(9308109703954634004145898361271 / 1000000000000000000000000000000 : ℚ), (1163513729924072109851367536621 / 125000000000000000000000000000 : ℚ)⟩
theorem b522 (b : ℝ) (hb : rootInterval.Contains b) : i522.Contains (n522 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b402 b hb) (b402 b hb))
    (by norm_num [i522, i402, i402, RationalInterval.mul]) (by norm_num [i522, i402, i402, RationalInterval.mul])

def n523 (b : ℝ) : ℝ := (n522 b) * (n282 b)
def i523 : RationalInterval := ⟨(-79099257995853251340495758199 / 1953125000000000000000000000 : ℚ), (-1619952766478845519275386509899 / 40000000000000000000000000000 : ℚ)⟩
theorem b523 (b : ℝ) (hb : rootInterval.Contains b) : i523.Contains (n523 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b522 b hb) (b282 b hb))
    (by norm_num [i523, i522, i282, RationalInterval.mul]) (by norm_num [i523, i522, i282, RationalInterval.mul])

def n524 (b : ℝ) : ℝ := (n522 b) * (n298 b)
def i524 : RationalInterval := ⟨(39259293981468396646584424181 / 1000000000000000000000000000000 : ℚ), (19629647619641848830409252509 / 500000000000000000000000000000 : ℚ)⟩
theorem b524 (b : ℝ) (hb : rootInterval.Contains b) : i524.Contains (n524 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b522 b hb) (b298 b hb))
    (by norm_num [i524, i522, i298, RationalInterval.mul]) (by norm_num [i524, i522, i298, RationalInterval.mul])

def n525 (b : ℝ) : ℝ := -(n519 b)
def i525 : RationalInterval := ⟨(-1525459753598286256571197991 / 50000000000000000000000000000 : ℚ), (-3813649356250403316761466883 / 125000000000000000000000000000 : ℚ)⟩
theorem b525 (b : ℝ) (hb : rootInterval.Contains b) : i525.Contains (n525 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b519 b hb))
    (by norm_num [i525, i519, RationalInterval.neg]) (by norm_num [i525, i519, RationalInterval.neg])

def n526 (b : ℝ) : ℝ := (n520 b) + (n525 b)
def i526 : RationalInterval := ⟨(11663837343884901296002621403 / 200000000000000000000000000000 : ℚ), (3644949334902673839806191453 / 62500000000000000000000000000 : ℚ)⟩
theorem b526 (b : ℝ) (hb : rootInterval.Contains b) : i526.Contains (n526 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b520 b hb) (b525 b hb))
    (by norm_num [i526, i520, i525, RationalInterval.add]) (by norm_num [i526, i520, i525, RationalInterval.add])

def n527 (b : ℝ) : ℝ := ((695 : ℚ) : ℝ)
def i527 : RationalInterval := ⟨(695 : ℚ), (695 : ℚ)⟩
theorem b527 (b : ℝ) (hb : rootInterval.Contains b) : i527.Contains (n527 b) := by
  exact RationalInterval.contains_point (695 : ℚ)

def n528 (b : ℝ) : ℝ := (n526 b) * (n527 b)
def i528 : RationalInterval := ⟨(1621273390800001280144364375017 / 40000000000000000000000000000 : ℚ), (506647957551471663733060611967 / 12500000000000000000000000000 : ℚ)⟩
theorem b528 (b : ℝ) (hb : rootInterval.Contains b) : i528.Contains (n528 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b526 b hb) (b527 b hb))
    (by norm_num [i528, i526, i527, RationalInterval.mul]) (by norm_num [i528, i526, i527, RationalInterval.mul])

def n529 (b : ℝ) : ℝ := (n523 b) + (n528 b)
def i529 : RationalInterval := ⟨(33014676123167317275281177537 / 1000000000000000000000000000000 : ℚ), (6603488429319023352037241977 / 200000000000000000000000000000 : ℚ)⟩
theorem b529 (b : ℝ) (hb : rootInterval.Contains b) : i529.Contains (n529 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b523 b hb) (b528 b hb))
    (by norm_num [i529, i523, i528, RationalInterval.add]) (by norm_num [i529, i523, i528, RationalInterval.add])

def n530 (b : ℝ) : ℝ := (n521 b) + (n525 b)
def i530 : RationalInterval := ⟨(2986024094306566378084307509081 / 1000000000000000000000000000000 : ℚ), (746506029417226432622757320207 / 250000000000000000000000000000 : ℚ)⟩
theorem b530 (b : ℝ) (hb : rootInterval.Contains b) : i530.Contains (n530 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b521 b hb) (b525 b hb))
    (by norm_num [i530, i521, i525, RationalInterval.add]) (by norm_num [i530, i521, i525, RationalInterval.add])

def n531 (b : ℝ) : ℝ := (n530 b) * (n527 b)
def i531 : RationalInterval := ⟨(415057349108612726553718743762259 / 200000000000000000000000000000 : ℚ), (103764338088994474134563267508773 / 50000000000000000000000000000 : ℚ)⟩
theorem b531 (b : ℝ) (hb : rootInterval.Contains b) : i531.Contains (n531 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b530 b hb) (b527 b hb))
    (by norm_num [i531, i530, i527, RationalInterval.mul]) (by norm_num [i531, i530, i527, RationalInterval.mul])

def n532 (b : ℝ) : ℝ := -(n531 b)
def i532 : RationalInterval := ⟨(-103764338088994474134563267508773 / 50000000000000000000000000000 : ℚ), (-415057349108612726553718743762259 / 200000000000000000000000000000 : ℚ)⟩
theorem b532 (b : ℝ) (hb : rootInterval.Contains b) : i532.Contains (n532 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b531 b hb))
    (by norm_num [i532, i531, RationalInterval.neg]) (by norm_num [i532, i531, RationalInterval.neg])

def n533 (b : ℝ) : ℝ := (n524 b) + (n532 b)
def i533 : RationalInterval := ⟨(-2075247502485908014294618765751279 / 1000000000000000000000000000000 : ℚ), (-2075247486247824349070932900306277 / 1000000000000000000000000000000 : ℚ)⟩
theorem b533 (b : ℝ) (hb : rootInterval.Contains b) : i533.Contains (n533 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b524 b hb) (b532 b hb))
    (by norm_num [i533, i524, i532, RationalInterval.add]) (by norm_num [i533, i524, i532, RationalInterval.add])

def n534 (b : ℝ) : ℝ := (n520 b) + (n521 b)
def i534 : RationalInterval := ⟨(388170208896240291853396066967 / 125000000000000000000000000000 : ℚ), (776340424181838741249027953551 / 250000000000000000000000000000 : ℚ)⟩
theorem b534 (b : ℝ) (hb : rootInterval.Contains b) : i534.Contains (n534 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b520 b hb) (b521 b hb))
    (by norm_num [i534, i520, i521, RationalInterval.add]) (by norm_num [i534, i520, i521, RationalInterval.add])

def n535 (b : ℝ) : ℝ := (n519 b) * (n13 b)
def i535 : RationalInterval := ⟨(3813649356250403316761466883 / 62500000000000000000000000000 : ℚ), (1525459753598286256571197991 / 25000000000000000000000000000 : ℚ)⟩
theorem b535 (b : ℝ) (hb : rootInterval.Contains b) : i535.Contains (n535 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b519 b hb) (b13 b hb))
    (by norm_num [i535, i519, i13, RationalInterval.mul]) (by norm_num [i535, i519, i13, RationalInterval.mul])

def n536 (b : ℝ) : ℝ := -(n535 b)
def i536 : RationalInterval := ⟨(-1525459753598286256571197991 / 25000000000000000000000000000 : ℚ), (-3813649356250403316761466883 / 62500000000000000000000000000 : ℚ)⟩
theorem b536 (b : ℝ) (hb : rootInterval.Contains b) : i536.Contains (n536 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b535 b hb))
    (by norm_num [i536, i535, RationalInterval.neg]) (by norm_num [i536, i535, RationalInterval.neg])

def n537 (b : ℝ) : ℝ := (n534 b) + (n536 b)
def i537 : RationalInterval := ⟨(95135727532062215142635019253 / 31250000000000000000000000000 : ℚ), (761085826756837127981982086019 / 250000000000000000000000000000 : ℚ)⟩
theorem b537 (b : ℝ) (hb : rootInterval.Contains b) : i537.Contains (n537 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b534 b hb) (b536 b hb))
    (by norm_num [i537, i534, i536, RationalInterval.add]) (by norm_num [i537, i534, i536, RationalInterval.add])

def n538 (b : ℝ) : ℝ := (n537 b) * (n13 b)
def i538 : RationalInterval := ⟨(95135727532062215142635019253 / 15625000000000000000000000000 : ℚ), (761085826756837127981982086019 / 125000000000000000000000000000 : ℚ)⟩
theorem b538 (b : ℝ) (hb : rootInterval.Contains b) : i538.Contains (n538 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b537 b hb) (b13 b hb))
    (by norm_num [i538, i537, i13, RationalInterval.mul]) (by norm_num [i538, i537, i13, RationalInterval.mul])

def n539 (b : ℝ) : ℝ := ((697 : ℚ) : ℝ)
def i539 : RationalInterval := ⟨(697 : ℚ), (697 : ℚ)⟩
theorem b539 (b : ℝ) (hb : rootInterval.Contains b) : i539.Contains (n539 b) := by
  exact RationalInterval.contains_point (697 : ℚ)

