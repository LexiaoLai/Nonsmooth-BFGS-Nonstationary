import BFGS.Counterexample.Certificates.IntervalTrace22

/-! Generated arithmetic proofs. Each bound is checked by the Lean kernel. -/
namespace BFGS.Counterexample.Trace
noncomputable section
open BFGS RationalInterval
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false

def n2070 (b : ℝ) : ℝ := (n1902 b) * (n1423 b)
def i2070 : RationalInterval := ⟨(58898508728929848675994126021299 / 500000000000000000000000000000 : ℚ), (117797047352102484272612283378119 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2070 (b : ℝ) (hb : rootInterval.Contains b) : i2070.Contains (n2070 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1902 b hb) (b1423 b hb))
    (by norm_num [i2070, i1902, i1423, RationalInterval.mul]) (by norm_num [i2070, i1902, i1423, RationalInterval.mul])

def n2071 (b : ℝ) : ℝ := (n2069 b) + (n2070 b)
def i2071 : RationalInterval := ⟨(-69144196724685332446423841320309 / 1000000000000000000000000000000 : ℚ), (-17286025567029650618689942861537 / 250000000000000000000000000000 : ℚ)⟩
theorem b2071 (b : ℝ) (hb : rootInterval.Contains b) : i2071.Contains (n2071 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2069 b hb) (b2070 b hb))
    (by norm_num [i2071, i2069, i2070, RationalInterval.add]) (by norm_num [i2071, i2069, i2070, RationalInterval.add])

def n2072 (b : ℝ) : ℝ := (n1967 b) * (n1460 b)
def i2072 : RationalInterval := ⟨(-30933567564768160846219400580233 / 1000000000000000000000000000000 : ℚ), (-1546678042919569110981622690263 / 50000000000000000000000000000 : ℚ)⟩
theorem b2072 (b : ℝ) (hb : rootInterval.Contains b) : i2072.Contains (n2072 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1967 b hb) (b1460 b hb))
    (by norm_num [i2072, i1967, i1460, RationalInterval.mul]) (by norm_num [i2072, i1967, i1460, RationalInterval.mul])

def n2073 (b : ℝ) : ℝ := (n2071 b) + (n2072 b)
def i2073 : RationalInterval := ⟨(-50038882144726746646321620950271 / 500000000000000000000000000000 : ℚ), (-6254853945406874043399514078213 / 62500000000000000000000000000 : ℚ)⟩
theorem b2073 (b : ℝ) (hb : rootInterval.Contains b) : i2073.Contains (n2073 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2071 b hb) (b2072 b hb))
    (by norm_num [i2073, i2071, i2072, RationalInterval.add]) (by norm_num [i2073, i2071, i2072, RationalInterval.add])

def n2074 (b : ℝ) : ℝ := (n1614 b) * (n1344 b)
def i2074 : RationalInterval := ⟨(16804654285056078694315937769099 / 1000000000000000000000000000000 : ℚ), (3360932213747972356450864948399 / 200000000000000000000000000000 : ℚ)⟩
theorem b2074 (b : ℝ) (hb : rootInterval.Contains b) : i2074.Contains (n2074 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1614 b hb) (b1344 b hb))
    (by norm_num [i2074, i1614, i1344, RationalInterval.mul]) (by norm_num [i2074, i1614, i1344, RationalInterval.mul])

def n2075 (b : ℝ) : ℝ := (n1725 b) * (n1361 b)
def i2075 : RationalInterval := ⟨(18323567188504880263504250867597 / 500000000000000000000000000000 : ℚ), (36647149684121958879354221894399 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2075 (b : ℝ) (hb : rootInterval.Contains b) : i2075.Contains (n2075 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1725 b hb) (b1361 b hb))
    (by norm_num [i2075, i1725, i1361, RationalInterval.mul]) (by norm_num [i2075, i1725, i1361, RationalInterval.mul])

def n2076 (b : ℝ) : ℝ := (n2074 b) + (n2075 b)
def i2076 : RationalInterval := ⟨(53451788662065839221324439504293 / 1000000000000000000000000000000 : ℚ), (26725905376430910330804273318197 / 500000000000000000000000000000 : ℚ)⟩
theorem b2076 (b : ℝ) (hb : rootInterval.Contains b) : i2076.Contains (n2076 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2074 b hb) (b2075 b hb))
    (by norm_num [i2076, i2074, i2075, RationalInterval.add]) (by norm_num [i2076, i2074, i2075, RationalInterval.add])

def n2077 (b : ℝ) : ℝ := (n1805 b) * (n1393 b)
def i2077 : RationalInterval := ⟨(11556809233841309497133322725971 / 250000000000000000000000000000 : ℚ), (11556812478236732573956566893389 / 250000000000000000000000000000 : ℚ)⟩
theorem b2077 (b : ℝ) (hb : rootInterval.Contains b) : i2077.Contains (n2077 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1805 b hb) (b1393 b hb))
    (by norm_num [i2077, i1805, i1393, RationalInterval.mul]) (by norm_num [i2077, i1805, i1393, RationalInterval.mul])

def n2078 (b : ℝ) : ℝ := (n2076 b) + (n2077 b)
def i2078 : RationalInterval := ⟨(99679025597431077209857730408177 / 1000000000000000000000000000000 : ℚ), (1993581213316175019148696284199 / 20000000000000000000000000000 : ℚ)⟩
theorem b2078 (b : ℝ) (hb : rootInterval.Contains b) : i2078.Contains (n2078 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2076 b hb) (b2077 b hb))
    (by norm_num [i2078, i2076, i2077, RationalInterval.add]) (by norm_num [i2078, i2076, i2077, RationalInterval.add])

def n2079 (b : ℝ) : ℝ := (n1902 b) * (n1430 b)
def i2079 : RationalInterval := ⟨(-62983151401889103501057103847223 / 1000000000000000000000000000000 : ℚ), (-6298313511616974258782228800929 / 100000000000000000000000000000 : ℚ)⟩
theorem b2079 (b : ℝ) (hb : rootInterval.Contains b) : i2079.Contains (n2079 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1902 b hb) (b1430 b hb))
    (by norm_num [i2079, i1902, i1430, RationalInterval.mul]) (by norm_num [i2079, i1902, i1430, RationalInterval.mul])

def n2080 (b : ℝ) : ℝ := (n2078 b) + (n2079 b)
def i2080 : RationalInterval := ⟨(18347937097770986854400313280477 / 500000000000000000000000000000 : ℚ), (1834796277481950418480626310033 / 50000000000000000000000000000 : ℚ)⟩
theorem b2080 (b : ℝ) (hb : rootInterval.Contains b) : i2080.Contains (n2080 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2078 b hb) (b2079 b hb))
    (by norm_num [i2080, i2078, i2079, RationalInterval.add]) (by norm_num [i2080, i2078, i2079, RationalInterval.add])

def n2081 (b : ℝ) : ℝ := (n1967 b) * (n1467 b)
def i2081 : RationalInterval := ⟨(14012089148590955326575499020323 / 1000000000000000000000000000000 : ℚ), (14012092740478031401565024166979 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2081 (b : ℝ) (hb : rootInterval.Contains b) : i2081.Contains (n2081 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1967 b hb) (b1467 b hb))
    (by norm_num [i2081, i1967, i1467, RationalInterval.mul]) (by norm_num [i2081, i1967, i1467, RationalInterval.mul])

def n2082 (b : ℝ) : ℝ := (n2080 b) + (n2081 b)
def i2082 : RationalInterval := ⟨(50707963344132929035376125581277 / 1000000000000000000000000000000 : ℚ), (50708018290117039771177550367639 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2082 (b : ℝ) (hb : rootInterval.Contains b) : i2082.Contains (n2082 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2080 b hb) (b2081 b hb))
    (by norm_num [i2082, i2080, i2081, RationalInterval.add]) (by norm_num [i2082, i2080, i2081, RationalInterval.add])

def n2083 (b : ℝ) : ℝ := (n1614 b) * (n1345 b)
def i2083 : RationalInterval := ⟨(4791732085210406869570934790717 / 250000000000000000000000000000 : ℚ), (2395866999066057058565615862411 / 125000000000000000000000000000 : ℚ)⟩
theorem b2083 (b : ℝ) (hb : rootInterval.Contains b) : i2083.Contains (n2083 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1614 b hb) (b1345 b hb))
    (by norm_num [i2083, i1614, i1345, RationalInterval.mul]) (by norm_num [i2083, i1614, i1345, RationalInterval.mul])

def n2084 (b : ℝ) : ℝ := (n1725 b) * (n1345 b)
def i2084 : RationalInterval := ⟨(2705093366164217553139798459813 / 50000000000000000000000000000 : ℚ), (6762736220358483896194780960039 / 125000000000000000000000000000 : ℚ)⟩
theorem b2084 (b : ℝ) (hb : rootInterval.Contains b) : i2084.Contains (n2084 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1725 b hb) (b1345 b hb))
    (by norm_num [i2084, i1725, i1345, RationalInterval.mul]) (by norm_num [i2084, i1725, i1345, RationalInterval.mul])

def n2085 (b : ℝ) : ℝ := (n2083 b) + (n2084 b)
def i2085 : RationalInterval := ⟨(9158599458015747317634963544891 / 125000000000000000000000000000 : ℚ), (183172064388490819095207936449 / 2500000000000000000000000000 : ℚ)⟩
theorem b2085 (b : ℝ) (hb : rootInterval.Contains b) : i2085.Contains (n2085 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2083 b hb) (b2084 b hb))
    (by norm_num [i2085, i2083, i2084, RationalInterval.add]) (by norm_num [i2085, i2083, i2084, RationalInterval.add])

def n2086 (b : ℝ) : ℝ := (n1805 b) * (n1398 b)
def i2086 : RationalInterval := ⟨(30874058284539900968474941334299 / 500000000000000000000000000000 : ℚ), (15437033228753913362608803140763 / 250000000000000000000000000000 : ℚ)⟩
theorem b2086 (b : ℝ) (hb : rootInterval.Contains b) : i2086.Contains (n2086 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1805 b hb) (b1398 b hb))
    (by norm_num [i2086, i1805, i1398, RationalInterval.mul]) (by norm_num [i2086, i1805, i1398, RationalInterval.mul])

def n2087 (b : ℝ) : ℝ := (n2085 b) + (n2086 b)
def i2087 : RationalInterval := ⟨(67508456116602890239014795513863 / 500000000000000000000000000000 : ℚ), (33754239667602995272129596785663 / 250000000000000000000000000000 : ℚ)⟩
theorem b2087 (b : ℝ) (hb : rootInterval.Contains b) : i2087.Contains (n2087 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2085 b hb) (b2086 b hb))
    (by norm_num [i2087, i2085, i2086, RationalInterval.add]) (by norm_num [i2087, i2085, i2086, RationalInterval.add])

def n2088 (b : ℝ) : ℝ := (n1902 b) * (n1435 b)
def i2088 : RationalInterval := ⟨(-43582998515904253355142962703763 / 500000000000000000000000000000 : ℚ), (-21791494082015924786104530785553 / 250000000000000000000000000000 : ℚ)⟩
theorem b2088 (b : ℝ) (hb : rootInterval.Contains b) : i2088.Contains (n2088 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1902 b hb) (b1435 b hb))
    (by norm_num [i2088, i1902, i1435, RationalInterval.mul]) (by norm_num [i2088, i1902, i1435, RationalInterval.mul])

def n2089 (b : ℝ) : ℝ := (n2087 b) + (n2088 b)
def i2089 : RationalInterval := ⟨(239254576006986368838718328101 / 5000000000000000000000000000 : ℚ), (1196274558558707048602506600011 / 25000000000000000000000000000 : ℚ)⟩
theorem b2089 (b : ℝ) (hb : rootInterval.Contains b) : i2089.Contains (n2089 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2087 b hb) (b2088 b hb))
    (by norm_num [i2089, i2087, i2088, RationalInterval.add]) (by norm_num [i2089, i2087, i2088, RationalInterval.add])

def n2090 (b : ℝ) : ℝ := (n1967 b) * (n1472 b)
def i2090 : RationalInterval := ⟨(1398439257697956091940570314927 / 50000000000000000000000000000 : ℚ), (2796878987470777282488727823727 / 100000000000000000000000000000 : ℚ)⟩
theorem b2090 (b : ℝ) (hb : rootInterval.Contains b) : i2090.Contains (n2090 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1967 b hb) (b1472 b hb))
    (by norm_num [i2090, i1967, i1472, RationalInterval.mul]) (by norm_num [i2090, i1967, i1472, RationalInterval.mul])

def n2091 (b : ℝ) : ℝ := (n2089 b) + (n2090 b)
def i2091 : RationalInterval := ⟨(3790985017767819780327753595937 / 50000000000000000000000000000 : ℚ), (7581977221705605476898754223771 / 100000000000000000000000000000 : ℚ)⟩
theorem b2091 (b : ℝ) (hb : rootInterval.Contains b) : i2091.Contains (n2091 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2089 b hb) (b2090 b hb))
    (by norm_num [i2091, i2089, i2090, RationalInterval.add]) (by norm_num [i2091, i2089, i2090, RationalInterval.add])

def n2092 (b : ℝ) : ℝ := (n1615 b) * (n1333 b)
def i2092 : RationalInterval := ⟨(469827512770616254281723106753 / 500000000000000000000000000000 : ℚ), (58728481427757335254179154699 / 62500000000000000000000000000 : ℚ)⟩
theorem b2092 (b : ℝ) (hb : rootInterval.Contains b) : i2092.Contains (n2092 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1615 b hb) (b1333 b hb))
    (by norm_num [i2092, i1615, i1333, RationalInterval.mul]) (by norm_num [i2092, i1615, i1333, RationalInterval.mul])

def n2093 (b : ℝ) : ℝ := (n1726 b) * (n1350 b)
def i2093 : RationalInterval := ⟨(323645614843387812511252122717 / 100000000000000000000000000000 : ℚ), (809114555110154450135596074391 / 250000000000000000000000000000 : ℚ)⟩
theorem b2093 (b : ℝ) (hb : rootInterval.Contains b) : i2093.Contains (n2093 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1726 b hb) (b1350 b hb))
    (by norm_num [i2093, i1726, i1350, RationalInterval.mul]) (by norm_num [i2093, i1726, i1350, RationalInterval.mul])

def n2094 (b : ℝ) : ℝ := (n2092 b) + (n2093 b)
def i2094 : RationalInterval := ⟨(1044027793493777658418991860169 / 250000000000000000000000000000 : ℚ), (1044028480821183791152312693187 / 250000000000000000000000000000 : ℚ)⟩
theorem b2094 (b : ℝ) (hb : rootInterval.Contains b) : i2094.Contains (n2094 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2092 b hb) (b2093 b hb))
    (by norm_num [i2094, i2092, i2093, RationalInterval.add]) (by norm_num [i2094, i2092, i2093, RationalInterval.add])

def n2095 (b : ℝ) : ℝ := (n1806 b) * (n1370 b)
def i2095 : RationalInterval := ⟨(1294118839080020087725362209269 / 1000000000000000000000000000000 : ℚ), (129411989939337351283300483413 / 100000000000000000000000000000 : ℚ)⟩
theorem b2095 (b : ℝ) (hb : rootInterval.Contains b) : i2095.Contains (n2095 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1806 b hb) (b1370 b hb))
    (by norm_num [i2095, i1806, i1370, RationalInterval.mul]) (by norm_num [i2095, i1806, i1370, RationalInterval.mul])

def n2096 (b : ℝ) : ℝ := (n2094 b) + (n2095 b)
def i2096 : RationalInterval := ⟨(1094046002611026144280265929989 / 200000000000000000000000000000 : ℚ), (2735116911339054338721127803439 / 500000000000000000000000000000 : ℚ)⟩
theorem b2096 (b : ℝ) (hb : rootInterval.Contains b) : i2096.Contains (n2096 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2094 b hb) (b2095 b hb))
    (by norm_num [i2096, i2094, i2095, RationalInterval.add]) (by norm_num [i2096, i2094, i2095, RationalInterval.add])

def n2097 (b : ℝ) : ℝ := (n1903 b) * (n1407 b)
def i2097 : RationalInterval := ⟨(-89382691380927945412912529911 / 125000000000000000000000000000 : ℚ), (-357530313674104208569846886289 / 500000000000000000000000000000 : ℚ)⟩
theorem b2097 (b : ℝ) (hb : rootInterval.Contains b) : i2097.Contains (n2097 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1903 b hb) (b1407 b hb))
    (by norm_num [i2097, i1903, i1407, RationalInterval.mul]) (by norm_num [i2097, i1903, i1407, RationalInterval.mul])

def n2098 (b : ℝ) : ℝ := (n2096 b) + (n2097 b)
def i2098 : RationalInterval := ⟨(4755168482007707158098029410657 / 1000000000000000000000000000000 : ℚ), (47551731953299002603025618343 / 10000000000000000000000000000 : ℚ)⟩
theorem b2098 (b : ℝ) (hb : rootInterval.Contains b) : i2098.Contains (n2098 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2096 b hb) (b2097 b hb))
    (by norm_num [i2098, i2096, i2097, RationalInterval.add]) (by norm_num [i2098, i2096, i2097, RationalInterval.add])

def n2099 (b : ℝ) : ℝ := (n1974 b) * (n1444 b)
def i2099 : RationalInterval := ⟨(18425856703907082378661590667 / 125000000000000000000000000000 : ℚ), (147407026198982514463304601121 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2099 (b : ℝ) (hb : rootInterval.Contains b) : i2099.Contains (n2099 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1974 b hb) (b1444 b hb))
    (by norm_num [i2099, i1974, i1444, RationalInterval.mul]) (by norm_num [i2099, i1974, i1444, RationalInterval.mul])

def n2100 (b : ℝ) : ℝ := (n2098 b) + (n2099 b)
def i2100 : RationalInterval := ⟨(4902575335638963817127322135993 / 1000000000000000000000000000000 : ℚ), (4902580221528882774765866435421 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2100 (b : ℝ) (hb : rootInterval.Contains b) : i2100.Contains (n2100 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2098 b hb) (b2099 b hb))
    (by norm_num [i2100, i2098, i2099, RationalInterval.add]) (by norm_num [i2100, i2098, i2099, RationalInterval.add])

def n2101 (b : ℝ) : ℝ := (n1615 b) * (n1338 b)
def i2101 : RationalInterval := ⟨(5463534806924619482158328013923 / 1000000000000000000000000000000 : ℚ), (5463537904475601245954015601761 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2101 (b : ℝ) (hb : rootInterval.Contains b) : i2101.Contains (n2101 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1615 b hb) (b1338 b hb))
    (by norm_num [i2101, i1615, i1338, RationalInterval.mul]) (by norm_num [i2101, i1615, i1338, RationalInterval.mul])

def n2102 (b : ℝ) : ℝ := (n1726 b) * (n1355 b)
def i2102 : RationalInterval := ⟨(3671357722653667733601639833747 / 1000000000000000000000000000000 : ℚ), (3671360108984143227097862896311 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2102 (b : ℝ) (hb : rootInterval.Contains b) : i2102.Contains (n2102 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1726 b hb) (b1355 b hb))
    (by norm_num [i2102, i1726, i1355, RationalInterval.mul]) (by norm_num [i2102, i1726, i1355, RationalInterval.mul])

def n2103 (b : ℝ) : ℝ := (n2101 b) + (n2102 b)
def i2103 : RationalInterval := ⟨(913489252957828721575996784767 / 100000000000000000000000000000 : ℚ), (1141862251682468059131484812259 / 125000000000000000000000000000 : ℚ)⟩
theorem b2103 (b : ℝ) (hb : rootInterval.Contains b) : i2103.Contains (n2103 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2101 b hb) (b2102 b hb))
    (by norm_num [i2103, i2101, i2102, RationalInterval.add]) (by norm_num [i2103, i2101, i2102, RationalInterval.add])

def n2104 (b : ℝ) : ℝ := (n1806 b) * (n1379 b)
def i2104 : RationalInterval := ⟨(467014026287441672261601613159 / 125000000000000000000000000000 : ℚ), (3736115510634321055006243617271 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2104 (b : ℝ) (hb : rootInterval.Contains b) : i2104.Contains (n2104 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1806 b hb) (b1379 b hb))
    (by norm_num [i2104, i1806, i1379, RationalInterval.mul]) (by norm_num [i2104, i1806, i1379, RationalInterval.mul])

def n2105 (b : ℝ) : ℝ := (n2103 b) + (n2104 b)
def i2105 : RationalInterval := ⟨(6435502369938910296926390376471 / 500000000000000000000000000000 : ℚ), (12871013524094065528058122115343 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2105 (b : ℝ) (hb : rootInterval.Contains b) : i2105.Contains (n2105 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2103 b hb) (b2104 b hb))
    (by norm_num [i2105, i2103, i2104, RationalInterval.add]) (by norm_num [i2105, i2103, i2104, RationalInterval.add])

def n2106 (b : ℝ) : ℝ := (n1903 b) * (n1416 b)
def i2106 : RationalInterval := ⟨(-1091843416352671714300329104049 / 500000000000000000000000000000 : ℚ), (-1091842046362816462961248741167 / 500000000000000000000000000000 : ℚ)⟩
theorem b2106 (b : ℝ) (hb : rootInterval.Contains b) : i2106.Contains (n2106 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1903 b hb) (b1416 b hb))
    (by norm_num [i2106, i1903, i1416, RationalInterval.mul]) (by norm_num [i2106, i1903, i1416, RationalInterval.mul])

def n2107 (b : ℝ) : ℝ := (n2105 b) + (n2106 b)
def i2107 : RationalInterval := ⟨(2671829476793119291313030636211 / 250000000000000000000000000000 : ℚ), (10687329431368432602135624633009 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2107 (b : ℝ) (hb : rootInterval.Contains b) : i2107.Contains (n2107 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2105 b hb) (b2106 b hb))
    (by norm_num [i2107, i2105, i2106, RationalInterval.add]) (by norm_num [i2107, i2105, i2106, RationalInterval.add])

def n2108 (b : ℝ) : ℝ := (n1974 b) * (n1453 b)
def i2108 : RationalInterval := ⟨(93192966096987566969760804619 / 200000000000000000000000000000 : ℚ), (9319306720937123409484945021 / 20000000000000000000000000000 : ℚ)⟩
theorem b2108 (b : ℝ) (hb : rootInterval.Contains b) : i2108.Contains (n2108 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1974 b hb) (b1453 b hb))
    (by norm_num [i2108, i1974, i1453, RationalInterval.mul]) (by norm_num [i2108, i1974, i1453, RationalInterval.mul])

def n2109 (b : ℝ) : ℝ := (n2107 b) + (n2108 b)
def i2109 : RationalInterval := ⟨(11153282737657415000100926567939 / 1000000000000000000000000000000 : ℚ), (11153294767415288772609871884059 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2109 (b : ℝ) (hb : rootInterval.Contains b) : i2109.Contains (n2109 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2107 b hb) (b2108 b hb))
    (by norm_num [i2109, i2107, i2108, RationalInterval.add]) (by norm_num [i2109, i2107, i2108, RationalInterval.add])

def n2110 (b : ℝ) : ℝ := (n1615 b) * (n1341 b)
def i2110 : RationalInterval := ⟨(-763170029849472979089334130377 / 50000000000000000000000000000 : ℚ), (-1907924068104813900045439692873 / 125000000000000000000000000000 : ℚ)⟩
theorem b2110 (b : ℝ) (hb : rootInterval.Contains b) : i2110.Contains (n2110 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1615 b hb) (b1341 b hb))
    (by norm_num [i2110, i1615, i1341, RationalInterval.mul]) (by norm_num [i2110, i1615, i1341, RationalInterval.mul])

def n2111 (b : ℝ) : ℝ := (n1726 b) * (n1358 b)
def i2111 : RationalInterval := ⟨(-7324060675528083084324165512579 / 250000000000000000000000000000 : ℚ), (-14648113100046731543714854545343 / 500000000000000000000000000000 : ℚ)⟩
theorem b2111 (b : ℝ) (hb : rootInterval.Contains b) : i2111.Contains (n2111 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1726 b hb) (b1358 b hb))
    (by norm_num [i2111, i1726, i1358, RationalInterval.mul]) (by norm_num [i2111, i1726, i1358, RationalInterval.mul])

def n2112 (b : ℝ) : ℝ := (n2110 b) + (n2111 b)
def i2112 : RationalInterval := ⟨(-696244426548465498735677260279 / 15625000000000000000000000000 : ℚ), (-4455961874493197428779322663367 / 100000000000000000000000000000 : ℚ)⟩
theorem b2112 (b : ℝ) (hb : rootInterval.Contains b) : i2112.Contains (n2112 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2110 b hb) (b2111 b hb))
    (by norm_num [i2112, i2110, i2111, RationalInterval.add]) (by norm_num [i2112, i2110, i2111, RationalInterval.add])

def n2113 (b : ℝ) : ℝ := (n1806 b) * (n1386 b)
def i2113 : RationalInterval := ⟨(-3730342384846478077030344517787 / 250000000000000000000000000000 : ℚ), (-14921364088026100736595888110063 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2113 (b : ℝ) (hb : rootInterval.Contains b) : i2113.Contains (n2113 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1806 b hb) (b1386 b hb))
    (by norm_num [i2113, i1806, i1386, RationalInterval.mul]) (by norm_num [i2113, i1806, i1386, RationalInterval.mul])

def n2114 (b : ℝ) : ℝ := (n2112 b) + (n2113 b)
def i2114 : RationalInterval := ⟨(-14870253209621926056801180682251 / 250000000000000000000000000000 : ℚ), (-59480982832958075024389114743733 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2114 (b : ℝ) (hb : rootInterval.Contains b) : i2114.Contains (n2114 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2112 b hb) (b2113 b hb))
    (by norm_num [i2114, i2112, i2113, RationalInterval.add]) (by norm_num [i2114, i2112, i2113, RationalInterval.add])

def n2115 (b : ℝ) : ℝ := (n1903 b) * (n1423 b)
def i2115 : RationalInterval := ⟨(36456457102654625606947255007 / 4000000000000000000000000000 : ℚ), (1139265114814423790401516740323 / 125000000000000000000000000000 : ℚ)⟩
theorem b2115 (b : ℝ) (hb : rootInterval.Contains b) : i2115.Contains (n2115 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1903 b hb) (b1423 b hb))
    (by norm_num [i2115, i1903, i1423, RationalInterval.mul]) (by norm_num [i2115, i1903, i1423, RationalInterval.mul])

def n2116 (b : ℝ) : ℝ := (n2114 b) + (n2115 b)
def i2116 : RationalInterval := ⟨(-25183449281412023912733954488627 / 500000000000000000000000000000 : ℚ), (-50366861914442684701176980821149 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2116 (b : ℝ) (hb : rootInterval.Contains b) : i2116.Contains (n2116 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2114 b hb) (b2115 b hb))
    (by norm_num [i2116, i2114, i2115, RationalInterval.add]) (by norm_num [i2116, i2114, i2115, RationalInterval.add])

def n2117 (b : ℝ) : ℝ := (n1974 b) * (n1460 b)
def i2117 : RationalInterval := ⟨(-1970694699817451695207139802021 / 1000000000000000000000000000000 : ℚ), (-985346819991137267992778450183 / 500000000000000000000000000000 : ℚ)⟩
theorem b2117 (b : ℝ) (hb : rootInterval.Contains b) : i2117.Contains (n2117 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1974 b hb) (b1460 b hb))
    (by norm_num [i2117, i1974, i1460, RationalInterval.mul]) (by norm_num [i2117, i1974, i1460, RationalInterval.mul])

def n2118 (b : ℝ) : ℝ := (n2116 b) + (n2117 b)
def i2118 : RationalInterval := ⟨(-2093503730505659980827001951171 / 40000000000000000000000000000 : ℚ), (-10467511110884991847432507544303 / 200000000000000000000000000000 : ℚ)⟩
theorem b2118 (b : ℝ) (hb : rootInterval.Contains b) : i2118.Contains (n2118 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2116 b hb) (b2117 b hb))
    (by norm_num [i2118, i2116, i2117, RationalInterval.add]) (by norm_num [i2118, i2116, i2117, RationalInterval.add])

def n2119 (b : ℝ) : ℝ := (n1615 b) * (n1344 b)
def i2119 : RationalInterval := ⟨(1549641084165350386693696175757 / 200000000000000000000000000000 : ℚ), (7748209513354222135350740946411 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2119 (b : ℝ) (hb : rootInterval.Contains b) : i2119.Contains (n2119 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1615 b hb) (b1344 b hb))
    (by norm_num [i2119, i1615, i1344, RationalInterval.mul]) (by norm_num [i2119, i1615, i1344, RationalInterval.mul])

def n2120 (b : ℝ) : ℝ := (n1726 b) * (n1361 b)
def i2120 : RationalInterval := ⟨(2051814011706124990048688558761 / 125000000000000000000000000000 : ℚ), (4103630335553641532650705942797 / 250000000000000000000000000000 : ℚ)⟩
theorem b2120 (b : ℝ) (hb : rootInterval.Contains b) : i2120.Contains (n2120 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1726 b hb) (b1361 b hb))
    (by norm_num [i2120, i1726, i1361, RationalInterval.mul]) (by norm_num [i2120, i1726, i1361, RationalInterval.mul])

def n2121 (b : ℝ) : ℝ := (n2119 b) + (n2120 b)
def i2121 : RationalInterval := ⟨(24162717514475751853857989348873 / 1000000000000000000000000000000 : ℚ), (24162730855568788265953564717599 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2121 (b : ℝ) (hb : rootInterval.Contains b) : i2121.Contains (n2121 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2119 b hb) (b2120 b hb))
    (by norm_num [i2121, i2119, i2120, RationalInterval.add]) (by norm_num [i2121, i2119, i2120, RationalInterval.add])

def n2122 (b : ℝ) : ℝ := (n1806 b) * (n1393 b)
def i2122 : RationalInterval := ⟨(7800193474698713217648347950051 / 1000000000000000000000000000000 : ℚ), (3900098202547494541564341977263 / 500000000000000000000000000000 : ℚ)⟩
theorem b2122 (b : ℝ) (hb : rootInterval.Contains b) : i2122.Contains (n2122 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1806 b hb) (b1393 b hb))
    (by norm_num [i2122, i1806, i1393, RationalInterval.mul]) (by norm_num [i2122, i1806, i1393, RationalInterval.mul])

def n2123 (b : ℝ) : ℝ := (n2121 b) + (n2122 b)
def i2123 : RationalInterval := ⟨(7990727747293616267876584324731 / 250000000000000000000000000000 : ℚ), (255703418085310218792657989377 / 8000000000000000000000000000 : ℚ)⟩
theorem b2123 (b : ℝ) (hb : rootInterval.Contains b) : i2123.Contains (n2123 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2121 b hb) (b2122 b hb))
    (by norm_num [i2123, i2121, i2122, RationalInterval.add]) (by norm_num [i2123, i2121, i2122, RationalInterval.add])

def n2124 (b : ℝ) : ℝ := (n1903 b) * (n1430 b)
def i2124 : RationalInterval := ⟨(-4873093771104049720313119793873 / 1000000000000000000000000000000 : ℚ), (-304568137248089224093289268617 / 62500000000000000000000000000 : ℚ)⟩
theorem b2124 (b : ℝ) (hb : rootInterval.Contains b) : i2124.Contains (n2124 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1903 b hb) (b1430 b hb))
    (by norm_num [i2124, i1903, i1430, RationalInterval.mul]) (by norm_num [i2124, i1903, i1430, RationalInterval.mul])

def n2125 (b : ℝ) : ℝ := (n2123 b) + (n2124 b)
def i2125 : RationalInterval := ⟨(27089817218070415351193217505051 / 1000000000000000000000000000000 : ℚ), (27089837064694349763589620374253 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2125 (b : ℝ) (hb : rootInterval.Contains b) : i2125.Contains (n2125 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2123 b hb) (b2124 b hb))
    (by norm_num [i2125, i2123, i2124, RationalInterval.add]) (by norm_num [i2125, i2123, i2124, RationalInterval.add])

def n2126 (b : ℝ) : ℝ := (n1974 b) * (n1467 b)
def i2126 : RationalInterval := ⟨(89267236624981326129901493453 / 100000000000000000000000000000 : ℚ), (892672881625886422344256758533 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2126 (b : ℝ) (hb : rootInterval.Contains b) : i2126.Contains (n2126 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1974 b hb) (b1467 b hb))
    (by norm_num [i2126, i1974, i1467, RationalInterval.mul]) (by norm_num [i2126, i1974, i1467, RationalInterval.mul])

def n2127 (b : ℝ) : ℝ := (n2125 b) + (n2126 b)
def i2127 : RationalInterval := ⟨(27982489584320228612492232439581 / 1000000000000000000000000000000 : ℚ), (13991254973160118092966938566393 / 500000000000000000000000000000 : ℚ)⟩
theorem b2127 (b : ℝ) (hb : rootInterval.Contains b) : i2127.Contains (n2127 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2125 b hb) (b2126 b hb))
    (by norm_num [i2127, i2125, i2126, RationalInterval.add]) (by norm_num [i2127, i2125, i2126, RationalInterval.add])

def n2128 (b : ℝ) : ℝ := (n1615 b) * (n1345 b)
def i2128 : RationalInterval := ⟨(2209347713317319980693233961963 / 250000000000000000000000000000 : ℚ), (441869774081366748207100793801 / 50000000000000000000000000000 : ℚ)⟩
theorem b2128 (b : ℝ) (hb : rootInterval.Contains b) : i2128.Contains (n2128 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1615 b hb) (b1345 b hb))
    (by norm_num [i2128, i1615, i1345, RationalInterval.mul]) (by norm_num [i2128, i1615, i1345, RationalInterval.mul])

def n2129 (b : ℝ) : ℝ := (n1726 b) * (n1345 b)
def i2129 : RationalInterval := ⟨(1514538194056173872596763721637 / 62500000000000000000000000000 : ℚ), (3029078085953779629261687153603 / 125000000000000000000000000000 : ℚ)⟩
theorem b2129 (b : ℝ) (hb : rootInterval.Contains b) : i2129.Contains (n2129 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1726 b hb) (b1345 b hb))
    (by norm_num [i2129, i1726, i1345, RationalInterval.mul]) (by norm_num [i2129, i1726, i1345, RationalInterval.mul])

def n2130 (b : ℝ) : ℝ := (n2128 b) + (n2129 b)
def i2130 : RationalInterval := ⟨(8267500489542015471080288848511 / 250000000000000000000000000000 : ℚ), (8267505042314392999558878276211 / 250000000000000000000000000000 : ℚ)⟩
theorem b2130 (b : ℝ) (hb : rootInterval.Contains b) : i2130.Contains (n2130 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2128 b hb) (b2129 b hb))
    (by norm_num [i2130, i2128, i2129, RationalInterval.add]) (by norm_num [i2130, i2128, i2129, RationalInterval.add])

def n2131 (b : ℝ) : ℝ := (n1806 b) * (n1398 b)
def i2131 : RationalInterval := ⟨(5209561374071624545287164217283 / 500000000000000000000000000000 : ℚ), (81399425746591839460260017879 / 7812500000000000000000000000 : ℚ)⟩
theorem b2131 (b : ℝ) (hb : rootInterval.Contains b) : i2131.Contains (n2131 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1806 b hb) (b1398 b hb))
    (by norm_num [i2131, i1806, i1398, RationalInterval.mul]) (by norm_num [i2131, i1806, i1398, RationalInterval.mul])

def n2132 (b : ℝ) : ℝ := (n2130 b) + (n2131 b)
def i2132 : RationalInterval := ⟨(4348912470631131097489548382861 / 100000000000000000000000000000 : ℚ), (10872286666205331862287198848339 / 250000000000000000000000000000 : ℚ)⟩
theorem b2132 (b : ℝ) (hb : rootInterval.Contains b) : i2132.Contains (n2132 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2130 b hb) (b2131 b hb))
    (by norm_num [i2132, i2130, i2131, RationalInterval.add]) (by norm_num [i2132, i2130, i2131, RationalInterval.add])

def n2133 (b : ℝ) : ℝ := (n1903 b) * (n1435 b)
def i2133 : RationalInterval := ⟨(-6744154075069665622539765621861 / 1000000000000000000000000000000 : ℚ), (-6744149269211898280813113070453 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2133 (b : ℝ) (hb : rootInterval.Contains b) : i2133.Contains (n2133 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1903 b hb) (b1435 b hb))
    (by norm_num [i2133, i1903, i1435, RationalInterval.mul]) (by norm_num [i2133, i1903, i1435, RationalInterval.mul])

def n2134 (b : ℝ) : ℝ := (n2132 b) + (n2133 b)
def i2134 : RationalInterval := ⟨(36744970631241645352355718206749 / 1000000000000000000000000000000 : ℚ), (36744997395609429168335682322903 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2134 (b : ℝ) (hb : rootInterval.Contains b) : i2134.Contains (n2134 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2132 b hb) (b2133 b hb))
    (by norm_num [i2134, i2132, i2133, RationalInterval.add]) (by norm_num [i2134, i2132, i2133, RationalInterval.add])

def n2135 (b : ℝ) : ℝ := (n1974 b) * (n1472 b)
def i2135 : RationalInterval := ⟨(445453946227354595331103084319 / 250000000000000000000000000000 : ℚ), (1781816657616022752536582353971 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2135 (b : ℝ) (hb : rootInterval.Contains b) : i2135.Contains (n2135 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1974 b hb) (b1472 b hb))
    (by norm_num [i2135, i1974, i1472, RationalInterval.mul]) (by norm_num [i2135, i1974, i1472, RationalInterval.mul])

def n2136 (b : ℝ) : ℝ := (n2134 b) + (n2135 b)
def i2136 : RationalInterval := ⟨(1541071456646042549347205221761 / 40000000000000000000000000000 : ℚ), (19263407026612725960436132338437 / 500000000000000000000000000000 : ℚ)⟩
theorem b2136 (b : ℝ) (hb : rootInterval.Contains b) : i2136.Contains (n2136 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2134 b hb) (b2135 b hb))
    (by norm_num [i2136, i2134, i2135, RationalInterval.add]) (by norm_num [i2136, i2134, i2135, RationalInterval.add])

def n2137 (b : ℝ) : ℝ := (n1617 b) * (n1333 b)
def i2137 : RationalInterval := ⟨(8472018286350149809041062209 / 20000000000000000000000000000 : ℚ), (13237540484544035741364755293 / 31250000000000000000000000000 : ℚ)⟩
theorem b2137 (b : ℝ) (hb : rootInterval.Contains b) : i2137.Contains (n2137 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1617 b hb) (b1333 b hb))
    (by norm_num [i2137, i1617, i1333, RationalInterval.mul]) (by norm_num [i2137, i1617, i1333, RationalInterval.mul])

def n2138 (b : ℝ) : ℝ := (n1728 b) * (n1350 b)
def i2138 : RationalInterval := ⟨(1408460404624922006107602134793 / 1000000000000000000000000000000 : ℚ), (281692323016363591696272712833 / 200000000000000000000000000000 : ℚ)⟩
theorem b2138 (b : ℝ) (hb : rootInterval.Contains b) : i2138.Contains (n2138 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1728 b hb) (b1350 b hb))
    (by norm_num [i2138, i1728, i1350, RationalInterval.mul]) (by norm_num [i2138, i1728, i1350, RationalInterval.mul])

def n2139 (b : ℝ) : ℝ := (n2137 b) + (n2138 b)
def i2139 : RationalInterval := ⟨(1832061318942429496559655245243 / 1000000000000000000000000000000 : ℚ), (1832062910587227102205035733541 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2139 (b : ℝ) (hb : rootInterval.Contains b) : i2139.Contains (n2139 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2137 b hb) (b2138 b hb))
    (by norm_num [i2139, i2137, i2138, RationalInterval.add]) (by norm_num [i2139, i2137, i2138, RationalInterval.add])

def n2140 (b : ℝ) : ℝ := (n1801 b) * (n1370 b)
def i2140 : RationalInterval := ⟨(-52308174745525724782987954891 / 200000000000000000000000000000 : ℚ), (-261540624280439472651093341571 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2140 (b : ℝ) (hb : rootInterval.Contains b) : i2140.Contains (n2140 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1801 b hb) (b1370 b hb))
    (by norm_num [i2140, i1801, i1370, RationalInterval.mul]) (by norm_num [i2140, i1801, i1370, RationalInterval.mul])

def n2141 (b : ℝ) : ℝ := (n2139 b) + (n2140 b)
def i2141 : RationalInterval := ⟨(392630111303700218161178867697 / 250000000000000000000000000000 : ℚ), (157052228630678762955394239197 / 100000000000000000000000000000 : ℚ)⟩
theorem b2141 (b : ℝ) (hb : rootInterval.Contains b) : i2141.Contains (n2141 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2139 b hb) (b2140 b hb))
    (by norm_num [i2141, i2139, i2140, RationalInterval.add]) (by norm_num [i2141, i2139, i2140, RationalInterval.add])

def n2142 (b : ℝ) : ℝ := (n1905 b) * (n1407 b)
def i2142 : RationalInterval := ⟨(216276452592917670783070697873 / 250000000000000000000000000000 : ℚ), (173021342291592898245803725627 / 200000000000000000000000000000 : ℚ)⟩
theorem b2142 (b : ℝ) (hb : rootInterval.Contains b) : i2142.Contains (n2142 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1905 b hb) (b1407 b hb))
    (by norm_num [i2142, i1905, i1407, RationalInterval.mul]) (by norm_num [i2142, i1905, i1407, RationalInterval.mul])

def n2143 (b : ℝ) : ℝ := (n2141 b) + (n2142 b)
def i2143 : RationalInterval := ⟨(60890656389661788894424956557 / 25000000000000000000000000000 : ℚ), (487125799552950424156592204021 / 200000000000000000000000000000 : ℚ)⟩
theorem b2143 (b : ℝ) (hb : rootInterval.Contains b) : i2143.Contains (n2143 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2141 b hb) (b2142 b hb))
    (by norm_num [i2143, i2141, i2142, RationalInterval.add]) (by norm_num [i2143, i2141, i2142, RationalInterval.add])

def n2144 (b : ℝ) : ℝ := (n1976 b) * (n1444 b)
def i2144 : RationalInterval := ⟨(-4363652425940257144221011801 / 125000000000000000000000000000 : ℚ), (-34909151916520792394483655629 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2144 (b : ℝ) (hb : rootInterval.Contains b) : i2144.Contains (n2144 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1976 b hb) (b1444 b hb))
    (by norm_num [i2144, i1976, i1444, RationalInterval.mul]) (by norm_num [i2144, i1976, i1444, RationalInterval.mul])

def n2145 (b : ℝ) : ℝ := (n2143 b) + (n2144 b)
def i2145 : RationalInterval := ⟨(37511203690296085915987971373 / 15625000000000000000000000000 : ℚ), (600179961462057832097119341119 / 250000000000000000000000000000 : ℚ)⟩
theorem b2145 (b : ℝ) (hb : rootInterval.Contains b) : i2145.Contains (n2145 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2143 b hb) (b2144 b hb))
    (by norm_num [i2145, i2143, i2144, RationalInterval.add]) (by norm_num [i2145, i2143, i2144, RationalInterval.add])

def n2146 (b : ℝ) : ℝ := (n1617 b) * (n1338 b)
def i2146 : RationalInterval := ⟨(615746810454652441155014153897 / 250000000000000000000000000000 : ℚ), (2462989079269931518357094268341 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2146 (b : ℝ) (hb : rootInterval.Contains b) : i2146.Contains (n2146 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1617 b hb) (b1338 b hb))
    (by norm_num [i2146, i1617, i1338, RationalInterval.mul]) (by norm_num [i2146, i1617, i1338, RationalInterval.mul])

def n2147 (b : ℝ) : ℝ := (n1728 b) * (n1355 b)
def i2147 : RationalInterval := ⟨(1597723480997524633522777674537 / 1000000000000000000000000000000 : ℚ), (39943121743301691300864032621 / 25000000000000000000000000000 : ℚ)⟩
theorem b2147 (b : ℝ) (hb : rootInterval.Contains b) : i2147.Contains (n2147 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1728 b hb) (b1355 b hb))
    (by norm_num [i2147, i1728, i1355, RationalInterval.mul]) (by norm_num [i2147, i1728, i1355, RationalInterval.mul])

def n2148 (b : ℝ) : ℝ := (n2146 b) + (n2147 b)
def i2148 : RationalInterval := ⟨(32485685782529075185142674321 / 8000000000000000000000000000 : ℚ), (4060713949001999170391655573181 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2148 (b : ℝ) (hb : rootInterval.Contains b) : i2148.Contains (n2148 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2146 b hb) (b2147 b hb))
    (by norm_num [i2148, i2146, i2147, RationalInterval.add]) (by norm_num [i2148, i2146, i2147, RationalInterval.add])

def n2149 (b : ℝ) : ℝ := (n1801 b) * (n1379 b)
def i2149 : RationalInterval := ⟨(-755066756532133687435292977271 / 1000000000000000000000000000000 : ℚ), (-755065988034111354155170613581 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2149 (b : ℝ) (hb : rootInterval.Contains b) : i2149.Contains (n2149 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1801 b hb) (b1379 b hb))
    (by norm_num [i2149, i1801, i1379, RationalInterval.mul]) (by norm_num [i2149, i1801, i1379, RationalInterval.mul])

def n2150 (b : ℝ) : ℝ := (n2148 b) + (n2149 b)
def i2150 : RationalInterval := ⟨(1652821983142000355353770656427 / 500000000000000000000000000000 : ℚ), (8264119902419719540591212399 / 2500000000000000000000000000 : ℚ)⟩
theorem b2150 (b : ℝ) (hb : rootInterval.Contains b) : i2150.Contains (n2150 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2148 b hb) (b2149 b hb))
    (by norm_num [i2150, i2148, i2149, RationalInterval.add]) (by norm_num [i2150, i2148, i2149, RationalInterval.add])

def n2151 (b : ℝ) : ℝ := (n1905 b) * (n1416 b)
def i2151 : RationalInterval := ⟨(2641898776665833325717686541243 / 1000000000000000000000000000000 : ℚ), (52838030090322102133755670329 / 20000000000000000000000000000 : ℚ)⟩
theorem b2151 (b : ℝ) (hb : rootInterval.Contains b) : i2151.Contains (n2151 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1905 b hb) (b1416 b hb))
    (by norm_num [i2151, i1905, i1416, RationalInterval.mul]) (by norm_num [i2151, i1905, i1416, RationalInterval.mul])

def n2152 (b : ℝ) : ℝ := (n2150 b) + (n2151 b)
def i2152 : RationalInterval := ⟨(5947542742949834036425227854097 / 1000000000000000000000000000000 : ℚ), (118950989309679858458485369521 / 20000000000000000000000000000 : ℚ)⟩
theorem b2152 (b : ℝ) (hb : rootInterval.Contains b) : i2152.Contains (n2152 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2150 b hb) (b2151 b hb))
    (by norm_num [i2152, i2150, i2151, RationalInterval.add]) (by norm_num [i2152, i2150, i2151, RationalInterval.add])

def n2153 (b : ℝ) : ℝ := (n1976 b) * (n1453 b)
def i2153 : RationalInterval := ⟨(-110350819576276948104050776823 / 1000000000000000000000000000000 : ℚ), (-110350615690133434868101813199 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2153 (b : ℝ) (hb : rootInterval.Contains b) : i2153.Contains (n2153 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1976 b hb) (b1453 b hb))
    (by norm_num [i2153, i1976, i1453, RationalInterval.mul]) (by norm_num [i2153, i1976, i1453, RationalInterval.mul])

def n2154 (b : ℝ) : ℝ := (n2152 b) + (n2153 b)
def i2154 : RationalInterval := ⟨(2918595961686778544160588538637 / 500000000000000000000000000000 : ℚ), (5837198849793859488056166662851 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2154 (b : ℝ) (hb : rootInterval.Contains b) : i2154.Contains (n2154 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2152 b hb) (b2153 b hb))
    (by norm_num [i2154, i2152, i2153, RationalInterval.add]) (by norm_num [i2154, i2152, i2153, RationalInterval.add])

def n2155 (b : ℝ) : ℝ := (n1617 b) * (n1341 b)
def i2155 : RationalInterval := ⟨(-3440407080557765664426318322669 / 500000000000000000000000000000 : ℚ), (-6880809298983425445667135378947 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2155 (b : ℝ) (hb : rootInterval.Contains b) : i2155.Contains (n2155 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1617 b hb) (b1341 b hb))
    (by norm_num [i2155, i1617, i1341, RationalInterval.mul]) (by norm_num [i2155, i1617, i1341, RationalInterval.mul])

def n2156 (b : ℝ) : ℝ := (n1728 b) * (n1358 b)
def i2156 : RationalInterval := ⟨(-12749317464208909844901572773641 / 1000000000000000000000000000000 : ℚ), (-1593663435998269652627098354359 / 125000000000000000000000000000 : ℚ)⟩
theorem b2156 (b : ℝ) (hb : rootInterval.Contains b) : i2156.Contains (n2156 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1728 b hb) (b1358 b hb))
    (by norm_num [i2156, i1728, i1358, RationalInterval.mul]) (by norm_num [i2156, i1728, i1358, RationalInterval.mul])

def n2157 (b : ℝ) : ℝ := (n2155 b) + (n2156 b)
def i2157 : RationalInterval := ⟨(-19630131625324441173754209418979 / 1000000000000000000000000000000 : ℚ), (-19630116786969582666683922213819 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2157 (b : ℝ) (hb : rootInterval.Contains b) : i2157.Contains (n2157 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2155 b hb) (b2156 b hb))
    (by norm_num [i2157, i2155, i2156, RationalInterval.add]) (by norm_num [i2157, i2155, i2156, RationalInterval.add])

def n2158 (b : ℝ) : ℝ := (n1801 b) * (n1386 b)
def i2158 : RationalInterval := ⟨(603119707533562662476393764003 / 200000000000000000000000000000 : ℚ), (1507800022383226560264812847559 / 500000000000000000000000000000 : ℚ)⟩
theorem b2158 (b : ℝ) (hb : rootInterval.Contains b) : i2158.Contains (n2158 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1801 b hb) (b1386 b hb))
    (by norm_num [i2158, i1801, i1386, RationalInterval.mul]) (by norm_num [i2158, i1801, i1386, RationalInterval.mul])

def n2159 (b : ℝ) : ℝ := (n2157 b) + (n2158 b)
def i2159 : RationalInterval := ⟨(-4153633271914156965343060149741 / 250000000000000000000000000000 : ℚ), (-16614516742203129546154296518701 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2159 (b : ℝ) (hb : rootInterval.Contains b) : i2159.Contains (n2159 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2157 b hb) (b2158 b hb))
    (by norm_num [i2159, i2157, i2158, RationalInterval.add]) (by norm_num [i2159, i2157, i2158, RationalInterval.add])

