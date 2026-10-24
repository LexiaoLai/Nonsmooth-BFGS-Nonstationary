import BFGS.Counterexample.Certificates.IntervalTrace24

/-! Generated arithmetic proofs. Each bound is checked by the Lean kernel. -/
namespace BFGS.Counterexample.Trace
noncomputable section
open BFGS RationalInterval
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false

def n2250 (b : ℝ) : ℝ := (n319 b) * (n2189 b)
def i2250 : RationalInterval := ⟨(-61214982918364352662765140333 / 500000000000000000000000000000 : ℚ), (-12242996354452883800310424683 / 100000000000000000000000000000 : ℚ)⟩
theorem b2250 (b : ℝ) (hb : rootInterval.Contains b) : i2250.Contains (n2250 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b319 b hb) (b2189 b hb))
    (by norm_num [i2250, i319, i2189, RationalInterval.mul]) (by norm_num [i2250, i319, i2189, RationalInterval.mul])

def n2251 (b : ℝ) : ℝ := (n2243 b) + (n2247 b)
def i2251 : RationalInterval := ⟨(-563827121032002840255877030329 / 500000000000000000000000000000 : ℚ), (-22553084506093189177876678369 / 20000000000000000000000000000 : ℚ)⟩
theorem b2251 (b : ℝ) (hb : rootInterval.Contains b) : i2251.Contains (n2251 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2243 b hb) (b2247 b hb))
    (by norm_num [i2251, i2243, i2247, RationalInterval.add]) (by norm_num [i2251, i2243, i2247, RationalInterval.add])

def n2252 (b : ℝ) : ℝ := (n2244 b) + (n2248 b)
def i2252 : RationalInterval := ⟨(-105413248601789908694721343287 / 200000000000000000000000000000 : ℚ), (-527066234215781730724515866483 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2252 (b : ℝ) (hb : rootInterval.Contains b) : i2252.Contains (n2252 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2244 b hb) (b2248 b hb))
    (by norm_num [i2252, i2244, i2248, RationalInterval.add]) (by norm_num [i2252, i2244, i2248, RationalInterval.add])

def n2253 (b : ℝ) : ℝ := (n2245 b) + (n2249 b)
def i2253 : RationalInterval := ⟨(-105413248601789908694721343287 / 200000000000000000000000000000 : ℚ), (-527066234215781730724515866483 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2253 (b : ℝ) (hb : rootInterval.Contains b) : i2253.Contains (n2253 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2245 b hb) (b2249 b hb))
    (by norm_num [i2253, i2245, i2249, RationalInterval.add]) (by norm_num [i2253, i2245, i2249, RationalInterval.add])

def n2254 (b : ℝ) : ℝ := (n2246 b) + (n2250 b)
def i2254 : RationalInterval := ⟨(-61214982918364352662765140333 / 250000000000000000000000000000 : ℚ), (-12242996354452883800310424683 / 50000000000000000000000000000 : ℚ)⟩
theorem b2254 (b : ℝ) (hb : rootInterval.Contains b) : i2254.Contains (n2254 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2246 b hb) (b2250 b hb))
    (by norm_num [i2254, i2246, i2250, RationalInterval.add]) (by norm_num [i2254, i2246, i2250, RationalInterval.add])

def n2255 (b : ℝ) : ℝ := (n2235 b) * (n318 b)
def i2255 : RationalInterval := ⟨(1255188265390940507875300946083 / 1000000000000000000000000000000 : ℚ), (627594158339948680198478643599 / 500000000000000000000000000000 : ℚ)⟩
theorem b2255 (b : ℝ) (hb : rootInterval.Contains b) : i2255.Contains (n2255 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2235 b hb) (b318 b hb))
    (by norm_num [i2255, i2235, i318, RationalInterval.mul]) (by norm_num [i2255, i2235, i318, RationalInterval.mul])

def n2256 (b : ℝ) : ℝ := (n2235 b) * (n319 b)
def i2256 : RationalInterval := ⟨(541032183176107957780202453607 / 1000000000000000000000000000000 : ℚ), (67629025885820017413483010981 / 125000000000000000000000000000 : ℚ)⟩
theorem b2256 (b : ℝ) (hb : rootInterval.Contains b) : i2256.Contains (n2256 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2235 b hb) (b319 b hb))
    (by norm_num [i2256, i2235, i319, RationalInterval.mul]) (by norm_num [i2256, i2235, i319, RationalInterval.mul])

def n2257 (b : ℝ) : ℝ := (n2238 b) * (n318 b)
def i2257 : RationalInterval := ⟨(536690488461647213965091736337 / 1000000000000000000000000000000 : ℚ), (134172628813345914632222984641 / 250000000000000000000000000000 : ℚ)⟩
theorem b2257 (b : ℝ) (hb : rootInterval.Contains b) : i2257.Contains (n2257 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2238 b hb) (b318 b hb))
    (by norm_num [i2257, i2238, i318, RationalInterval.mul]) (by norm_num [i2257, i2238, i318, RationalInterval.mul])

def n2258 (b : ℝ) : ℝ := (n2238 b) * (n319 b)
def i2258 : RationalInterval := ⟨(231333286542333326627395895301 / 1000000000000000000000000000000 : ℚ), (231333298861490064642471930923 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2258 (b : ℝ) (hb : rootInterval.Contains b) : i2258.Contains (n2258 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2238 b hb) (b319 b hb))
    (by norm_num [i2258, i2238, i319, RationalInterval.mul]) (by norm_num [i2258, i2238, i319, RationalInterval.mul])

def n2259 (b : ℝ) : ℝ := (n2210 b) * (n2188 b)
def i2259 : RationalInterval := ⟨(-381673057129833003186576938931 / 250000000000000000000000000000 : ℚ), (-763346105502660705767552759559 / 500000000000000000000000000000 : ℚ)⟩
theorem b2259 (b : ℝ) (hb : rootInterval.Contains b) : i2259.Contains (n2259 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2210 b hb) (b2188 b hb))
    (by norm_num [i2259, i2210, i2188, RationalInterval.mul]) (by norm_num [i2259, i2210, i2188, RationalInterval.mul])

def n2260 (b : ℝ) : ℝ := (n2210 b) * (n2189 b)
def i2260 : RationalInterval := ⟨(-769093303623190974978470545207 / 1000000000000000000000000000000 : ℚ), (-384546647197151171847669265433 / 500000000000000000000000000000 : ℚ)⟩
theorem b2260 (b : ℝ) (hb : rootInterval.Contains b) : i2260.Contains (n2260 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2210 b hb) (b2189 b hb))
    (by norm_num [i2260, i2210, i2189, RationalInterval.mul]) (by norm_num [i2260, i2210, i2189, RationalInterval.mul])

def n2261 (b : ℝ) : ℝ := (n2213 b) * (n2188 b)
def i2261 : RationalInterval := ⟨(-90038940982728000433752071081 / 125000000000000000000000000000 : ℚ), (-144062303744464349942761153171 / 200000000000000000000000000000 : ℚ)⟩
theorem b2261 (b : ℝ) (hb : rootInterval.Contains b) : i2261.Contains (n2261 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2213 b hb) (b2188 b hb))
    (by norm_num [i2261, i2213, i2188, RationalInterval.mul]) (by norm_num [i2261, i2213, i2188, RationalInterval.mul])

def n2262 (b : ℝ) : ℝ := (n2213 b) * (n2189 b)
def i2262 : RationalInterval := ⟨(-362867356139229497240987478619 / 1000000000000000000000000000000 : ℚ), (-90716837835884960070881294217 / 250000000000000000000000000000 : ℚ)⟩
theorem b2262 (b : ℝ) (hb : rootInterval.Contains b) : i2262.Contains (n2262 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2213 b hb) (b2189 b hb))
    (by norm_num [i2262, i2213, i2189, RationalInterval.mul]) (by norm_num [i2262, i2213, i2189, RationalInterval.mul])

def n2263 (b : ℝ) : ℝ := (n2255 b) + (n2259 b)
def i2263 : RationalInterval := ⟨(-271503963128391504871006809641 / 1000000000000000000000000000000 : ℚ), (-3393798679067800639226852899 / 12500000000000000000000000000 : ℚ)⟩
theorem b2263 (b : ℝ) (hb : rootInterval.Contains b) : i2263.Contains (n2263 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2255 b hb) (b2259 b hb))
    (by norm_num [i2263, i2255, i2259, RationalInterval.add]) (by norm_num [i2263, i2255, i2259, RationalInterval.add])

def n2264 (b : ℝ) : ℝ := (n2256 b) + (n2260 b)
def i2264 : RationalInterval := ⟨(-570152801117707542995670229 / 2500000000000000000000000000 : ℚ), (-114030543653871102193737221509 / 500000000000000000000000000000 : ℚ)⟩
theorem b2264 (b : ℝ) (hb : rootInterval.Contains b) : i2264.Contains (n2264 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2256 b hb) (b2260 b hb))
    (by norm_num [i2264, i2256, i2260, RationalInterval.add]) (by norm_num [i2264, i2256, i2260, RationalInterval.add])

def n2265 (b : ℝ) : ℝ := (n2257 b) + (n2261 b)
def i2265 : RationalInterval := ⟨(-183621039400176789504924832311 / 1000000000000000000000000000000 : ℚ), (-183621003468938091184913827291 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2265 (b : ℝ) (hb : rootInterval.Contains b) : i2265.Contains (n2265 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2257 b hb) (b2261 b hb))
    (by norm_num [i2265, i2257, i2261, RationalInterval.add]) (by norm_num [i2265, i2257, i2261, RationalInterval.add])

def n2266 (b : ℝ) : ℝ := (n2258 b) + (n2262 b)
def i2266 : RationalInterval := ⟨(-65767034798448085306795791659 / 500000000000000000000000000000 : ℚ), (-26306810496409955128210649189 / 200000000000000000000000000000 : ℚ)⟩
theorem b2266 (b : ℝ) (hb : rootInterval.Contains b) : i2266.Contains (n2266 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2258 b hb) (b2262 b hb))
    (by norm_num [i2266, i2258, i2262, RationalInterval.add]) (by norm_num [i2266, i2258, i2262, RationalInterval.add])

def n2267 (b : ℝ) : ℝ := (n2188 b) * (n2210 b)
def i2267 : RationalInterval := ⟨(-381673057129833003186576938931 / 250000000000000000000000000000 : ℚ), (-763346105502660705767552759559 / 500000000000000000000000000000 : ℚ)⟩
theorem b2267 (b : ℝ) (hb : rootInterval.Contains b) : i2267.Contains (n2267 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2188 b hb) (b2210 b hb))
    (by norm_num [i2267, i2188, i2210, RationalInterval.mul]) (by norm_num [i2267, i2188, i2210, RationalInterval.mul])

def n2268 (b : ℝ) : ℝ := (n2188 b) * (n2213 b)
def i2268 : RationalInterval := ⟨(-90038940982728000433752071081 / 125000000000000000000000000000 : ℚ), (-144062303744464349942761153171 / 200000000000000000000000000000 : ℚ)⟩
theorem b2268 (b : ℝ) (hb : rootInterval.Contains b) : i2268.Contains (n2268 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2188 b hb) (b2213 b hb))
    (by norm_num [i2268, i2188, i2213, RationalInterval.mul]) (by norm_num [i2268, i2188, i2213, RationalInterval.mul])

def n2269 (b : ℝ) : ℝ := (n2189 b) * (n2210 b)
def i2269 : RationalInterval := ⟨(-769093303623190974978470545207 / 1000000000000000000000000000000 : ℚ), (-384546647197151171847669265433 / 500000000000000000000000000000 : ℚ)⟩
theorem b2269 (b : ℝ) (hb : rootInterval.Contains b) : i2269.Contains (n2269 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2189 b hb) (b2210 b hb))
    (by norm_num [i2269, i2189, i2210, RationalInterval.mul]) (by norm_num [i2269, i2189, i2210, RationalInterval.mul])

def n2270 (b : ℝ) : ℝ := (n2189 b) * (n2213 b)
def i2270 : RationalInterval := ⟨(-362867356139229497240987478619 / 1000000000000000000000000000000 : ℚ), (-90716837835884960070881294217 / 250000000000000000000000000000 : ℚ)⟩
theorem b2270 (b : ℝ) (hb : rootInterval.Contains b) : i2270.Contains (n2270 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2189 b hb) (b2213 b hb))
    (by norm_num [i2270, i2189, i2213, RationalInterval.mul]) (by norm_num [i2270, i2189, i2213, RationalInterval.mul])

def n2271 (b : ℝ) : ℝ := (n318 b) * (n2235 b)
def i2271 : RationalInterval := ⟨(1255188265390940507875300946083 / 1000000000000000000000000000000 : ℚ), (627594158339948680198478643599 / 500000000000000000000000000000 : ℚ)⟩
theorem b2271 (b : ℝ) (hb : rootInterval.Contains b) : i2271.Contains (n2271 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b318 b hb) (b2235 b hb))
    (by norm_num [i2271, i318, i2235, RationalInterval.mul]) (by norm_num [i2271, i318, i2235, RationalInterval.mul])

def n2272 (b : ℝ) : ℝ := (n318 b) * (n2238 b)
def i2272 : RationalInterval := ⟨(536690488461647213965091736337 / 1000000000000000000000000000000 : ℚ), (134172628813345914632222984641 / 250000000000000000000000000000 : ℚ)⟩
theorem b2272 (b : ℝ) (hb : rootInterval.Contains b) : i2272.Contains (n2272 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b318 b hb) (b2238 b hb))
    (by norm_num [i2272, i318, i2238, RationalInterval.mul]) (by norm_num [i2272, i318, i2238, RationalInterval.mul])

def n2273 (b : ℝ) : ℝ := (n319 b) * (n2235 b)
def i2273 : RationalInterval := ⟨(541032183176107957780202453607 / 1000000000000000000000000000000 : ℚ), (67629025885820017413483010981 / 125000000000000000000000000000 : ℚ)⟩
theorem b2273 (b : ℝ) (hb : rootInterval.Contains b) : i2273.Contains (n2273 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b319 b hb) (b2235 b hb))
    (by norm_num [i2273, i319, i2235, RationalInterval.mul]) (by norm_num [i2273, i319, i2235, RationalInterval.mul])

def n2274 (b : ℝ) : ℝ := (n319 b) * (n2238 b)
def i2274 : RationalInterval := ⟨(231333286542333326627395895301 / 1000000000000000000000000000000 : ℚ), (231333298861490064642471930923 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2274 (b : ℝ) (hb : rootInterval.Contains b) : i2274.Contains (n2274 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b319 b hb) (b2238 b hb))
    (by norm_num [i2274, i319, i2238, RationalInterval.mul]) (by norm_num [i2274, i319, i2238, RationalInterval.mul])

def n2275 (b : ℝ) : ℝ := (n2267 b) + (n2271 b)
def i2275 : RationalInterval := ⟨(-271503963128391504871006809641 / 1000000000000000000000000000000 : ℚ), (-3393798679067800639226852899 / 12500000000000000000000000000 : ℚ)⟩
theorem b2275 (b : ℝ) (hb : rootInterval.Contains b) : i2275.Contains (n2275 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2267 b hb) (b2271 b hb))
    (by norm_num [i2275, i2267, i2271, RationalInterval.add]) (by norm_num [i2275, i2267, i2271, RationalInterval.add])

def n2276 (b : ℝ) : ℝ := (n2268 b) + (n2272 b)
def i2276 : RationalInterval := ⟨(-183621039400176789504924832311 / 1000000000000000000000000000000 : ℚ), (-183621003468938091184913827291 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2276 (b : ℝ) (hb : rootInterval.Contains b) : i2276.Contains (n2276 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2268 b hb) (b2272 b hb))
    (by norm_num [i2276, i2268, i2272, RationalInterval.add]) (by norm_num [i2276, i2268, i2272, RationalInterval.add])

def n2277 (b : ℝ) : ℝ := (n2269 b) + (n2273 b)
def i2277 : RationalInterval := ⟨(-570152801117707542995670229 / 2500000000000000000000000000 : ℚ), (-114030543653871102193737221509 / 500000000000000000000000000000 : ℚ)⟩
theorem b2277 (b : ℝ) (hb : rootInterval.Contains b) : i2277.Contains (n2277 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2269 b hb) (b2273 b hb))
    (by norm_num [i2277, i2269, i2273, RationalInterval.add]) (by norm_num [i2277, i2269, i2273, RationalInterval.add])

def n2278 (b : ℝ) : ℝ := (n2270 b) + (n2274 b)
def i2278 : RationalInterval := ⟨(-65767034798448085306795791659 / 500000000000000000000000000000 : ℚ), (-26306810496409955128210649189 / 200000000000000000000000000000 : ℚ)⟩
theorem b2278 (b : ℝ) (hb : rootInterval.Contains b) : i2278.Contains (n2278 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2270 b hb) (b2274 b hb))
    (by norm_num [i2278, i2270, i2274, RationalInterval.add]) (by norm_num [i2278, i2270, i2274, RationalInterval.add])

def n2279 (b : ℝ) : ℝ := (n2263 b) + (n2275 b)
def i2279 : RationalInterval := ⟨(-271503963128391504871006809641 / 500000000000000000000000000000 : ℚ), (-3393798679067800639226852899 / 6250000000000000000000000000 : ℚ)⟩
theorem b2279 (b : ℝ) (hb : rootInterval.Contains b) : i2279.Contains (n2279 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2263 b hb) (b2275 b hb))
    (by norm_num [i2279, i2263, i2275, RationalInterval.add]) (by norm_num [i2279, i2263, i2275, RationalInterval.add])

def n2280 (b : ℝ) : ℝ := (n2264 b) + (n2276 b)
def i2280 : RationalInterval := ⟨(-411682159847259806703192923911 / 1000000000000000000000000000000 : ℚ), (-411682090776680295572388270309 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2280 (b : ℝ) (hb : rootInterval.Contains b) : i2280.Contains (n2280 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2264 b hb) (b2276 b hb))
    (by norm_num [i2280, i2264, i2276, RationalInterval.add]) (by norm_num [i2280, i2264, i2276, RationalInterval.add])

def n2281 (b : ℝ) : ℝ := (n2265 b) + (n2277 b)
def i2281 : RationalInterval := ⟨(-411682159847259806703192923911 / 1000000000000000000000000000000 : ℚ), (-411682090776680295572388270309 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2281 (b : ℝ) (hb : rootInterval.Contains b) : i2281.Contains (n2281 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2265 b hb) (b2277 b hb))
    (by norm_num [i2281, i2265, i2277, RationalInterval.add]) (by norm_num [i2281, i2265, i2277, RationalInterval.add])

def n2282 (b : ℝ) : ℝ := (n2266 b) + (n2278 b)
def i2282 : RationalInterval := ⟨(-65767034798448085306795791659 / 250000000000000000000000000000 : ℚ), (-26306810496409955128210649189 / 100000000000000000000000000000 : ℚ)⟩
theorem b2282 (b : ℝ) (hb : rootInterval.Contains b) : i2282.Contains (n2282 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2266 b hb) (b2278 b hb))
    (by norm_num [i2282, i2266, i2278, RationalInterval.add]) (by norm_num [i2282, i2266, i2278, RationalInterval.add])

def n2283 (b : ℝ) : ℝ := 1 / (n335 b)
def i2283 : RationalInterval := ⟨(484244290395409584950985089499 / 1000000000000000000000000000000 : ℚ), (484244296108863732806787716887 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2283 (b : ℝ) (hb : rootInterval.Contains b) : i2283.Contains (n2283 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_inv_of_positive (b335 b hb) (by norm_num [i335]))
    (by norm_num [i2283, i335, RationalInterval.inv]) (by norm_num [i2283, i335, RationalInterval.inv])

def n2284 (b : ℝ) : ℝ := (n16 b) * (n2283 b)
def i2284 : RationalInterval := ⟨(-484244296108863732806787716887 / 1000000000000000000000000000000 : ℚ), (-484244290395409584950985089499 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2284 (b : ℝ) (hb : rootInterval.Contains b) : i2284.Contains (n2284 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b16 b hb) (b2283 b hb))
    (by norm_num [i2284, i16, i2283, RationalInterval.mul]) (by norm_num [i2284, i16, i2283, RationalInterval.mul])

def n2285 (b : ℝ) : ℝ := (n2284 b) * (n2279 b)
def i2285 : RationalInterval := ⟨(131474210647205240760108322409 / 500000000000000000000000000000 : ℚ), (262948491031749673573268840523 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2285 (b : ℝ) (hb : rootInterval.Contains b) : i2285.Contains (n2285 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2284 b hb) (b2279 b hb))
    (by norm_num [i2285, i2284, i2279, RationalInterval.mul]) (by norm_num [i2285, i2284, i2279, RationalInterval.mul])

def n2286 (b : ℝ) : ℝ := (n2284 b) * (n2280 b)
def i2286 : RationalInterval := ⟨(7974188076666085717288088963 / 40000000000000000000000000000 : ℚ), (797418950863252197108068403 / 4000000000000000000000000000 : ℚ)⟩
theorem b2286 (b : ℝ) (hb : rootInterval.Contains b) : i2286.Contains (n2286 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2284 b hb) (b2280 b hb))
    (by norm_num [i2286, i2284, i2280, RationalInterval.mul]) (by norm_num [i2286, i2284, i2280, RationalInterval.mul])

def n2287 (b : ℝ) : ℝ := (n2284 b) * (n2281 b)
def i2287 : RationalInterval := ⟨(7974188076666085717288088963 / 40000000000000000000000000000 : ℚ), (797418950863252197108068403 / 4000000000000000000000000000 : ℚ)⟩
theorem b2287 (b : ℝ) (hb : rootInterval.Contains b) : i2287.Contains (n2287 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2284 b hb) (b2281 b hb))
    (by norm_num [i2287, i2284, i2281, RationalInterval.mul]) (by norm_num [i2287, i2284, i2281, RationalInterval.mul])

def n2288 (b : ℝ) : ℝ := (n2284 b) * (n2282 b)
def i2288 : RationalInterval := ⟨(3184730695350137822440475793 / 25000000000000000000000000000 : ℚ), (15923655736570819932865117187 / 125000000000000000000000000000 : ℚ)⟩
theorem b2288 (b : ℝ) (hb : rootInterval.Contains b) : i2288.Contains (n2288 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2284 b hb) (b2282 b hb))
    (by norm_num [i2288, i2284, i2282, RationalInterval.mul]) (by norm_num [i2288, i2284, i2282, RationalInterval.mul])

def n2289 (b : ℝ) : ℝ := (n335 b) * (n335 b)
def i2289 : RationalInterval := ⟨(533066002435582210089692317407 / 125000000000000000000000000000 : ℚ), (170581124804658002292414598671 / 40000000000000000000000000000 : ℚ)⟩
theorem b2289 (b : ℝ) (hb : rootInterval.Contains b) : i2289.Contains (n2289 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b335 b hb) (b335 b hb))
    (by norm_num [i2289, i335, i335, RationalInterval.mul]) (by norm_num [i2289, i335, i335, RationalInterval.mul])

def n2290 (b : ℝ) : ℝ := 1 / (n2289 b)
def i2290 : RationalInterval := ⟨(234492532780553767603917658801 / 1000000000000000000000000000000 : ℚ), (234492538313968899317761356291 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2290 (b : ℝ) (hb : rootInterval.Contains b) : i2290.Contains (n2290 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_inv_of_positive (b2289 b hb) (by norm_num [i2289]))
    (by norm_num [i2290, i2289, RationalInterval.inv]) (by norm_num [i2290, i2289, RationalInterval.inv])

def n2291 (b : ℝ) : ℝ := (n2207 b) * (n2290 b)
def i2291 : RationalInterval := ⟨(-1524857255122435218031714081 / 125000000000000000000000000000 : ℚ), (-12198848781399300798324917177 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2291 (b : ℝ) (hb : rootInterval.Contains b) : i2291.Contains (n2291 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2207 b hb) (b2290 b hb))
    (by norm_num [i2291, i2207, i2290, RationalInterval.mul]) (by norm_num [i2291, i2207, i2290, RationalInterval.mul])

def n2292 (b : ℝ) : ℝ := (n2291 b) * (n2225 b)
def i2292 : RationalInterval := ⟨(-25774355652232492940853697577 / 250000000000000000000000000000 : ℚ), (-12887167910867644591784603851 / 125000000000000000000000000000 : ℚ)⟩
theorem b2292 (b : ℝ) (hb : rootInterval.Contains b) : i2292.Contains (n2292 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2291 b hb) (b2225 b hb))
    (by norm_num [i2292, i2291, i2225, RationalInterval.mul]) (by norm_num [i2292, i2291, i2225, RationalInterval.mul])

def n2293 (b : ℝ) : ℝ := (n2291 b) * (n2226 b)
def i2293 : RationalInterval := ⟨(-46540679775418945651956354331 / 1000000000000000000000000000000 : ℚ), (-23270321931957618827312691847 / 500000000000000000000000000000 : ℚ)⟩
theorem b2293 (b : ℝ) (hb : rootInterval.Contains b) : i2293.Contains (n2293 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2291 b hb) (b2226 b hb))
    (by norm_num [i2293, i2291, i2226, RationalInterval.mul]) (by norm_num [i2293, i2291, i2226, RationalInterval.mul])

def n2294 (b : ℝ) : ℝ := (n2291 b) * (n2227 b)
def i2294 : RationalInterval := ⟨(-46540679775418945651956354331 / 1000000000000000000000000000000 : ℚ), (-23270321931957618827312691847 / 500000000000000000000000000000 : ℚ)⟩
theorem b2294 (b : ℝ) (hb : rootInterval.Contains b) : i2294.Contains (n2294 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2291 b hb) (b2227 b hb))
    (by norm_num [i2294, i2291, i2227, RationalInterval.mul]) (by norm_num [i2294, i2291, i2227, RationalInterval.mul])

def n2295 (b : ℝ) : ℝ := (n2291 b) * (n2228 b)
def i2295 : RationalInterval := ⟨(-10483369993789293548025511219 / 500000000000000000000000000000 : ℚ), (-524168094015734570256310911 / 25000000000000000000000000000 : ℚ)⟩
theorem b2295 (b : ℝ) (hb : rootInterval.Contains b) : i2295.Contains (n2295 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2291 b hb) (b2228 b hb))
    (by norm_num [i2295, i2291, i2228, RationalInterval.mul]) (by norm_num [i2295, i2291, i2228, RationalInterval.mul])

def n2296 (b : ℝ) : ℝ := (n2285 b) + (n2292 b)
def i2296 : RationalInterval := ⟨(15985099868548050975680185451 / 100000000000000000000000000000 : ℚ), (31970229548961703367798401943 / 200000000000000000000000000000 : ℚ)⟩
theorem b2296 (b : ℝ) (hb : rootInterval.Contains b) : i2296.Contains (n2296 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2285 b hb) (b2292 b hb))
    (by norm_num [i2296, i2285, i2292, RationalInterval.add]) (by norm_num [i2296, i2285, i2292, RationalInterval.add])

def n2297 (b : ℝ) : ℝ := (n2286 b) + (n2293 b)
def i2297 : RationalInterval := ⟨(9550876383827074830015366859 / 62500000000000000000000000000 : ℚ), (2387720216435903306599870579 / 15625000000000000000000000000 : ℚ)⟩
theorem b2297 (b : ℝ) (hb : rootInterval.Contains b) : i2297.Contains (n2297 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2286 b hb) (b2293 b hb))
    (by norm_num [i2297, i2286, i2293, RationalInterval.add]) (by norm_num [i2297, i2286, i2293, RationalInterval.add])

def n2298 (b : ℝ) : ℝ := (n2287 b) + (n2294 b)
def i2298 : RationalInterval := ⟨(9550876383827074830015366859 / 62500000000000000000000000000 : ℚ), (2387720216435903306599870579 / 15625000000000000000000000000 : ℚ)⟩
theorem b2298 (b : ℝ) (hb : rootInterval.Contains b) : i2298.Contains (n2298 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2287 b hb) (b2294 b hb))
    (by norm_num [i2298, i2287, i2294, RationalInterval.add]) (by norm_num [i2298, i2287, i2294, RationalInterval.add])

def n2299 (b : ℝ) : ℝ := (n2288 b) + (n2295 b)
def i2299 : RationalInterval := ⟨(53211243913213462900784004641 / 500000000000000000000000000000 : ℚ), (1662851908311518385197945329 / 15625000000000000000000000000 : ℚ)⟩
theorem b2299 (b : ℝ) (hb : rootInterval.Contains b) : i2299.Contains (n2299 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2288 b hb) (b2295 b hb))
    (by norm_num [i2299, i2288, i2295, RationalInterval.add]) (by norm_num [i2299, i2288, i2295, RationalInterval.add])

def n2300 (b : ℝ) : ℝ := (n2207 b) + (n2242 b)
def i2300 : RationalInterval := ⟨(327709302951906828857061676899 / 100000000000000000000000000000 : ℚ), (819273297422952654867731894849 / 250000000000000000000000000000 : ℚ)⟩
theorem b2300 (b : ℝ) (hb : rootInterval.Contains b) : i2300.Contains (n2300 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2207 b hb) (b2242 b hb))
    (by norm_num [i2300, i2207, i2242, RationalInterval.add]) (by norm_num [i2300, i2207, i2242, RationalInterval.add])

def n2301 (b : ℝ) : ℝ := (n2300 b) * (n2290 b)
def i2301 : RationalInterval := ⟨(192113461162356094061868971999 / 250000000000000000000000000000 : ℚ), (192113475085563362926089882867 / 250000000000000000000000000000 : ℚ)⟩
theorem b2301 (b : ℝ) (hb : rootInterval.Contains b) : i2301.Contains (n2301 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2300 b hb) (b2290 b hb))
    (by norm_num [i2301, i2300, i2290, RationalInterval.mul]) (by norm_num [i2301, i2300, i2290, RationalInterval.mul])

def n2302 (b : ℝ) : ℝ := (n335 b) + (n2216 b)
def i2302 : RationalInterval := ⟨(939094742213725944200025936443 / 125000000000000000000000000000 : ℚ), (1502551599255637562128593692971 / 200000000000000000000000000000 : ℚ)⟩
theorem b2302 (b : ℝ) (hb : rootInterval.Contains b) : i2302.Contains (n2302 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b335 b hb) (b2216 b hb))
    (by norm_num [i2302, i335, i2216, RationalInterval.add]) (by norm_num [i2302, i335, i2216, RationalInterval.add])

def n2303 (b : ℝ) : ℝ := (n2302 b) * (n13 b)
def i2303 : RationalInterval := ⟨(939094742213725944200025936443 / 62500000000000000000000000000 : ℚ), (1502551599255637562128593692971 / 100000000000000000000000000000 : ℚ)⟩
theorem b2303 (b : ℝ) (hb : rootInterval.Contains b) : i2303.Contains (n2303 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2302 b hb) (b13 b hb))
    (by norm_num [i2303, i2302, i13, RationalInterval.mul]) (by norm_num [i2303, i2302, i13, RationalInterval.mul])

def n2304 (b : ℝ) : ℝ := (n2303 b) * (n2207 b)
def i2304 : RationalInterval := ⟨(-781662981276804107279384008419 / 1000000000000000000000000000000 : ℚ), (-390831200152312075648881816351 / 500000000000000000000000000000 : ℚ)⟩
theorem b2304 (b : ℝ) (hb : rootInterval.Contains b) : i2304.Contains (n2304 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2303 b hb) (b2207 b hb))
    (by norm_num [i2304, i2303, i2207, RationalInterval.mul]) (by norm_num [i2304, i2303, i2207, RationalInterval.mul])

def n2305 (b : ℝ) : ℝ := (n2289 b) * (n335 b)
def i2305 : RationalInterval := ⟨(1761312648905602114813207289059 / 200000000000000000000000000000 : ℚ), (110082044453075802315878559299 / 12500000000000000000000000000 : ℚ)⟩
theorem b2305 (b : ℝ) (hb : rootInterval.Contains b) : i2305.Contains (n2305 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2289 b hb) (b335 b hb))
    (by norm_num [i2305, i2289, i335, RationalInterval.mul]) (by norm_num [i2305, i2289, i335, RationalInterval.mul])

def n2306 (b : ℝ) : ℝ := 1 / (n2305 b)
def i2306 : RationalInterval := ⟨(28387917534835395015262034679 / 250000000000000000000000000000 : ℚ), (56775837079314314826110784999 / 500000000000000000000000000000 : ℚ)⟩
theorem b2306 (b : ℝ) (hb : rootInterval.Contains b) : i2306.Contains (n2306 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_inv_of_positive (b2305 b hb) (by norm_num [i2305]))
    (by norm_num [i2306, i2305, RationalInterval.inv]) (by norm_num [i2306, i2305, RationalInterval.inv])

def n2307 (b : ℝ) : ℝ := (n2304 b) * (n2306 b)
def i2307 : RationalInterval := ⟨(-44379570075902945660729600871 / 500000000000000000000000000000 : ℚ), (-88759071039716655034951572949 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2307 (b : ℝ) (hb : rootInterval.Contains b) : i2307.Contains (n2307 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2304 b hb) (b2306 b hb))
    (by norm_num [i2307, i2304, i2306, RationalInterval.mul]) (by norm_num [i2307, i2304, i2306, RationalInterval.mul])

def n2308 (b : ℝ) : ℝ := -(n2307 b)
def i2308 : RationalInterval := ⟨(88759071039716655034951572949 / 1000000000000000000000000000000 : ℚ), (44379570075902945660729600871 / 500000000000000000000000000000 : ℚ)⟩
theorem b2308 (b : ℝ) (hb : rootInterval.Contains b) : i2308.Contains (n2308 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b2307 b hb))
    (by norm_num [i2308, i2307, RationalInterval.neg]) (by norm_num [i2308, i2307, RationalInterval.neg])

def n2309 (b : ℝ) : ℝ := (n2301 b) + (n2308 b)
def i2309 : RationalInterval := ⟨(171442583137828206256485492189 / 200000000000000000000000000000 : ℚ), (85721304049405934302581873321 / 100000000000000000000000000000 : ℚ)⟩
theorem b2309 (b : ℝ) (hb : rootInterval.Contains b) : i2309.Contains (n2309 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2301 b hb) (b2308 b hb))
    (by norm_num [i2309, i2301, i2308, RationalInterval.add]) (by norm_num [i2309, i2301, i2308, RationalInterval.add])

def n2310 (b : ℝ) : ℝ := (n2309 b) * (n2229 b)
def i2310 : RationalInterval := ⟨(133777107850580419485537018437 / 100000000000000000000000000000 : ℚ), (668885645819579276203654663333 / 500000000000000000000000000000 : ℚ)⟩
theorem b2310 (b : ℝ) (hb : rootInterval.Contains b) : i2310.Contains (n2310 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2309 b hb) (b2229 b hb))
    (by norm_num [i2310, i2309, i2229, RationalInterval.mul]) (by norm_num [i2310, i2309, i2229, RationalInterval.mul])

def n2311 (b : ℝ) : ℝ := (n2309 b) * (n2230 b)
def i2311 : RationalInterval := ⟨(36039275299890189824386852707 / 62500000000000000000000000000 : ℚ), (576628498588194374555048520369 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2311 (b : ℝ) (hb : rootInterval.Contains b) : i2311.Contains (n2311 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2309 b hb) (b2230 b hb))
    (by norm_num [i2311, i2309, i2230, RationalInterval.mul]) (by norm_num [i2311, i2309, i2230, RationalInterval.mul])

def n2312 (b : ℝ) : ℝ := (n2309 b) * (n2231 b)
def i2312 : RationalInterval := ⟨(36039275299890189824386852707 / 62500000000000000000000000000 : ℚ), (576628498588194374555048520369 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2312 (b : ℝ) (hb : rootInterval.Contains b) : i2312.Contains (n2312 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2309 b hb) (b2231 b hb))
    (by norm_num [i2312, i2309, i2231, RationalInterval.mul]) (by norm_num [i2312, i2309, i2231, RationalInterval.mul])

def n2313 (b : ℝ) : ℝ := (n2309 b) * (n2232 b)
def i2313 : RationalInterval := ⟨(248547993421674060156208318249 / 1000000000000000000000000000000 : ℚ), (124274017338444168989744393041 / 500000000000000000000000000000 : ℚ)⟩
theorem b2313 (b : ℝ) (hb : rootInterval.Contains b) : i2313.Contains (n2313 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2309 b hb) (b2232 b hb))
    (by norm_num [i2313, i2309, i2232, RationalInterval.mul]) (by norm_num [i2313, i2309, i2232, RationalInterval.mul])

def n2314 (b : ℝ) : ℝ := (n2296 b) + (n2310 b)
def i2314 : RationalInterval := ⟨(9360137982445529403826075243 / 6250000000000000000000000000 : ℚ), (1497622439383967069246301336381 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2314 (b : ℝ) (hb : rootInterval.Contains b) : i2314.Contains (n2314 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2296 b hb) (b2310 b hb))
    (by norm_num [i2314, i2296, i2310, RationalInterval.add]) (by norm_num [i2314, i2296, i2310, RationalInterval.add])

def n2315 (b : ℝ) : ℝ := (n2297 b) + (n2311 b)
def i2315 : RationalInterval := ⟨(22795075841858632327201109783 / 31250000000000000000000000000 : ℚ), (29177703697603687447097609497 / 40000000000000000000000000000 : ℚ)⟩
theorem b2315 (b : ℝ) (hb : rootInterval.Contains b) : i2315.Contains (n2315 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2297 b hb) (b2311 b hb))
    (by norm_num [i2315, i2297, i2311, RationalInterval.add]) (by norm_num [i2315, i2297, i2311, RationalInterval.add])

def n2316 (b : ℝ) : ℝ := (n2298 b) + (n2312 b)
def i2316 : RationalInterval := ⟨(22795075841858632327201109783 / 31250000000000000000000000000 : ℚ), (29177703697603687447097609497 / 40000000000000000000000000000 : ℚ)⟩
theorem b2316 (b : ℝ) (hb : rootInterval.Contains b) : i2316.Contains (n2316 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2298 b hb) (b2312 b hb))
    (by norm_num [i2316, i2298, i2312, RationalInterval.add]) (by norm_num [i2316, i2298, i2312, RationalInterval.add])

def n2317 (b : ℝ) : ℝ := (n2299 b) + (n2313 b)
def i2317 : RationalInterval := ⟨(354970481248100985957776327531 / 1000000000000000000000000000000 : ℚ), (177485278404412757316078643569 / 500000000000000000000000000000 : ℚ)⟩
theorem b2317 (b : ℝ) (hb : rootInterval.Contains b) : i2317.Contains (n2317 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2299 b hb) (b2313 b hb))
    (by norm_num [i2317, i2299, i2313, RationalInterval.add]) (by norm_num [i2317, i2299, i2313, RationalInterval.add])

def n2318 (b : ℝ) : ℝ := (n2302 b) * (n2290 b)
def i2318 : RationalInterval := ⟨(352337127396156513570413438821 / 200000000000000000000000000000 : ℚ), (352337138457167834538101196437 / 200000000000000000000000000000 : ℚ)⟩
theorem b2318 (b : ℝ) (hb : rootInterval.Contains b) : i2318.Contains (n2318 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2302 b hb) (b2290 b hb))
    (by norm_num [i2318, i2302, i2290, RationalInterval.mul]) (by norm_num [i2318, i2302, i2290, RationalInterval.mul])

def n2319 (b : ℝ) : ℝ := (n2318 b) * (n2251 b)
def i2319 : RationalInterval := ⟨(-1986572344089591111196795321187 / 1000000000000000000000000000000 : ℚ), (-1986572252199909899348337095933 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2319 (b : ℝ) (hb : rootInterval.Contains b) : i2319.Contains (n2319 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2318 b hb) (b2251 b hb))
    (by norm_num [i2319, i2318, i2251, RationalInterval.mul]) (by norm_num [i2319, i2318, i2251, RationalInterval.mul])

def n2320 (b : ℝ) : ℝ := (n2318 b) * (n2252 b)
def i2320 : RationalInterval := ⟨(-928525059195717617542156251881 / 1000000000000000000000000000000 : ℚ), (-116065626819436471768859120013 / 125000000000000000000000000000 : ℚ)⟩
theorem b2320 (b : ℝ) (hb : rootInterval.Contains b) : i2320.Contains (n2320 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2318 b hb) (b2252 b hb))
    (by norm_num [i2320, i2318, i2252, RationalInterval.mul]) (by norm_num [i2320, i2318, i2252, RationalInterval.mul])

def n2321 (b : ℝ) : ℝ := (n2318 b) * (n2253 b)
def i2321 : RationalInterval := ⟨(-928525059195717617542156251881 / 1000000000000000000000000000000 : ℚ), (-116065626819436471768859120013 / 125000000000000000000000000000 : ℚ)⟩
theorem b2321 (b : ℝ) (hb : rootInterval.Contains b) : i2321.Contains (n2321 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2318 b hb) (b2253 b hb))
    (by norm_num [i2321, i2318, i2253, RationalInterval.mul]) (by norm_num [i2321, i2318, i2253, RationalInterval.mul])

def n2322 (b : ℝ) : ℝ := (n2318 b) * (n2254 b)
def i2322 : RationalInterval := ⟨(-21568311912160904840496834189 / 50000000000000000000000000000 : ℚ), (-431366216624954548650155286209 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2322 (b : ℝ) (hb : rootInterval.Contains b) : i2322.Contains (n2322 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2318 b hb) (b2254 b hb))
    (by norm_num [i2322, i2318, i2254, RationalInterval.mul]) (by norm_num [i2322, i2318, i2254, RationalInterval.mul])

def n2323 (b : ℝ) : ℝ := (n2314 b) + (n2319 b)
def i2323 : RationalInterval := ⟨(-488950266898306406584623282307 / 1000000000000000000000000000000 : ℚ), (-7639840825249106720344308743 / 15625000000000000000000000000 : ℚ)⟩
theorem b2323 (b : ℝ) (hb : rootInterval.Contains b) : i2323.Contains (n2323 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2314 b hb) (b2319 b hb))
    (by norm_num [i2323, i2314, i2319, RationalInterval.add]) (by norm_num [i2323, i2314, i2319, RationalInterval.add])

def n2324 (b : ℝ) : ℝ := (n2315 b) + (n2320 b)
def i2324 : RationalInterval := ⟨(-7963305290249655322868829553 / 40000000000000000000000000000 : ℚ), (-199082422115399587973432722679 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2324 (b : ℝ) (hb : rootInterval.Contains b) : i2324.Contains (n2324 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2315 b hb) (b2320 b hb))
    (by norm_num [i2324, i2315, i2320, RationalInterval.add]) (by norm_num [i2324, i2315, i2320, RationalInterval.add])

def n2325 (b : ℝ) : ℝ := (n2316 b) + (n2321 b)
def i2325 : RationalInterval := ⟨(-7963305290249655322868829553 / 40000000000000000000000000000 : ℚ), (-199082422115399587973432722679 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2325 (b : ℝ) (hb : rootInterval.Contains b) : i2325.Contains (n2325 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2316 b hb) (b2321 b hb))
    (by norm_num [i2325, i2316, i2321, RationalInterval.add]) (by norm_num [i2325, i2316, i2321, RationalInterval.add])

def n2326 (b : ℝ) : ℝ := (n2317 b) + (n2322 b)
def i2326 : RationalInterval := ⟨(-76395756995117110852160356249 / 1000000000000000000000000000000 : ℚ), (-76395659816129034017997999071 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2326 (b : ℝ) (hb : rootInterval.Contains b) : i2326.Contains (n2326 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2317 b hb) (b2322 b hb))
    (by norm_num [i2326, i2317, i2322, RationalInterval.add]) (by norm_num [i2326, i2317, i2322, RationalInterval.add])

def n2327 (b : ℝ) : ℝ := (n118 b) * (n225 b)
def i2327 : RationalInterval := ⟨(100501173458158331797210006903 / 1000000000000000000000000000000 : ℚ), (100501174607992216623927100981 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2327 (b : ℝ) (hb : rootInterval.Contains b) : i2327.Contains (n2327 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b118 b hb) (b225 b hb))
    (by norm_num [i2327, i118, i225, RationalInterval.mul]) (by norm_num [i2327, i118, i225, RationalInterval.mul])

def n2328 (b : ℝ) : ℝ := (n119 b) * (n227 b)
def i2328 : RationalInterval := ⟨(6234708432789057504057004047 / 500000000000000000000000000000 : ℚ), (1558677135786844470513179851 / 125000000000000000000000000000 : ℚ)⟩
theorem b2328 (b : ℝ) (hb : rootInterval.Contains b) : i2328.Contains (n2328 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b119 b hb) (b227 b hb))
    (by norm_num [i2328, i119, i227, RationalInterval.mul]) (by norm_num [i2328, i119, i227, RationalInterval.mul])

def n2329 (b : ℝ) : ℝ := (n2327 b) + (n2328 b)
def i2329 : RationalInterval := ⟨(112970590323736446805324014997 / 1000000000000000000000000000000 : ℚ), (112970591694286972388032539789 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2329 (b : ℝ) (hb : rootInterval.Contains b) : i2329.Contains (n2329 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2327 b hb) (b2328 b hb))
    (by norm_num [i2329, i2327, i2328, RationalInterval.add]) (by norm_num [i2329, i2327, i2328, RationalInterval.add])

def n2330 (b : ℝ) : ℝ := (n120 b) * (n225 b)
def i2330 : RationalInterval := ⟨(24908648161004821367397310663 / 500000000000000000000000000000 : ℚ), (24908648455892743294120353017 / 500000000000000000000000000000 : ℚ)⟩
theorem b2330 (b : ℝ) (hb : rootInterval.Contains b) : i2330.Contains (n2330 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b120 b hb) (b225 b hb))
    (by norm_num [i2330, i120, i225, RationalInterval.mul]) (by norm_num [i2330, i120, i225, RationalInterval.mul])

def n2331 (b : ℝ) : ℝ := (n121 b) * (n227 b)
def i2331 : RationalInterval := ⟨(7093273375950723837480688667 / 1000000000000000000000000000000 : ℚ), (110832398541387220194724513 / 15625000000000000000000000000 : ℚ)⟩
theorem b2331 (b : ℝ) (hb : rootInterval.Contains b) : i2331.Contains (n2331 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b121 b hb) (b227 b hb))
    (by norm_num [i2331, i121, i227, RationalInterval.mul]) (by norm_num [i2331, i121, i227, RationalInterval.mul])

def n2332 (b : ℝ) : ℝ := (n2330 b) + (n2331 b)
def i2332 : RationalInterval := ⟨(56910569697960366572275309993 / 1000000000000000000000000000000 : ℚ), (28455285209217134340351537433 / 500000000000000000000000000000 : ℚ)⟩
theorem b2332 (b : ℝ) (hb : rootInterval.Contains b) : i2332.Contains (n2332 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2330 b hb) (b2331 b hb))
    (by norm_num [i2332, i2330, i2331, RationalInterval.add]) (by norm_num [i2332, i2330, i2331, RationalInterval.add])

def n2333 (b : ℝ) : ℝ := -(n2329 b)
def i2333 : RationalInterval := ⟨(-112970591694286972388032539789 / 1000000000000000000000000000000 : ℚ), (-112970590323736446805324014997 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2333 (b : ℝ) (hb : rootInterval.Contains b) : i2333.Contains (n2333 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b2329 b hb))
    (by norm_num [i2333, i2329, RationalInterval.neg]) (by norm_num [i2333, i2329, RationalInterval.neg])

def n2334 (b : ℝ) : ℝ := -(n2332 b)
def i2334 : RationalInterval := ⟨(-28455285209217134340351537433 / 500000000000000000000000000000 : ℚ), (-56910569697960366572275309993 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2334 (b : ℝ) (hb : rootInterval.Contains b) : i2334.Contains (n2334 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b2332 b hb))
    (by norm_num [i2334, i2332, RationalInterval.neg]) (by norm_num [i2334, i2332, RationalInterval.neg])

def n2335 (b : ℝ) : ℝ := (n2334 b) + (n15 b)
def i2335 : RationalInterval := ⟨(471544714790782865659648462567 / 500000000000000000000000000000 : ℚ), (943089430302039633427724690007 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2335 (b : ℝ) (hb : rootInterval.Contains b) : i2335.Contains (n2335 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2334 b hb) (b15 b hb))
    (by norm_num [i2335, i2334, i15, RationalInterval.add]) (by norm_num [i2335, i2334, i15, RationalInterval.add])

def n2336 (b : ℝ) : ℝ := (n229 b) * (n2333 b)
def i2336 : RationalInterval := ⟨(-85856758440749261703456264171 / 500000000000000000000000000000 : ℚ), (-171713514693787053364923723973 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2336 (b : ℝ) (hb : rootInterval.Contains b) : i2336.Contains (n2336 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b229 b hb) (b2333 b hb))
    (by norm_num [i2336, i229, i2333, RationalInterval.mul]) (by norm_num [i2336, i229, i2333, RationalInterval.mul])

def n2337 (b : ℝ) : ℝ := (n230 b) * (n2335 b)
def i2337 : RationalInterval := ⟨(-1093632066917192544015663860433 / 1000000000000000000000000000000 : ℚ), (-1093632065184073894026092133407 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2337 (b : ℝ) (hb : rootInterval.Contains b) : i2337.Contains (n2337 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b230 b hb) (b2335 b hb))
    (by norm_num [i2337, i230, i2335, RationalInterval.mul]) (by norm_num [i2337, i230, i2335, RationalInterval.mul])

def n2338 (b : ℝ) : ℝ := (n2336 b) + (n2337 b)
def i2338 : RationalInterval := ⟨(-50613823351947642696903055551 / 40000000000000000000000000000 : ℚ), (-63267278993893047369550792869 / 50000000000000000000000000000 : ℚ)⟩
theorem b2338 (b : ℝ) (hb : rootInterval.Contains b) : i2338.Contains (n2338 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2336 b hb) (b2337 b hb))
    (by norm_num [i2338, i2336, i2337, RationalInterval.add]) (by norm_num [i2338, i2336, i2337, RationalInterval.add])

def n2339 (b : ℝ) : ℝ := (n231 b) * (n2333 b)
def i2339 : RationalInterval := ⟨(65501879315744376036626784517 / 500000000000000000000000000000 : ℚ), (2620075206566846129479382707 / 20000000000000000000000000000 : ℚ)⟩
theorem b2339 (b : ℝ) (hb : rootInterval.Contains b) : i2339.Contains (n2339 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b231 b hb) (b2333 b hb))
    (by norm_num [i2339, i231, i2333, RationalInterval.mul]) (by norm_num [i2339, i231, i2333, RationalInterval.mul])

