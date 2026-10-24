import BFGS.Counterexample.DerivativeCore
import BFGS.Counterexample.TraceBridge
import BFGS.Counterexample.Certificates.IntervalTrace35

namespace BFGS.Counterexample
noncomputable section
open BFGS.Algorithm Trace
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

theorem jacobian3_column0 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    expandedStep (traceMetric b 3) (traceGradient b 3) (traceGradient b 4)
      (symmetricMap (traceHessian b 3)) (symmetricMap (traceHessian b 4))
      ![1,0,0,0,0] = ![n2190 b,n2189 b,n2323 b,n2324 b,n2326 b] := by
  have hs92 : n92 b = n91 b := by rw [trace_n92 b hb hp,trace_n91 b hb hp]
  have hs120 : n120 b = n119 b := by rw [trace_n120 b hb hp,trace_n119 b hb hp]
  have hs184 : n184 b = n183 b := by rw [trace_n184 b hb hp,trace_n183 b hb hp]
  have hs198 : n198 b = n197 b := by rw [trace_n198 b hb hp,trace_n197 b hb hp]
  have hs212 : n212 b = n211 b := by rw [trace_n212 b hb hp,trace_n211 b hb hp]
  have hs226 : n226 b = n225 b := by rw [trace_n226 b hb hp,trace_n225 b hb hp]
  have hs231 : n231 b = n230 b := by rw [trace_n231 b hb hp,trace_n230 b hb hp]
  ext i
  fin_cases i <;>
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail, expandedStep, expandedUpdate, traceMetric, traceGradient, traceHessian, addSym, outerSym, crossSym, pack, point, metric, Sym2.mulV, Sym2.scale, dot, symmetricMap_apply, div_eq_mul_inv, mul_inv_rev, n13, n15, n16, n64, n66, n122, n233, n312, n313, n314, n315, n316, n317, n318, n319, n330, n331, n332, n333, n334, n335, n2182, n2183, n2184, n2185, n2186, n2187, n2188, n2189, n2190, n2191, n2192, n2193, n2194, n2195, n2196, n2197, n2198, n2199, n2200, n2201, n2202, n2203, n2204, n2205, n2206, n2207, n2208, n2209, n2210, n2211, n2212, n2213, n2214, n2215, n2216, n2217, n2218, n2220, n2221, n2222, n2224, n2225, n2226, n2228, n2229, n2230, n2232, n2233, n2234, n2235, n2236, n2237, n2238, n2239, n2240, n2241, n2242, n2243, n2244, n2246, n2247, n2248, n2250, n2251, n2252, n2254, n2255, n2256, n2258, n2259, n2260, n2262, n2263, n2264, n2266, n2267, n2268, n2270, n2271, n2272, n2274, n2275, n2276, n2278, n2279, n2280, n2282, n2283, n2284, n2285, n2286, n2288, n2289, n2290, n2291, n2292, n2293, n2295, n2296, n2297, n2299, n2300, n2301, n2302, n2303, n2304, n2305, n2306, n2307, n2308, n2309, n2310, n2311, n2313, n2314, n2315, n2317, n2318, n2319, n2320, n2322, n2323, n2324, n2326, hs92, hs120, hs184, hs198, hs212, hs226, hs231] <;> ring <;> try simp only [true_or,or_true]

theorem jacobian3_column1 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    expandedStep (traceMetric b 3) (traceGradient b 3) (traceGradient b 4)
      (symmetricMap (traceHessian b 3)) (symmetricMap (traceHessian b 4))
      ![0,1,0,0,0] = ![n2333 b,n2335 b,n2434 b,n2435 b,n2437 b] := by
  have hs92 : n92 b = n91 b := by rw [trace_n92 b hb hp,trace_n91 b hb hp]
  have hs120 : n120 b = n119 b := by rw [trace_n120 b hb hp,trace_n119 b hb hp]
  have hs184 : n184 b = n183 b := by rw [trace_n184 b hb hp,trace_n183 b hb hp]
  have hs198 : n198 b = n197 b := by rw [trace_n198 b hb hp,trace_n197 b hb hp]
  have hs212 : n212 b = n211 b := by rw [trace_n212 b hb hp,trace_n211 b hb hp]
  have hs226 : n226 b = n225 b := by rw [trace_n226 b hb hp,trace_n225 b hb hp]
  have hs231 : n231 b = n230 b := by rw [trace_n231 b hb hp,trace_n230 b hb hp]
  ext i
  fin_cases i <;>
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail, expandedStep, expandedUpdate, traceMetric, traceGradient, traceHessian, addSym, outerSym, crossSym, pack, point, metric, Sym2.mulV, Sym2.scale, dot, symmetricMap_apply, div_eq_mul_inv, mul_inv_rev, n13, n15, n16, n64, n66, n122, n233, n312, n313, n314, n315, n316, n317, n318, n319, n330, n331, n332, n333, n334, n335, n2208, n2209, n2210, n2211, n2212, n2213, n2214, n2215, n2216, n2217, n2218, n2220, n2221, n2222, n2224, n2225, n2226, n2228, n2229, n2230, n2232, n2283, n2284, n2289, n2290, n2302, n2303, n2305, n2306, n2318, n2327, n2328, n2329, n2330, n2331, n2332, n2333, n2334, n2335, n2336, n2337, n2338, n2339, n2340, n2341, n2342, n2343, n2344, n2345, n2346, n2347, n2348, n2349, n2350, n2351, n2352, n2353, n2354, n2355, n2356, n2357, n2358, n2359, n2360, n2361, n2362, n2363, n2364, n2366, n2367, n2368, n2370, n2371, n2372, n2374, n2375, n2376, n2378, n2379, n2380, n2382, n2383, n2384, n2386, n2387, n2388, n2390, n2391, n2392, n2394, n2395, n2396, n2398, n2399, n2400, n2402, n2403, n2404, n2406, n2407, n2408, n2409, n2411, n2412, n2413, n2415, n2416, n2417, n2418, n2419, n2420, n2421, n2422, n2423, n2425, n2426, n2427, n2429, n2430, n2431, n2433, n2434, n2435, n2437, hs92, hs120, hs184, hs198, hs212, hs226, hs231] <;> ring <;> try simp only [true_or,or_true]

theorem jacobian3_column2 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    expandedStep (traceMetric b 3) (traceGradient b 3) (traceGradient b 4)
      (symmetricMap (traceHessian b 3)) (symmetricMap (traceHessian b 4))
      ![0,0,1,0,0] = ![n330 b,n66 b,n2514 b,n2515 b,n2510 b] := by
  have hs92 : n92 b = n91 b := by rw [trace_n92 b hb hp,trace_n91 b hb hp]
  have hs120 : n120 b = n119 b := by rw [trace_n120 b hb hp,trace_n119 b hb hp]
  have hs184 : n184 b = n183 b := by rw [trace_n184 b hb hp,trace_n183 b hb hp]
  have hs198 : n198 b = n197 b := by rw [trace_n198 b hb hp,trace_n197 b hb hp]
  have hs212 : n212 b = n211 b := by rw [trace_n212 b hb hp,trace_n211 b hb hp]
  have hs226 : n226 b = n225 b := by rw [trace_n226 b hb hp,trace_n225 b hb hp]
  have hs231 : n231 b = n230 b := by rw [trace_n231 b hb hp,trace_n230 b hb hp]
  ext i
  fin_cases i <;>
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail, expandedStep, expandedUpdate, traceMetric, traceGradient, traceHessian, addSym, outerSym, crossSym, pack, point, metric, Sym2.mulV, Sym2.scale, dot, symmetricMap_apply, div_eq_mul_inv, mul_inv_rev, n13, n15, n16, n64, n66, n122, n233, n312, n313, n314, n315, n316, n317, n318, n319, n330, n331, n332, n333, n334, n335, n2208, n2209, n2210, n2211, n2212, n2213, n2214, n2215, n2216, n2217, n2218, n2220, n2221, n2222, n2224, n2225, n2226, n2228, n2229, n2230, n2232, n2283, n2284, n2289, n2290, n2302, n2303, n2305, n2306, n2318, n2438, n2439, n2440, n2441, n2442, n2443, n2444, n2445, n2446, n2447, n2448, n2449, n2450, n2451, n2452, n2453, n2454, n2455, n2456, n2457, n2458, n2459, n2460, n2462, n2463, n2464, n2466, n2467, n2469, n2471, n2472, n2473, n2474, n2476, n2477, n2478, n2479, n2480, n2482, n2483, n2484, n2486, n2487, n2488, n2489, n2490, n2492, n2493, n2494, n2496, n2497, n2498, n2499, n2500, n2501, n2502, n2503, n2504, n2506, n2507, n2508, n2510, n2511, n2512, n2514, n2515, hs92, hs120, hs184, hs198, hs212, hs226, hs231] <;> ring <;> try simp only [true_or,or_true]

theorem jacobian3_column3 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    expandedStep (traceMetric b 3) (traceGradient b 3) (traceGradient b 4)
      (symmetricMap (traceHessian b 3)) (symmetricMap (traceHessian b 4))
      ![0,0,0,1,0] = ![n331 b,n330 b,n2608 b,n2609 b,n2611 b] := by
  have hs92 : n92 b = n91 b := by rw [trace_n92 b hb hp,trace_n91 b hb hp]
  have hs120 : n120 b = n119 b := by rw [trace_n120 b hb hp,trace_n119 b hb hp]
  have hs184 : n184 b = n183 b := by rw [trace_n184 b hb hp,trace_n183 b hb hp]
  have hs198 : n198 b = n197 b := by rw [trace_n198 b hb hp,trace_n197 b hb hp]
  have hs212 : n212 b = n211 b := by rw [trace_n212 b hb hp,trace_n211 b hb hp]
  have hs226 : n226 b = n225 b := by rw [trace_n226 b hb hp,trace_n225 b hb hp]
  have hs231 : n231 b = n230 b := by rw [trace_n231 b hb hp,trace_n230 b hb hp]
  ext i
  fin_cases i <;>
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail, expandedStep, expandedUpdate, traceMetric, traceGradient, traceHessian, addSym, outerSym, crossSym, pack, point, metric, Sym2.mulV, Sym2.scale, dot, symmetricMap_apply, div_eq_mul_inv, mul_inv_rev, n13, n15, n16, n64, n66, n122, n233, n312, n313, n314, n315, n316, n317, n318, n319, n330, n331, n332, n333, n334, n335, n2208, n2209, n2210, n2211, n2212, n2213, n2214, n2215, n2216, n2217, n2218, n2220, n2221, n2222, n2224, n2225, n2226, n2228, n2229, n2230, n2232, n2283, n2284, n2289, n2290, n2302, n2303, n2305, n2306, n2318, n2459, n2460, n2461, n2467, n2468, n2472, n2517, n2518, n2519, n2520, n2521, n2522, n2523, n2524, n2525, n2526, n2527, n2528, n2529, n2530, n2531, n2532, n2533, n2534, n2535, n2536, n2537, n2538, n2539, n2540, n2541, n2542, n2543, n2544, n2545, n2546, n2547, n2548, n2549, n2551, n2552, n2553, n2555, n2556, n2558, n2559, n2561, n2562, n2563, n2564, n2566, n2567, n2568, n2570, n2571, n2572, n2574, n2575, n2576, n2578, n2579, n2581, n2582, n2583, n2585, n2586, n2587, n2589, n2590, n2591, n2592, n2593, n2594, n2595, n2596, n2597, n2599, n2600, n2601, n2603, n2604, n2605, n2607, n2608, n2609, n2611, hs92, hs120, hs184, hs198, hs212, hs226, hs231] <;> ring <;> try simp only [true_or,or_true]

theorem jacobian3_column4 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    expandedStep (traceMetric b 3) (traceGradient b 3) (traceGradient b 4)
      (symmetricMap (traceHessian b 3)) (symmetricMap (traceHessian b 4))
      ![0,0,0,0,1] = ![n66 b,n331 b,n2672 b,n2679 b,n2681 b] := by
  have hs92 : n92 b = n91 b := by rw [trace_n92 b hb hp,trace_n91 b hb hp]
  have hs120 : n120 b = n119 b := by rw [trace_n120 b hb hp,trace_n119 b hb hp]
  have hs184 : n184 b = n183 b := by rw [trace_n184 b hb hp,trace_n183 b hb hp]
  have hs198 : n198 b = n197 b := by rw [trace_n198 b hb hp,trace_n197 b hb hp]
  have hs212 : n212 b = n211 b := by rw [trace_n212 b hb hp,trace_n211 b hb hp]
  have hs226 : n226 b = n225 b := by rw [trace_n226 b hb hp,trace_n225 b hb hp]
  have hs231 : n231 b = n230 b := by rw [trace_n231 b hb hp,trace_n230 b hb hp]
  ext i
  fin_cases i <;>
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail, expandedStep, expandedUpdate, traceMetric, traceGradient, traceHessian, addSym, outerSym, crossSym, pack, point, metric, Sym2.mulV, Sym2.scale, dot, symmetricMap_apply, div_eq_mul_inv, mul_inv_rev, n13, n15, n16, n64, n66, n122, n233, n312, n313, n314, n315, n316, n317, n318, n319, n330, n331, n332, n333, n334, n335, n2208, n2209, n2210, n2211, n2212, n2213, n2214, n2215, n2216, n2217, n2218, n2220, n2221, n2222, n2224, n2225, n2226, n2228, n2229, n2230, n2232, n2283, n2284, n2289, n2290, n2302, n2303, n2305, n2306, n2318, n2546, n2547, n2556, n2557, n2612, n2613, n2614, n2615, n2616, n2617, n2618, n2619, n2620, n2621, n2622, n2623, n2624, n2625, n2626, n2627, n2628, n2629, n2630, n2631, n2632, n2633, n2635, n2636, n2637, n2638, n2639, n2641, n2643, n2644, n2645, n2647, n2648, n2649, n2651, n2652, n2653, n2654, n2655, n2657, n2658, n2659, n2661, n2662, n2663, n2664, n2665, n2666, n2667, n2668, n2669, n2671, n2672, n2673, n2675, n2676, n2678, n2679, n2681, hs92, hs120, hs184, hs198, hs212, hs226, hs231] <;> ring <;> try simp only [true_or,or_true]

end
end BFGS.Counterexample
