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

theorem jacobian0_column0 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    expandedStep (traceMetric b 0) (traceGradient b 0) (traceGradient b 1)
      (symmetricMap (traceHessian b 0)) (symmetricMap (traceHessian b 1))
      ![1,0,0,0,0] = ![n583 b,n582 b,n680 b,n681 b,n683 b] := by
  have hs92 : n92 b = n91 b := by rw [trace_n92 b hb hp,trace_n91 b hb hp]
  have hs120 : n120 b = n119 b := by rw [trace_n120 b hb hp,trace_n119 b hb hp]
  have hs184 : n184 b = n183 b := by rw [trace_n184 b hb hp,trace_n183 b hb hp]
  have hs198 : n198 b = n197 b := by rw [trace_n198 b hb hp,trace_n197 b hb hp]
  have hs212 : n212 b = n211 b := by rw [trace_n212 b hb hp,trace_n211 b hb hp]
  have hs226 : n226 b = n225 b := by rw [trace_n226 b hb hp,trace_n225 b hb hp]
  have hs231 : n231 b = n230 b := by rw [trace_n231 b hb hp,trace_n230 b hb hp]
  ext i
  fin_cases i <;>
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail, expandedStep, expandedUpdate, traceMetric, traceGradient, traceHessian, addSym, outerSym, crossSym, pack, point, metric, Sym2.mulV, Sym2.scale, dot, symmetricMap_apply, div_eq_mul_inv, mul_inv_rev, n13, n15, n16, n57, n58, n64, n66, n122, n152, n233, n413, n576, n577, n578, n579, n580, n581, n582, n583, n584, n585, n586, n587, n588, n589, n590, n591, n592, n593, n594, n595, n596, n597, n598, n599, n600, n601, n602, n603, n604, n605, n607, n608, n609, n610, n611, n612, n613, n614, n615, n616, n617, n618, n619, n621, n622, n623, n625, n626, n627, n628, n629, n631, n632, n633, n635, n636, n637, n639, n640, n641, n643, n644, n645, n647, n648, n649, n651, n652, n653, n655, n656, n657, n659, n660, n661, n662, n663, n664, n665, n666, n667, n668, n669, n670, n671, n672, n674, n675, n676, n677, n679, n680, n681, n683, hs92, hs120, hs184, hs198, hs212, hs226, hs231] <;> ring <;> try simp only [true_or,or_true]

theorem jacobian0_column1 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    expandedStep (traceMetric b 0) (traceGradient b 0) (traceGradient b 1)
      (symmetricMap (traceHessian b 0)) (symmetricMap (traceHessian b 1))
      ![0,1,0,0,0] = ![n689 b,n691 b,n776 b,n777 b,n779 b] := by
  have hs92 : n92 b = n91 b := by rw [trace_n92 b hb hp,trace_n91 b hb hp]
  have hs120 : n120 b = n119 b := by rw [trace_n120 b hb hp,trace_n119 b hb hp]
  have hs184 : n184 b = n183 b := by rw [trace_n184 b hb hp,trace_n183 b hb hp]
  have hs198 : n198 b = n197 b := by rw [trace_n198 b hb hp,trace_n197 b hb hp]
  have hs212 : n212 b = n211 b := by rw [trace_n212 b hb hp,trace_n211 b hb hp]
  have hs226 : n226 b = n225 b := by rw [trace_n226 b hb hp,trace_n225 b hb hp]
  have hs231 : n231 b = n230 b := by rw [trace_n231 b hb hp,trace_n230 b hb hp]
  ext i
  fin_cases i <;>
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail, expandedStep, expandedUpdate, traceMetric, traceGradient, traceHessian, addSym, outerSym, crossSym, pack, point, metric, Sym2.mulV, Sym2.scale, dot, symmetricMap_apply, div_eq_mul_inv, mul_inv_rev, n13, n15, n16, n57, n58, n64, n66, n122, n152, n233, n413, n600, n601, n602, n603, n604, n605, n607, n662, n663, n665, n675, n684, n685, n686, n687, n688, n689, n690, n691, n692, n693, n694, n695, n696, n697, n698, n699, n700, n701, n702, n703, n704, n705, n706, n707, n708, n709, n710, n711, n712, n713, n714, n715, n716, n717, n718, n719, n721, n722, n723, n725, n726, n727, n728, n729, n731, n732, n733, n735, n736, n737, n739, n740, n741, n743, n744, n745, n747, n748, n749, n751, n752, n753, n755, n756, n757, n759, n760, n761, n762, n763, n764, n765, n766, n767, n768, n769, n771, n772, n773, n775, n776, n777, n779, hs92, hs120, hs184, hs198, hs212, hs226, hs231] <;> ring <;> try simp only [true_or,or_true]

theorem jacobian0_column2 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    expandedStep (traceMetric b 0) (traceGradient b 0) (traceGradient b 1)
      (symmetricMap (traceHessian b 0)) (symmetricMap (traceHessian b 1))
      ![0,0,1,0,0] = ![n16 b,n66 b,n839 b,n840 b,n836 b] := by
  have hs92 : n92 b = n91 b := by rw [trace_n92 b hb hp,trace_n91 b hb hp]
  have hs120 : n120 b = n119 b := by rw [trace_n120 b hb hp,trace_n119 b hb hp]
  have hs184 : n184 b = n183 b := by rw [trace_n184 b hb hp,trace_n183 b hb hp]
  have hs198 : n198 b = n197 b := by rw [trace_n198 b hb hp,trace_n197 b hb hp]
  have hs212 : n212 b = n211 b := by rw [trace_n212 b hb hp,trace_n211 b hb hp]
  have hs226 : n226 b = n225 b := by rw [trace_n226 b hb hp,trace_n225 b hb hp]
  have hs231 : n231 b = n230 b := by rw [trace_n231 b hb hp,trace_n230 b hb hp]
  ext i
  fin_cases i <;>
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail, expandedStep, expandedUpdate, traceMetric, traceGradient, traceHessian, addSym, outerSym, crossSym, pack, point, metric, Sym2.mulV, Sym2.scale, dot, symmetricMap_apply, div_eq_mul_inv, mul_inv_rev, n13, n15, n16, n57, n58, n64, n66, n122, n152, n233, n413, n600, n601, n602, n603, n604, n605, n607, n662, n663, n665, n675, n780, n781, n782, n783, n784, n785, n786, n787, n788, n789, n790, n791, n792, n793, n794, n795, n796, n797, n798, n799, n800, n801, n803, n805, n806, n807, n808, n809, n811, n812, n813, n815, n816, n817, n818, n820, n821, n822, n824, n825, n826, n827, n828, n829, n830, n831, n832, n833, n834, n836, n837, n838, n839, n840, hs92, hs120, hs184, hs198, hs212, hs226, hs231] <;> ring <;> try simp only [true_or,or_true]

theorem jacobian0_column3 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    expandedStep (traceMetric b 0) (traceGradient b 0) (traceGradient b 1)
      (symmetricMap (traceHessian b 0)) (symmetricMap (traceHessian b 1))
      ![0,0,0,1,0] = ![n66 b,n16 b,n896 b,n900 b,n902 b] := by
  have hs92 : n92 b = n91 b := by rw [trace_n92 b hb hp,trace_n91 b hb hp]
  have hs120 : n120 b = n119 b := by rw [trace_n120 b hb hp,trace_n119 b hb hp]
  have hs184 : n184 b = n183 b := by rw [trace_n184 b hb hp,trace_n183 b hb hp]
  have hs198 : n198 b = n197 b := by rw [trace_n198 b hb hp,trace_n197 b hb hp]
  have hs212 : n212 b = n211 b := by rw [trace_n212 b hb hp,trace_n211 b hb hp]
  have hs226 : n226 b = n225 b := by rw [trace_n226 b hb hp,trace_n225 b hb hp]
  have hs231 : n231 b = n230 b := by rw [trace_n231 b hb hp,trace_n230 b hb hp]
  ext i
  fin_cases i <;>
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail, expandedStep, expandedUpdate, traceMetric, traceGradient, traceHessian, addSym, outerSym, crossSym, pack, point, metric, Sym2.mulV, Sym2.scale, dot, symmetricMap_apply, div_eq_mul_inv, mul_inv_rev, n13, n15, n16, n57, n58, n64, n66, n122, n152, n233, n413, n600, n601, n602, n603, n604, n605, n607, n662, n663, n665, n675, n803, n842, n843, n844, n845, n846, n847, n848, n849, n850, n851, n852, n853, n854, n855, n856, n857, n858, n859, n860, n861, n862, n863, n864, n865, n867, n869, n870, n871, n873, n874, n875, n877, n878, n880, n881, n883, n884, n885, n887, n888, n889, n890, n891, n892, n893, n894, n895, n896, n897, n899, n900, n902, hs92, hs120, hs184, hs198, hs212, hs226, hs231] <;> ring <;> try simp only [true_or,or_true]

theorem jacobian0_column4 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    expandedStep (traceMetric b 0) (traceGradient b 0) (traceGradient b 1)
      (symmetricMap (traceHessian b 0)) (symmetricMap (traceHessian b 1))
      ![0,0,0,0,1] = ![n66 b,n66 b,n57 b,n57 b,n57 b] := by
  have hs92 : n92 b = n91 b := by rw [trace_n92 b hb hp,trace_n91 b hb hp]
  have hs120 : n120 b = n119 b := by rw [trace_n120 b hb hp,trace_n119 b hb hp]
  have hs184 : n184 b = n183 b := by rw [trace_n184 b hb hp,trace_n183 b hb hp]
  have hs198 : n198 b = n197 b := by rw [trace_n198 b hb hp,trace_n197 b hb hp]
  have hs212 : n212 b = n211 b := by rw [trace_n212 b hb hp,trace_n211 b hb hp]
  have hs226 : n226 b = n225 b := by rw [trace_n226 b hb hp,trace_n225 b hb hp]
  have hs231 : n231 b = n230 b := by rw [trace_n231 b hb hp,trace_n230 b hb hp]
  ext i
  fin_cases i <;>
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail, expandedStep, expandedUpdate, traceMetric, traceGradient, traceHessian, addSym, outerSym, crossSym, pack, point, metric, Sym2.mulV, Sym2.scale, dot, symmetricMap_apply, div_eq_mul_inv, mul_inv_rev, n15, n57, n64, n66, n122, n233, hs92, hs120, hs184, hs198, hs212, hs226, hs231] <;> ring <;> try simp only [true_or,or_true]

end
end BFGS.Counterexample
