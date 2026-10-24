import BFGS.Counterexample.DerivativeLinear
import BFGS.Counterexample.TraceBridge
import BFGS.Counterexample.Certificates.IntervalTrace35

/-! The trace matrices, their exact product, quotient projection and change
of coordinates. Every identity below is polynomial arithmetic in trace nodes. -/
namespace BFGS.Counterexample
noncomputable section
open BFGS.Algorithm Trace
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.cons_val_four Matrix.vecHead Matrix.vecTail

attribute [local irreducible] n15 n16 n56 n57 n61 n64 n66 n136 n150 n324 n330 n331 n582 n583 n680 n681 n683 n689 n691 n776 n777 n779 n836 n839 n840 n896 n900 n902 n910 n911 n1044 n1045 n1047 n1054 n1056 n1155 n1156 n1158 n1171 n1172 n1173 n1251 n1255 n1256 n1319 n1326 n1328 n1333 n1338 n1341 n1344 n1345 n1350 n1355 n1358 n1361 n1370 n1379 n1386 n1393 n1398 n1407 n1416 n1423 n1430 n1435 n1444 n1453 n1460 n1467 n1472 n1480 n1481 n1614 n1615 n1617 n1624 n1626 n1725 n1726 n1728 n1801 n1805 n1806 n1902 n1903 n1905 n1967 n1974 n1976 n1983 n1990 n1997 n2004 n2011 n2018 n2025 n2032 n2039 n2046 n2055 n2064 n2073 n2082 n2091 n2100 n2109 n2118 n2127 n2136 n2145 n2154 n2163 n2172 n2181 n2189 n2190 n2323 n2324 n2326 n2333 n2335 n2434 n2435 n2437 n2510 n2514 n2515 n2608 n2609 n2611 n2672 n2679 n2681 n2688 n2695 n2702 n2709 n2716 n2723 n2730 n2737 n2744 n2751 n2760 n2769 n2778 n2787 n2796 n2805 n2814 n2823 n2832 n2841 n2850 n2859 n2868 n2877 n2886 n2887 n2888 n2889 n2890 n2891 n2892 n2893 n2894 n2895 n2896 n2897 n2898 n2899 n2900 n2901 n2902 n2903 n2904 n2905 n2906 n2907 n2908 n2909 n2910 n2911

abbrev Matrix5 := Matrix (Fin 5) (Fin 5) ℝ
abbrev Matrix4 := Matrix (Fin 4) (Fin 4) ℝ
def traceJacobian (b : ℝ) : Fin 4 → Matrix5 :=
  ![![![n583 b,n689 b,n16 b,n66 b,n66 b],![n582 b,n691 b,n66 b,n16 b,n66 b],![n680 b,n776 b,n839 b,n896 b,n57 b],![n681 b,n777 b,n840 b,n900 b,n57 b],![n683 b,n779 b,n836 b,n902 b,n57 b]],![![n911 b,n1054 b,n66 b,n16 b,n66 b],![n910 b,n1056 b,n66 b,n66 b,n16 b],![n1044 b,n1155 b,n1172 b,n1255 b,n1319 b],![n1045 b,n1156 b,n1173 b,n1256 b,n1326 b],![n1047 b,n1158 b,n1171 b,n1251 b,n1328 b]],![![n1481 b,n1624 b,n56 b,n324 b,n66 b],![n1480 b,n1626 b,n66 b,n56 b,n324 b],![n1614 b,n1725 b,n1805 b,n1902 b,n1967 b],![n1615 b,n1726 b,n1806 b,n1903 b,n1974 b],![n1617 b,n1728 b,n1801 b,n1905 b,n1976 b]],![![n2190 b,n2333 b,n330 b,n331 b,n66 b],![n2189 b,n2335 b,n66 b,n330 b,n331 b],![n2323 b,n2434 b,n2514 b,n2608 b,n2672 b],![n2324 b,n2435 b,n2515 b,n2609 b,n2679 b],![n2326 b,n2437 b,n2510 b,n2611 b,n2681 b]]]

def traceProduct (b : ℝ) : Fin 4 → Matrix5 :=
  ![traceJacobian b 0,![![n1333 b,n1338 b,n1341 b,n1344 b,n1345 b],![n1350 b,n1355 b,n1358 b,n1361 b,n1345 b],![n1370 b,n1379 b,n1386 b,n1393 b,n1398 b],![n1407 b,n1416 b,n1423 b,n1430 b,n1435 b],![n1444 b,n1453 b,n1460 b,n1467 b,n1472 b]],![![n1983 b,n1990 b,n1997 b,n2004 b,n2011 b],![n2018 b,n2025 b,n2032 b,n2039 b,n2046 b],![n2055 b,n2064 b,n2073 b,n2082 b,n2091 b],![n2100 b,n2109 b,n2118 b,n2127 b,n2136 b],![n2145 b,n2154 b,n2163 b,n2172 b,n2181 b]],![![n2688 b,n2695 b,n2702 b,n2709 b,n2716 b],![n2723 b,n2730 b,n2737 b,n2744 b,n2751 b],![n2760 b,n2769 b,n2778 b,n2787 b,n2796 b],![n2805 b,n2814 b,n2823 b,n2832 b,n2841 b],![n2850 b,n2859 b,n2868 b,n2877 b,n2886 b]]]

def traceReturnDerivative (b : ℝ) : Matrix5 :=
  ![![n2887 b,n2888 b,n2889 b,n2890 b,n2891 b],![n2892 b,n2893 b,n2894 b,n2895 b,n2896 b],![n2897 b,n2898 b,n2899 b,n2900 b,n2901 b],![n2902 b,n2903 b,n2904 b,n2905 b,n2906 b],![n2907 b,n2908 b,n2909 b,n2910 b,n2911 b]]

def traceBaseState (b : ℝ) : State := ![n136 b,n150 b,n15 b,n64 b,n61 b]

def transverseKeep : Fin 4 → Fin 5 := ![0,1,3,4]

def traceTransverse (b : ℝ) : Matrix4 := fun i j =>
  traceReturnDerivative b (transverseKeep i) (transverseKeep j)-
  traceBaseState b (transverseKeep i)*traceReturnDerivative b 2 (transverseKeep j)

def transverseConjugator : Matrix4 := ![![464,1077,4501,-1708],![1366,2793,10000,552],![-448,-1058,-4343,1648],![16,293,1787,-2075]]

def transverseConjugatorInv : Matrix4 := ![![(521647187/22230591050),(-118215737/22230591050),(23413073/4446118210),(-183928858/11115295525)],![(-574350721/11115295525),(888696/11115295525),(-118410819/2223059105),(2783828/11115295525)],![(123292286/11115295525),(8549264/11115295525),(30921059/2223059105),(23578552/11115295525)],![(27089991/11115295525),(7032384/11115295525),(9999454/2223059105),(13924037/11115295525)]]

def traceConjugatedTransverse (b : ℝ) : Matrix4 :=
  ![![n3098 b,n3109 b,n3120 b,n3131 b],![n3138 b,n3145 b,n3152 b,n3159 b],![n3166 b,n3173 b,n3180 b,n3187 b],![n3194 b,n3201 b,n3208 b,n3215 b]]

private theorem mul5_entry_nested (A B : Matrix5) (i j : Fin 5) :
    (A*B) i j = A i 0*B 0 j + (A i 1*B 1 j + (A i 2*B 2 j + (A i 3*B 3 j + (A i 4*B 4 j+0)))) := by
  simp only [Matrix.mul_apply,Fin.sum_univ_succ,Fin.sum_univ_zero]
  rfl

theorem traceProduct_zero (b : ℝ) : traceProduct b 0 = traceJacobian b 0 := by
  unfold traceProduct
  exact Matrix.cons_val_zero _ _

private theorem product1_0_0 (b : ℝ) :
    traceProduct b 1 0 0 = (traceJacobian b 1 * traceProduct b 0) 0 0 := by
  change n1333 b = _
  rw [mul5_entry_nested]
  change n1333 b = (n911 b*n583 b+(n1054 b*n582 b+(n66 b*n680 b+(n16 b*n681 b+(n66 b*n683 b+0)))))
  simp only [n16,n66,n1329,n1330,n1331,n1332,n1333]
  generalize n582 b = v582
  generalize n583 b = v583
  generalize n680 b = v680
  generalize n681 b = v681
  generalize n683 b = v683
  generalize n911 b = v911
  generalize n1054 b = v1054
  norm_num <;> ring

private theorem product1_0_1 (b : ℝ) :
    traceProduct b 1 0 1 = (traceJacobian b 1 * traceProduct b 0) 0 1 := by
  change n1338 b = _
  rw [mul5_entry_nested]
  change n1338 b = (n911 b*n689 b+(n1054 b*n691 b+(n66 b*n776 b+(n16 b*n777 b+(n66 b*n779 b+0)))))
  simp only [n16,n66,n1334,n1335,n1336,n1337,n1338]
  generalize n689 b = v689
  generalize n691 b = v691
  generalize n776 b = v776
  generalize n777 b = v777
  generalize n779 b = v779
  generalize n911 b = v911
  generalize n1054 b = v1054
  norm_num <;> ring

private theorem product1_0_2 (b : ℝ) :
    traceProduct b 1 0 2 = (traceJacobian b 1 * traceProduct b 0) 0 2 := by
  change n1341 b = _
  rw [mul5_entry_nested]
  change n1341 b = (n911 b*n16 b+(n1054 b*n66 b+(n66 b*n839 b+(n16 b*n840 b+(n66 b*n836 b+0)))))
  simp only [n16,n66,n1339,n1340,n1341]
  generalize n836 b = v836
  generalize n839 b = v839
  generalize n840 b = v840
  generalize n911 b = v911
  generalize n1054 b = v1054
  norm_num

private theorem product1_0_3 (b : ℝ) :
    traceProduct b 1 0 3 = (traceJacobian b 1 * traceProduct b 0) 0 3 := by
  change n1344 b = _
  rw [mul5_entry_nested]
  change n1344 b = (n911 b*n66 b+(n1054 b*n16 b+(n66 b*n896 b+(n16 b*n900 b+(n66 b*n902 b+0)))))
  simp only [n16,n66,n1342,n1343,n1344]
  generalize n896 b = v896
  generalize n900 b = v900
  generalize n902 b = v902
  generalize n911 b = v911
  generalize n1054 b = v1054
  norm_num

private theorem product1_0_4 (b : ℝ) :
    traceProduct b 1 0 4 = (traceJacobian b 1 * traceProduct b 0) 0 4 := by
  change n1345 b = _
  rw [mul5_entry_nested]
  change n1345 b = (n911 b*n66 b+(n1054 b*n66 b+(n66 b*n57 b+(n16 b*n57 b+(n66 b*n57 b+0)))))
  simp only [n16,n57,n66,n1345]
  generalize n911 b = v911
  generalize n1054 b = v1054
  norm_num

private theorem product1_1_0 (b : ℝ) :
    traceProduct b 1 1 0 = (traceJacobian b 1 * traceProduct b 0) 1 0 := by
  change n1350 b = _
  rw [mul5_entry_nested]
  change n1350 b = (n910 b*n583 b+(n1056 b*n582 b+(n66 b*n680 b+(n66 b*n681 b+(n16 b*n683 b+0)))))
  simp only [n16,n66,n1346,n1347,n1348,n1349,n1350]
  generalize n582 b = v582
  generalize n583 b = v583
  generalize n680 b = v680
  generalize n681 b = v681
  generalize n683 b = v683
  generalize n910 b = v910
  generalize n1056 b = v1056
  norm_num <;> ring

private theorem product1_1_1 (b : ℝ) :
    traceProduct b 1 1 1 = (traceJacobian b 1 * traceProduct b 0) 1 1 := by
  change n1355 b = _
  rw [mul5_entry_nested]
  change n1355 b = (n910 b*n689 b+(n1056 b*n691 b+(n66 b*n776 b+(n66 b*n777 b+(n16 b*n779 b+0)))))
  simp only [n16,n66,n1351,n1352,n1353,n1354,n1355]
  generalize n689 b = v689
  generalize n691 b = v691
  generalize n776 b = v776
  generalize n777 b = v777
  generalize n779 b = v779
  generalize n910 b = v910
  generalize n1056 b = v1056
  norm_num <;> ring

private theorem product1_1_2 (b : ℝ) :
    traceProduct b 1 1 2 = (traceJacobian b 1 * traceProduct b 0) 1 2 := by
  change n1358 b = _
  rw [mul5_entry_nested]
  change n1358 b = (n910 b*n16 b+(n1056 b*n66 b+(n66 b*n839 b+(n66 b*n840 b+(n16 b*n836 b+0)))))
  simp only [n16,n66,n1356,n1357,n1358]
  generalize n836 b = v836
  generalize n839 b = v839
  generalize n840 b = v840
  generalize n910 b = v910
  generalize n1056 b = v1056
  norm_num

private theorem product1_1_3 (b : ℝ) :
    traceProduct b 1 1 3 = (traceJacobian b 1 * traceProduct b 0) 1 3 := by
  change n1361 b = _
  rw [mul5_entry_nested]
  change n1361 b = (n910 b*n66 b+(n1056 b*n16 b+(n66 b*n896 b+(n66 b*n900 b+(n16 b*n902 b+0)))))
  simp only [n16,n66,n1359,n1360,n1361]
  generalize n896 b = v896
  generalize n900 b = v900
  generalize n902 b = v902
  generalize n910 b = v910
  generalize n1056 b = v1056
  norm_num

private theorem product1_1_4 (b : ℝ) :
    traceProduct b 1 1 4 = (traceJacobian b 1 * traceProduct b 0) 1 4 := by
  change n1345 b = _
  rw [mul5_entry_nested]
  change n1345 b = (n910 b*n66 b+(n1056 b*n66 b+(n66 b*n57 b+(n66 b*n57 b+(n16 b*n57 b+0)))))
  simp only [n16,n57,n66,n1345]
  generalize n910 b = v910
  generalize n1056 b = v1056
  norm_num

private theorem product1_2_0 (b : ℝ) :
    traceProduct b 1 2 0 = (traceJacobian b 1 * traceProduct b 0) 2 0 := by
  change n1370 b = _
  rw [mul5_entry_nested]
  change n1370 b = (n1044 b*n583 b+(n1155 b*n582 b+(n1172 b*n680 b+(n1255 b*n681 b+(n1319 b*n683 b+0)))))
  simp only [n1362,n1363,n1364,n1365,n1366,n1367,n1368,n1369,n1370]
  generalize n582 b = v582
  generalize n583 b = v583
  generalize n680 b = v680
  generalize n681 b = v681
  generalize n683 b = v683
  generalize n1044 b = v1044
  generalize n1155 b = v1155
  generalize n1172 b = v1172
  generalize n1255 b = v1255
  generalize n1319 b = v1319
  norm_num <;> ring

private theorem product1_2_1 (b : ℝ) :
    traceProduct b 1 2 1 = (traceJacobian b 1 * traceProduct b 0) 2 1 := by
  change n1379 b = _
  rw [mul5_entry_nested]
  change n1379 b = (n1044 b*n689 b+(n1155 b*n691 b+(n1172 b*n776 b+(n1255 b*n777 b+(n1319 b*n779 b+0)))))
  simp only [n1371,n1372,n1373,n1374,n1375,n1376,n1377,n1378,n1379]
  generalize n689 b = v689
  generalize n691 b = v691
  generalize n776 b = v776
  generalize n777 b = v777
  generalize n779 b = v779
  generalize n1044 b = v1044
  generalize n1155 b = v1155
  generalize n1172 b = v1172
  generalize n1255 b = v1255
  generalize n1319 b = v1319
  norm_num <;> ring

private theorem product1_2_2 (b : ℝ) :
    traceProduct b 1 2 2 = (traceJacobian b 1 * traceProduct b 0) 2 2 := by
  change n1386 b = _
  rw [mul5_entry_nested]
  change n1386 b = (n1044 b*n16 b+(n1155 b*n66 b+(n1172 b*n839 b+(n1255 b*n840 b+(n1319 b*n836 b+0)))))
  simp only [n16,n66,n1380,n1381,n1382,n1383,n1384,n1385,n1386]
  generalize n836 b = v836
  generalize n839 b = v839
  generalize n840 b = v840
  generalize n1044 b = v1044
  generalize n1155 b = v1155
  generalize n1172 b = v1172
  generalize n1255 b = v1255
  generalize n1319 b = v1319
  norm_num <;> ring

private theorem product1_2_3 (b : ℝ) :
    traceProduct b 1 2 3 = (traceJacobian b 1 * traceProduct b 0) 2 3 := by
  change n1393 b = _
  rw [mul5_entry_nested]
  change n1393 b = (n1044 b*n66 b+(n1155 b*n16 b+(n1172 b*n896 b+(n1255 b*n900 b+(n1319 b*n902 b+0)))))
  simp only [n16,n66,n1387,n1388,n1389,n1390,n1391,n1392,n1393]
  generalize n896 b = v896
  generalize n900 b = v900
  generalize n902 b = v902
  generalize n1044 b = v1044
  generalize n1155 b = v1155
  generalize n1172 b = v1172
  generalize n1255 b = v1255
  generalize n1319 b = v1319
  norm_num <;> ring

private theorem product1_2_4 (b : ℝ) :
    traceProduct b 1 2 4 = (traceJacobian b 1 * traceProduct b 0) 2 4 := by
  change n1398 b = _
  rw [mul5_entry_nested]
  change n1398 b = (n1044 b*n66 b+(n1155 b*n66 b+(n1172 b*n57 b+(n1255 b*n57 b+(n1319 b*n57 b+0)))))
  simp only [n57,n66,n1394,n1395,n1396,n1397,n1398]
  generalize n1044 b = v1044
  generalize n1155 b = v1155
  generalize n1172 b = v1172
  generalize n1255 b = v1255
  generalize n1319 b = v1319
  norm_num <;> ring

private theorem product1_3_0 (b : ℝ) :
    traceProduct b 1 3 0 = (traceJacobian b 1 * traceProduct b 0) 3 0 := by
  change n1407 b = _
  rw [mul5_entry_nested]
  change n1407 b = (n1045 b*n583 b+(n1156 b*n582 b+(n1173 b*n680 b+(n1256 b*n681 b+(n1326 b*n683 b+0)))))
  simp only [n1399,n1400,n1401,n1402,n1403,n1404,n1405,n1406,n1407]
  generalize n582 b = v582
  generalize n583 b = v583
  generalize n680 b = v680
  generalize n681 b = v681
  generalize n683 b = v683
  generalize n1045 b = v1045
  generalize n1156 b = v1156
  generalize n1173 b = v1173
  generalize n1256 b = v1256
  generalize n1326 b = v1326
  norm_num <;> ring

private theorem product1_3_1 (b : ℝ) :
    traceProduct b 1 3 1 = (traceJacobian b 1 * traceProduct b 0) 3 1 := by
  change n1416 b = _
  rw [mul5_entry_nested]
  change n1416 b = (n1045 b*n689 b+(n1156 b*n691 b+(n1173 b*n776 b+(n1256 b*n777 b+(n1326 b*n779 b+0)))))
  simp only [n1408,n1409,n1410,n1411,n1412,n1413,n1414,n1415,n1416]
  generalize n689 b = v689
  generalize n691 b = v691
  generalize n776 b = v776
  generalize n777 b = v777
  generalize n779 b = v779
  generalize n1045 b = v1045
  generalize n1156 b = v1156
  generalize n1173 b = v1173
  generalize n1256 b = v1256
  generalize n1326 b = v1326
  norm_num <;> ring

private theorem product1_3_2 (b : ℝ) :
    traceProduct b 1 3 2 = (traceJacobian b 1 * traceProduct b 0) 3 2 := by
  change n1423 b = _
  rw [mul5_entry_nested]
  change n1423 b = (n1045 b*n16 b+(n1156 b*n66 b+(n1173 b*n839 b+(n1256 b*n840 b+(n1326 b*n836 b+0)))))
  simp only [n16,n66,n1417,n1418,n1419,n1420,n1421,n1422,n1423]
  generalize n836 b = v836
  generalize n839 b = v839
  generalize n840 b = v840
  generalize n1045 b = v1045
  generalize n1156 b = v1156
  generalize n1173 b = v1173
  generalize n1256 b = v1256
  generalize n1326 b = v1326
  norm_num <;> ring

private theorem product1_3_3 (b : ℝ) :
    traceProduct b 1 3 3 = (traceJacobian b 1 * traceProduct b 0) 3 3 := by
  change n1430 b = _
  rw [mul5_entry_nested]
  change n1430 b = (n1045 b*n66 b+(n1156 b*n16 b+(n1173 b*n896 b+(n1256 b*n900 b+(n1326 b*n902 b+0)))))
  simp only [n16,n66,n1424,n1425,n1426,n1427,n1428,n1429,n1430]
  generalize n896 b = v896
  generalize n900 b = v900
  generalize n902 b = v902
  generalize n1045 b = v1045
  generalize n1156 b = v1156
  generalize n1173 b = v1173
  generalize n1256 b = v1256
  generalize n1326 b = v1326
  norm_num <;> ring

private theorem product1_3_4 (b : ℝ) :
    traceProduct b 1 3 4 = (traceJacobian b 1 * traceProduct b 0) 3 4 := by
  change n1435 b = _
  rw [mul5_entry_nested]
  change n1435 b = (n1045 b*n66 b+(n1156 b*n66 b+(n1173 b*n57 b+(n1256 b*n57 b+(n1326 b*n57 b+0)))))
  simp only [n57,n66,n1431,n1432,n1433,n1434,n1435]
  generalize n1045 b = v1045
  generalize n1156 b = v1156
  generalize n1173 b = v1173
  generalize n1256 b = v1256
  generalize n1326 b = v1326
  norm_num <;> ring

private theorem product1_4_0 (b : ℝ) :
    traceProduct b 1 4 0 = (traceJacobian b 1 * traceProduct b 0) 4 0 := by
  change n1444 b = _
  rw [mul5_entry_nested]
  change n1444 b = (n1047 b*n583 b+(n1158 b*n582 b+(n1171 b*n680 b+(n1251 b*n681 b+(n1328 b*n683 b+0)))))
  simp only [n1436,n1437,n1438,n1439,n1440,n1441,n1442,n1443,n1444]
  generalize n582 b = v582
  generalize n583 b = v583
  generalize n680 b = v680
  generalize n681 b = v681
  generalize n683 b = v683
  generalize n1047 b = v1047
  generalize n1158 b = v1158
  generalize n1171 b = v1171
  generalize n1251 b = v1251
  generalize n1328 b = v1328
  norm_num <;> ring

private theorem product1_4_1 (b : ℝ) :
    traceProduct b 1 4 1 = (traceJacobian b 1 * traceProduct b 0) 4 1 := by
  change n1453 b = _
  rw [mul5_entry_nested]
  change n1453 b = (n1047 b*n689 b+(n1158 b*n691 b+(n1171 b*n776 b+(n1251 b*n777 b+(n1328 b*n779 b+0)))))
  simp only [n1445,n1446,n1447,n1448,n1449,n1450,n1451,n1452,n1453]
  generalize n689 b = v689
  generalize n691 b = v691
  generalize n776 b = v776
  generalize n777 b = v777
  generalize n779 b = v779
  generalize n1047 b = v1047
  generalize n1158 b = v1158
  generalize n1171 b = v1171
  generalize n1251 b = v1251
  generalize n1328 b = v1328
  norm_num <;> ring

private theorem product1_4_2 (b : ℝ) :
    traceProduct b 1 4 2 = (traceJacobian b 1 * traceProduct b 0) 4 2 := by
  change n1460 b = _
  rw [mul5_entry_nested]
  change n1460 b = (n1047 b*n16 b+(n1158 b*n66 b+(n1171 b*n839 b+(n1251 b*n840 b+(n1328 b*n836 b+0)))))
  simp only [n16,n66,n1454,n1455,n1456,n1457,n1458,n1459,n1460]
  generalize n836 b = v836
  generalize n839 b = v839
  generalize n840 b = v840
  generalize n1047 b = v1047
  generalize n1158 b = v1158
  generalize n1171 b = v1171
  generalize n1251 b = v1251
  generalize n1328 b = v1328
  norm_num <;> ring

private theorem product1_4_3 (b : ℝ) :
    traceProduct b 1 4 3 = (traceJacobian b 1 * traceProduct b 0) 4 3 := by
  change n1467 b = _
  rw [mul5_entry_nested]
  change n1467 b = (n1047 b*n66 b+(n1158 b*n16 b+(n1171 b*n896 b+(n1251 b*n900 b+(n1328 b*n902 b+0)))))
  simp only [n16,n66,n1461,n1462,n1463,n1464,n1465,n1466,n1467]
  generalize n896 b = v896
  generalize n900 b = v900
  generalize n902 b = v902
  generalize n1047 b = v1047
  generalize n1158 b = v1158
  generalize n1171 b = v1171
  generalize n1251 b = v1251
  generalize n1328 b = v1328
  norm_num <;> ring

private theorem product1_4_4 (b : ℝ) :
    traceProduct b 1 4 4 = (traceJacobian b 1 * traceProduct b 0) 4 4 := by
  change n1472 b = _
  rw [mul5_entry_nested]
  change n1472 b = (n1047 b*n66 b+(n1158 b*n66 b+(n1171 b*n57 b+(n1251 b*n57 b+(n1328 b*n57 b+0)))))
  simp only [n57,n66,n1468,n1469,n1470,n1471,n1472]
  generalize n1047 b = v1047
  generalize n1158 b = v1158
  generalize n1171 b = v1171
  generalize n1251 b = v1251
  generalize n1328 b = v1328
  norm_num <;> ring

theorem traceProduct_1 (b : ℝ) : traceProduct b 1 = traceJacobian b 1 * traceProduct b 0 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact product1_0_0 b
  · exact product1_0_1 b
  · exact product1_0_2 b
  · exact product1_0_3 b
  · exact product1_0_4 b
  · exact product1_1_0 b
  · exact product1_1_1 b
  · exact product1_1_2 b
  · exact product1_1_3 b
  · exact product1_1_4 b
  · exact product1_2_0 b
  · exact product1_2_1 b
  · exact product1_2_2 b
  · exact product1_2_3 b
  · exact product1_2_4 b
  · exact product1_3_0 b
  · exact product1_3_1 b
  · exact product1_3_2 b
  · exact product1_3_3 b
  · exact product1_3_4 b
  · exact product1_4_0 b
  · exact product1_4_1 b
  · exact product1_4_2 b
  · exact product1_4_3 b
  · exact product1_4_4 b

private theorem product2_0_0 (b : ℝ) :
    traceProduct b 2 0 0 = (traceJacobian b 2 * traceProduct b 1) 0 0 := by
  change n1983 b = _
  rw [mul5_entry_nested]
  change n1983 b = (n1481 b*n1333 b+(n1624 b*n1350 b+(n56 b*n1370 b+(n324 b*n1407 b+(n66 b*n1444 b+0)))))
  simp only [n66,n1977,n1978,n1979,n1980,n1981,n1982,n1983]
  generalize n56 b = v56
  generalize n324 b = v324
  generalize n1333 b = v1333
  generalize n1350 b = v1350
  generalize n1370 b = v1370
  generalize n1407 b = v1407
  generalize n1444 b = v1444
  generalize n1481 b = v1481
  generalize n1624 b = v1624
  norm_num <;> ring

private theorem product2_0_1 (b : ℝ) :
    traceProduct b 2 0 1 = (traceJacobian b 2 * traceProduct b 1) 0 1 := by
  change n1990 b = _
  rw [mul5_entry_nested]
  change n1990 b = (n1481 b*n1338 b+(n1624 b*n1355 b+(n56 b*n1379 b+(n324 b*n1416 b+(n66 b*n1453 b+0)))))
  simp only [n66,n1984,n1985,n1986,n1987,n1988,n1989,n1990]
  generalize n56 b = v56
  generalize n324 b = v324
  generalize n1338 b = v1338
  generalize n1355 b = v1355
  generalize n1379 b = v1379
  generalize n1416 b = v1416
  generalize n1453 b = v1453
  generalize n1481 b = v1481
  generalize n1624 b = v1624
  norm_num <;> ring

private theorem product2_0_2 (b : ℝ) :
    traceProduct b 2 0 2 = (traceJacobian b 2 * traceProduct b 1) 0 2 := by
  change n1997 b = _
  rw [mul5_entry_nested]
  change n1997 b = (n1481 b*n1341 b+(n1624 b*n1358 b+(n56 b*n1386 b+(n324 b*n1423 b+(n66 b*n1460 b+0)))))
  simp only [n66,n1991,n1992,n1993,n1994,n1995,n1996,n1997]
  generalize n56 b = v56
  generalize n324 b = v324
  generalize n1341 b = v1341
  generalize n1358 b = v1358
  generalize n1386 b = v1386
  generalize n1423 b = v1423
  generalize n1460 b = v1460
  generalize n1481 b = v1481
  generalize n1624 b = v1624
  norm_num <;> ring

private theorem product2_0_3 (b : ℝ) :
    traceProduct b 2 0 3 = (traceJacobian b 2 * traceProduct b 1) 0 3 := by
  change n2004 b = _
  rw [mul5_entry_nested]
  change n2004 b = (n1481 b*n1344 b+(n1624 b*n1361 b+(n56 b*n1393 b+(n324 b*n1430 b+(n66 b*n1467 b+0)))))
  simp only [n66,n1998,n1999,n2000,n2001,n2002,n2003,n2004]
  generalize n56 b = v56
  generalize n324 b = v324
  generalize n1344 b = v1344
  generalize n1361 b = v1361
  generalize n1393 b = v1393
  generalize n1430 b = v1430
  generalize n1467 b = v1467
  generalize n1481 b = v1481
  generalize n1624 b = v1624
  norm_num <;> ring

private theorem product2_0_4 (b : ℝ) :
    traceProduct b 2 0 4 = (traceJacobian b 2 * traceProduct b 1) 0 4 := by
  change n2011 b = _
  rw [mul5_entry_nested]
  change n2011 b = (n1481 b*n1345 b+(n1624 b*n1345 b+(n56 b*n1398 b+(n324 b*n1435 b+(n66 b*n1472 b+0)))))
  simp only [n66,n1345,n2005,n2006,n2007,n2008,n2009,n2010,n2011]
  generalize n56 b = v56
  generalize n324 b = v324
  generalize n1398 b = v1398
  generalize n1435 b = v1435
  generalize n1472 b = v1472
  generalize n1481 b = v1481
  generalize n1624 b = v1624
  norm_num <;> ring

private theorem product2_1_0 (b : ℝ) :
    traceProduct b 2 1 0 = (traceJacobian b 2 * traceProduct b 1) 1 0 := by
  change n2018 b = _
  rw [mul5_entry_nested]
  change n2018 b = (n1480 b*n1333 b+(n1626 b*n1350 b+(n66 b*n1370 b+(n56 b*n1407 b+(n324 b*n1444 b+0)))))
  simp only [n66,n2012,n2013,n2014,n2015,n2016,n2017,n2018]
  generalize n56 b = v56
  generalize n324 b = v324
  generalize n1333 b = v1333
  generalize n1350 b = v1350
  generalize n1370 b = v1370
  generalize n1407 b = v1407
  generalize n1444 b = v1444
  generalize n1480 b = v1480
  generalize n1626 b = v1626
  norm_num <;> ring

private theorem product2_1_1 (b : ℝ) :
    traceProduct b 2 1 1 = (traceJacobian b 2 * traceProduct b 1) 1 1 := by
  change n2025 b = _
  rw [mul5_entry_nested]
  change n2025 b = (n1480 b*n1338 b+(n1626 b*n1355 b+(n66 b*n1379 b+(n56 b*n1416 b+(n324 b*n1453 b+0)))))
  simp only [n66,n2019,n2020,n2021,n2022,n2023,n2024,n2025]
  generalize n56 b = v56
  generalize n324 b = v324
  generalize n1338 b = v1338
  generalize n1355 b = v1355
  generalize n1379 b = v1379
  generalize n1416 b = v1416
  generalize n1453 b = v1453
  generalize n1480 b = v1480
  generalize n1626 b = v1626
  norm_num <;> ring

private theorem product2_1_2 (b : ℝ) :
    traceProduct b 2 1 2 = (traceJacobian b 2 * traceProduct b 1) 1 2 := by
  change n2032 b = _
  rw [mul5_entry_nested]
  change n2032 b = (n1480 b*n1341 b+(n1626 b*n1358 b+(n66 b*n1386 b+(n56 b*n1423 b+(n324 b*n1460 b+0)))))
  simp only [n66,n2026,n2027,n2028,n2029,n2030,n2031,n2032]
  generalize n56 b = v56
  generalize n324 b = v324
  generalize n1341 b = v1341
  generalize n1358 b = v1358
  generalize n1386 b = v1386
  generalize n1423 b = v1423
  generalize n1460 b = v1460
  generalize n1480 b = v1480
  generalize n1626 b = v1626
  norm_num <;> ring

private theorem product2_1_3 (b : ℝ) :
    traceProduct b 2 1 3 = (traceJacobian b 2 * traceProduct b 1) 1 3 := by
  change n2039 b = _
  rw [mul5_entry_nested]
  change n2039 b = (n1480 b*n1344 b+(n1626 b*n1361 b+(n66 b*n1393 b+(n56 b*n1430 b+(n324 b*n1467 b+0)))))
  simp only [n66,n2033,n2034,n2035,n2036,n2037,n2038,n2039]
  generalize n56 b = v56
  generalize n324 b = v324
  generalize n1344 b = v1344
  generalize n1361 b = v1361
  generalize n1393 b = v1393
  generalize n1430 b = v1430
  generalize n1467 b = v1467
  generalize n1480 b = v1480
  generalize n1626 b = v1626
  norm_num <;> ring

private theorem product2_1_4 (b : ℝ) :
    traceProduct b 2 1 4 = (traceJacobian b 2 * traceProduct b 1) 1 4 := by
  change n2046 b = _
  rw [mul5_entry_nested]
  change n2046 b = (n1480 b*n1345 b+(n1626 b*n1345 b+(n66 b*n1398 b+(n56 b*n1435 b+(n324 b*n1472 b+0)))))
  simp only [n66,n1345,n2040,n2041,n2042,n2043,n2044,n2045,n2046]
  generalize n56 b = v56
  generalize n324 b = v324
  generalize n1398 b = v1398
  generalize n1435 b = v1435
  generalize n1472 b = v1472
  generalize n1480 b = v1480
  generalize n1626 b = v1626
  norm_num <;> ring

private theorem product2_2_0 (b : ℝ) :
    traceProduct b 2 2 0 = (traceJacobian b 2 * traceProduct b 1) 2 0 := by
  change n2055 b = _
  rw [mul5_entry_nested]
  change n2055 b = (n1614 b*n1333 b+(n1725 b*n1350 b+(n1805 b*n1370 b+(n1902 b*n1407 b+(n1967 b*n1444 b+0)))))
  simp only [n2047,n2048,n2049,n2050,n2051,n2052,n2053,n2054,n2055]
  generalize n1333 b = v1333
  generalize n1350 b = v1350
  generalize n1370 b = v1370
  generalize n1407 b = v1407
  generalize n1444 b = v1444
  generalize n1614 b = v1614
  generalize n1725 b = v1725
  generalize n1805 b = v1805
  generalize n1902 b = v1902
  generalize n1967 b = v1967
  norm_num <;> ring

private theorem product2_2_1 (b : ℝ) :
    traceProduct b 2 2 1 = (traceJacobian b 2 * traceProduct b 1) 2 1 := by
  change n2064 b = _
  rw [mul5_entry_nested]
  change n2064 b = (n1614 b*n1338 b+(n1725 b*n1355 b+(n1805 b*n1379 b+(n1902 b*n1416 b+(n1967 b*n1453 b+0)))))
  simp only [n2056,n2057,n2058,n2059,n2060,n2061,n2062,n2063,n2064]
  generalize n1338 b = v1338
  generalize n1355 b = v1355
  generalize n1379 b = v1379
  generalize n1416 b = v1416
  generalize n1453 b = v1453
  generalize n1614 b = v1614
  generalize n1725 b = v1725
  generalize n1805 b = v1805
  generalize n1902 b = v1902
  generalize n1967 b = v1967
  norm_num <;> ring

private theorem product2_2_2 (b : ℝ) :
    traceProduct b 2 2 2 = (traceJacobian b 2 * traceProduct b 1) 2 2 := by
  change n2073 b = _
  rw [mul5_entry_nested]
  change n2073 b = (n1614 b*n1341 b+(n1725 b*n1358 b+(n1805 b*n1386 b+(n1902 b*n1423 b+(n1967 b*n1460 b+0)))))
  simp only [n2065,n2066,n2067,n2068,n2069,n2070,n2071,n2072,n2073]
  generalize n1341 b = v1341
  generalize n1358 b = v1358
  generalize n1386 b = v1386
  generalize n1423 b = v1423
  generalize n1460 b = v1460
  generalize n1614 b = v1614
  generalize n1725 b = v1725
  generalize n1805 b = v1805
  generalize n1902 b = v1902
  generalize n1967 b = v1967
  norm_num <;> ring

private theorem product2_2_3 (b : ℝ) :
    traceProduct b 2 2 3 = (traceJacobian b 2 * traceProduct b 1) 2 3 := by
  change n2082 b = _
  rw [mul5_entry_nested]
  change n2082 b = (n1614 b*n1344 b+(n1725 b*n1361 b+(n1805 b*n1393 b+(n1902 b*n1430 b+(n1967 b*n1467 b+0)))))
  simp only [n2074,n2075,n2076,n2077,n2078,n2079,n2080,n2081,n2082]
  generalize n1344 b = v1344
  generalize n1361 b = v1361
  generalize n1393 b = v1393
  generalize n1430 b = v1430
  generalize n1467 b = v1467
  generalize n1614 b = v1614
  generalize n1725 b = v1725
  generalize n1805 b = v1805
  generalize n1902 b = v1902
  generalize n1967 b = v1967
  norm_num <;> ring

private theorem product2_2_4 (b : ℝ) :
    traceProduct b 2 2 4 = (traceJacobian b 2 * traceProduct b 1) 2 4 := by
  change n2091 b = _
  rw [mul5_entry_nested]
  change n2091 b = (n1614 b*n1345 b+(n1725 b*n1345 b+(n1805 b*n1398 b+(n1902 b*n1435 b+(n1967 b*n1472 b+0)))))
  simp only [n1345,n2083,n2084,n2085,n2086,n2087,n2088,n2089,n2090,n2091]
  generalize n1398 b = v1398
  generalize n1435 b = v1435
  generalize n1472 b = v1472
  generalize n1614 b = v1614
  generalize n1725 b = v1725
  generalize n1805 b = v1805
  generalize n1902 b = v1902
  generalize n1967 b = v1967
  norm_num <;> ring

private theorem product2_3_0 (b : ℝ) :
    traceProduct b 2 3 0 = (traceJacobian b 2 * traceProduct b 1) 3 0 := by
  change n2100 b = _
  rw [mul5_entry_nested]
  change n2100 b = (n1615 b*n1333 b+(n1726 b*n1350 b+(n1806 b*n1370 b+(n1903 b*n1407 b+(n1974 b*n1444 b+0)))))
  simp only [n2092,n2093,n2094,n2095,n2096,n2097,n2098,n2099,n2100]
  generalize n1333 b = v1333
  generalize n1350 b = v1350
  generalize n1370 b = v1370
  generalize n1407 b = v1407
  generalize n1444 b = v1444
  generalize n1615 b = v1615
  generalize n1726 b = v1726
  generalize n1806 b = v1806
  generalize n1903 b = v1903
  generalize n1974 b = v1974
  norm_num <;> ring

private theorem product2_3_1 (b : ℝ) :
    traceProduct b 2 3 1 = (traceJacobian b 2 * traceProduct b 1) 3 1 := by
  change n2109 b = _
  rw [mul5_entry_nested]
  change n2109 b = (n1615 b*n1338 b+(n1726 b*n1355 b+(n1806 b*n1379 b+(n1903 b*n1416 b+(n1974 b*n1453 b+0)))))
  simp only [n2101,n2102,n2103,n2104,n2105,n2106,n2107,n2108,n2109]
  generalize n1338 b = v1338
  generalize n1355 b = v1355
  generalize n1379 b = v1379
  generalize n1416 b = v1416
  generalize n1453 b = v1453
  generalize n1615 b = v1615
  generalize n1726 b = v1726
  generalize n1806 b = v1806
  generalize n1903 b = v1903
  generalize n1974 b = v1974
  norm_num <;> ring

private theorem product2_3_2 (b : ℝ) :
    traceProduct b 2 3 2 = (traceJacobian b 2 * traceProduct b 1) 3 2 := by
  change n2118 b = _
  rw [mul5_entry_nested]
  change n2118 b = (n1615 b*n1341 b+(n1726 b*n1358 b+(n1806 b*n1386 b+(n1903 b*n1423 b+(n1974 b*n1460 b+0)))))
  simp only [n2110,n2111,n2112,n2113,n2114,n2115,n2116,n2117,n2118]
  generalize n1341 b = v1341
  generalize n1358 b = v1358
  generalize n1386 b = v1386
  generalize n1423 b = v1423
  generalize n1460 b = v1460
  generalize n1615 b = v1615
  generalize n1726 b = v1726
  generalize n1806 b = v1806
  generalize n1903 b = v1903
  generalize n1974 b = v1974
  norm_num <;> ring

private theorem product2_3_3 (b : ℝ) :
    traceProduct b 2 3 3 = (traceJacobian b 2 * traceProduct b 1) 3 3 := by
  change n2127 b = _
  rw [mul5_entry_nested]
  change n2127 b = (n1615 b*n1344 b+(n1726 b*n1361 b+(n1806 b*n1393 b+(n1903 b*n1430 b+(n1974 b*n1467 b+0)))))
  simp only [n2119,n2120,n2121,n2122,n2123,n2124,n2125,n2126,n2127]
  generalize n1344 b = v1344
  generalize n1361 b = v1361
  generalize n1393 b = v1393
  generalize n1430 b = v1430
  generalize n1467 b = v1467
  generalize n1615 b = v1615
  generalize n1726 b = v1726
  generalize n1806 b = v1806
  generalize n1903 b = v1903
  generalize n1974 b = v1974
  norm_num <;> ring

private theorem product2_3_4 (b : ℝ) :
    traceProduct b 2 3 4 = (traceJacobian b 2 * traceProduct b 1) 3 4 := by
  change n2136 b = _
  rw [mul5_entry_nested]
  change n2136 b = (n1615 b*n1345 b+(n1726 b*n1345 b+(n1806 b*n1398 b+(n1903 b*n1435 b+(n1974 b*n1472 b+0)))))
  simp only [n1345,n2128,n2129,n2130,n2131,n2132,n2133,n2134,n2135,n2136]
  generalize n1398 b = v1398
  generalize n1435 b = v1435
  generalize n1472 b = v1472
  generalize n1615 b = v1615
  generalize n1726 b = v1726
  generalize n1806 b = v1806
  generalize n1903 b = v1903
  generalize n1974 b = v1974
  norm_num <;> ring

private theorem product2_4_0 (b : ℝ) :
    traceProduct b 2 4 0 = (traceJacobian b 2 * traceProduct b 1) 4 0 := by
  change n2145 b = _
  rw [mul5_entry_nested]
  change n2145 b = (n1617 b*n1333 b+(n1728 b*n1350 b+(n1801 b*n1370 b+(n1905 b*n1407 b+(n1976 b*n1444 b+0)))))
  simp only [n2137,n2138,n2139,n2140,n2141,n2142,n2143,n2144,n2145]
  generalize n1333 b = v1333
  generalize n1350 b = v1350
  generalize n1370 b = v1370
  generalize n1407 b = v1407
  generalize n1444 b = v1444
  generalize n1617 b = v1617
  generalize n1728 b = v1728
  generalize n1801 b = v1801
  generalize n1905 b = v1905
  generalize n1976 b = v1976
  norm_num <;> ring

private theorem product2_4_1 (b : ℝ) :
    traceProduct b 2 4 1 = (traceJacobian b 2 * traceProduct b 1) 4 1 := by
  change n2154 b = _
  rw [mul5_entry_nested]
  change n2154 b = (n1617 b*n1338 b+(n1728 b*n1355 b+(n1801 b*n1379 b+(n1905 b*n1416 b+(n1976 b*n1453 b+0)))))
  simp only [n2146,n2147,n2148,n2149,n2150,n2151,n2152,n2153,n2154]
  generalize n1338 b = v1338
  generalize n1355 b = v1355
  generalize n1379 b = v1379
  generalize n1416 b = v1416
  generalize n1453 b = v1453
  generalize n1617 b = v1617
  generalize n1728 b = v1728
  generalize n1801 b = v1801
  generalize n1905 b = v1905
  generalize n1976 b = v1976
  norm_num <;> ring

private theorem product2_4_2 (b : ℝ) :
    traceProduct b 2 4 2 = (traceJacobian b 2 * traceProduct b 1) 4 2 := by
  change n2163 b = _
  rw [mul5_entry_nested]
  change n2163 b = (n1617 b*n1341 b+(n1728 b*n1358 b+(n1801 b*n1386 b+(n1905 b*n1423 b+(n1976 b*n1460 b+0)))))
  simp only [n2155,n2156,n2157,n2158,n2159,n2160,n2161,n2162,n2163]
  generalize n1341 b = v1341
  generalize n1358 b = v1358
  generalize n1386 b = v1386
  generalize n1423 b = v1423
  generalize n1460 b = v1460
  generalize n1617 b = v1617
  generalize n1728 b = v1728
  generalize n1801 b = v1801
  generalize n1905 b = v1905
  generalize n1976 b = v1976
  norm_num <;> ring

private theorem product2_4_3 (b : ℝ) :
    traceProduct b 2 4 3 = (traceJacobian b 2 * traceProduct b 1) 4 3 := by
  change n2172 b = _
  rw [mul5_entry_nested]
  change n2172 b = (n1617 b*n1344 b+(n1728 b*n1361 b+(n1801 b*n1393 b+(n1905 b*n1430 b+(n1976 b*n1467 b+0)))))
  simp only [n2164,n2165,n2166,n2167,n2168,n2169,n2170,n2171,n2172]
  generalize n1344 b = v1344
  generalize n1361 b = v1361
  generalize n1393 b = v1393
  generalize n1430 b = v1430
  generalize n1467 b = v1467
  generalize n1617 b = v1617
  generalize n1728 b = v1728
  generalize n1801 b = v1801
  generalize n1905 b = v1905
  generalize n1976 b = v1976
  norm_num <;> ring

private theorem product2_4_4 (b : ℝ) :
    traceProduct b 2 4 4 = (traceJacobian b 2 * traceProduct b 1) 4 4 := by
  change n2181 b = _
  rw [mul5_entry_nested]
  change n2181 b = (n1617 b*n1345 b+(n1728 b*n1345 b+(n1801 b*n1398 b+(n1905 b*n1435 b+(n1976 b*n1472 b+0)))))
  simp only [n1345,n2173,n2174,n2175,n2176,n2177,n2178,n2179,n2180,n2181]
  generalize n1398 b = v1398
  generalize n1435 b = v1435
  generalize n1472 b = v1472
  generalize n1617 b = v1617
  generalize n1728 b = v1728
  generalize n1801 b = v1801
  generalize n1905 b = v1905
  generalize n1976 b = v1976
  norm_num <;> ring

theorem traceProduct_2 (b : ℝ) : traceProduct b 2 = traceJacobian b 2 * traceProduct b 1 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact product2_0_0 b
  · exact product2_0_1 b
  · exact product2_0_2 b
  · exact product2_0_3 b
  · exact product2_0_4 b
  · exact product2_1_0 b
  · exact product2_1_1 b
  · exact product2_1_2 b
  · exact product2_1_3 b
  · exact product2_1_4 b
  · exact product2_2_0 b
  · exact product2_2_1 b
  · exact product2_2_2 b
  · exact product2_2_3 b
  · exact product2_2_4 b
  · exact product2_3_0 b
  · exact product2_3_1 b
  · exact product2_3_2 b
  · exact product2_3_3 b
  · exact product2_3_4 b
  · exact product2_4_0 b
  · exact product2_4_1 b
  · exact product2_4_2 b
  · exact product2_4_3 b
  · exact product2_4_4 b

private theorem product3_0_0 (b : ℝ) :
    traceProduct b 3 0 0 = (traceJacobian b 3 * traceProduct b 2) 0 0 := by
  change n2688 b = _
  rw [mul5_entry_nested]
  change n2688 b = (n2190 b*n1983 b+(n2333 b*n2018 b+(n330 b*n2055 b+(n331 b*n2100 b+(n66 b*n2145 b+0)))))
  simp only [n66,n2682,n2683,n2684,n2685,n2686,n2687,n2688]
  generalize n330 b = v330
  generalize n331 b = v331
  generalize n1983 b = v1983
  generalize n2018 b = v2018
  generalize n2055 b = v2055
  generalize n2100 b = v2100
  generalize n2145 b = v2145
  generalize n2190 b = v2190
  generalize n2333 b = v2333
  norm_num <;> ring

private theorem product3_0_1 (b : ℝ) :
    traceProduct b 3 0 1 = (traceJacobian b 3 * traceProduct b 2) 0 1 := by
  change n2695 b = _
  rw [mul5_entry_nested]
  change n2695 b = (n2190 b*n1990 b+(n2333 b*n2025 b+(n330 b*n2064 b+(n331 b*n2109 b+(n66 b*n2154 b+0)))))
  simp only [n66,n2689,n2690,n2691,n2692,n2693,n2694,n2695]
  generalize n330 b = v330
  generalize n331 b = v331
  generalize n1990 b = v1990
  generalize n2025 b = v2025
  generalize n2064 b = v2064
  generalize n2109 b = v2109
  generalize n2154 b = v2154
  generalize n2190 b = v2190
  generalize n2333 b = v2333
  norm_num <;> ring

private theorem product3_0_2 (b : ℝ) :
    traceProduct b 3 0 2 = (traceJacobian b 3 * traceProduct b 2) 0 2 := by
  change n2702 b = _
  rw [mul5_entry_nested]
  change n2702 b = (n2190 b*n1997 b+(n2333 b*n2032 b+(n330 b*n2073 b+(n331 b*n2118 b+(n66 b*n2163 b+0)))))
  simp only [n66,n2696,n2697,n2698,n2699,n2700,n2701,n2702]
  generalize n330 b = v330
  generalize n331 b = v331
  generalize n1997 b = v1997
  generalize n2032 b = v2032
  generalize n2073 b = v2073
  generalize n2118 b = v2118
  generalize n2163 b = v2163
  generalize n2190 b = v2190
  generalize n2333 b = v2333
  norm_num <;> ring

private theorem product3_0_3 (b : ℝ) :
    traceProduct b 3 0 3 = (traceJacobian b 3 * traceProduct b 2) 0 3 := by
  change n2709 b = _
  rw [mul5_entry_nested]
  change n2709 b = (n2190 b*n2004 b+(n2333 b*n2039 b+(n330 b*n2082 b+(n331 b*n2127 b+(n66 b*n2172 b+0)))))
  simp only [n66,n2703,n2704,n2705,n2706,n2707,n2708,n2709]
  generalize n330 b = v330
  generalize n331 b = v331
  generalize n2004 b = v2004
  generalize n2039 b = v2039
  generalize n2082 b = v2082
  generalize n2127 b = v2127
  generalize n2172 b = v2172
  generalize n2190 b = v2190
  generalize n2333 b = v2333
  norm_num <;> ring

private theorem product3_0_4 (b : ℝ) :
    traceProduct b 3 0 4 = (traceJacobian b 3 * traceProduct b 2) 0 4 := by
  change n2716 b = _
  rw [mul5_entry_nested]
  change n2716 b = (n2190 b*n2011 b+(n2333 b*n2046 b+(n330 b*n2091 b+(n331 b*n2136 b+(n66 b*n2181 b+0)))))
  simp only [n66,n2710,n2711,n2712,n2713,n2714,n2715,n2716]
  generalize n330 b = v330
  generalize n331 b = v331
  generalize n2011 b = v2011
  generalize n2046 b = v2046
  generalize n2091 b = v2091
  generalize n2136 b = v2136
  generalize n2181 b = v2181
  generalize n2190 b = v2190
  generalize n2333 b = v2333
  norm_num <;> ring

private theorem product3_1_0 (b : ℝ) :
    traceProduct b 3 1 0 = (traceJacobian b 3 * traceProduct b 2) 1 0 := by
  change n2723 b = _
  rw [mul5_entry_nested]
  change n2723 b = (n2189 b*n1983 b+(n2335 b*n2018 b+(n66 b*n2055 b+(n330 b*n2100 b+(n331 b*n2145 b+0)))))
  simp only [n66,n2717,n2718,n2719,n2720,n2721,n2722,n2723]
  generalize n330 b = v330
  generalize n331 b = v331
  generalize n1983 b = v1983
  generalize n2018 b = v2018
  generalize n2055 b = v2055
  generalize n2100 b = v2100
  generalize n2145 b = v2145
  generalize n2189 b = v2189
  generalize n2335 b = v2335
  norm_num <;> ring

private theorem product3_1_1 (b : ℝ) :
    traceProduct b 3 1 1 = (traceJacobian b 3 * traceProduct b 2) 1 1 := by
  change n2730 b = _
  rw [mul5_entry_nested]
  change n2730 b = (n2189 b*n1990 b+(n2335 b*n2025 b+(n66 b*n2064 b+(n330 b*n2109 b+(n331 b*n2154 b+0)))))
  simp only [n66,n2724,n2725,n2726,n2727,n2728,n2729,n2730]
  generalize n330 b = v330
  generalize n331 b = v331
  generalize n1990 b = v1990
  generalize n2025 b = v2025
  generalize n2064 b = v2064
  generalize n2109 b = v2109
  generalize n2154 b = v2154
  generalize n2189 b = v2189
  generalize n2335 b = v2335
  norm_num <;> ring

private theorem product3_1_2 (b : ℝ) :
    traceProduct b 3 1 2 = (traceJacobian b 3 * traceProduct b 2) 1 2 := by
  change n2737 b = _
  rw [mul5_entry_nested]
  change n2737 b = (n2189 b*n1997 b+(n2335 b*n2032 b+(n66 b*n2073 b+(n330 b*n2118 b+(n331 b*n2163 b+0)))))
  simp only [n66,n2731,n2732,n2733,n2734,n2735,n2736,n2737]
  generalize n330 b = v330
  generalize n331 b = v331
  generalize n1997 b = v1997
  generalize n2032 b = v2032
  generalize n2073 b = v2073
  generalize n2118 b = v2118
  generalize n2163 b = v2163
  generalize n2189 b = v2189
  generalize n2335 b = v2335
  norm_num <;> ring

private theorem product3_1_3 (b : ℝ) :
    traceProduct b 3 1 3 = (traceJacobian b 3 * traceProduct b 2) 1 3 := by
  change n2744 b = _
  rw [mul5_entry_nested]
  change n2744 b = (n2189 b*n2004 b+(n2335 b*n2039 b+(n66 b*n2082 b+(n330 b*n2127 b+(n331 b*n2172 b+0)))))
  simp only [n66,n2738,n2739,n2740,n2741,n2742,n2743,n2744]
  generalize n330 b = v330
  generalize n331 b = v331
  generalize n2004 b = v2004
  generalize n2039 b = v2039
  generalize n2082 b = v2082
  generalize n2127 b = v2127
  generalize n2172 b = v2172
  generalize n2189 b = v2189
  generalize n2335 b = v2335
  norm_num <;> ring

private theorem product3_1_4 (b : ℝ) :
    traceProduct b 3 1 4 = (traceJacobian b 3 * traceProduct b 2) 1 4 := by
  change n2751 b = _
  rw [mul5_entry_nested]
  change n2751 b = (n2189 b*n2011 b+(n2335 b*n2046 b+(n66 b*n2091 b+(n330 b*n2136 b+(n331 b*n2181 b+0)))))
  simp only [n66,n2745,n2746,n2747,n2748,n2749,n2750,n2751]
  generalize n330 b = v330
  generalize n331 b = v331
  generalize n2011 b = v2011
  generalize n2046 b = v2046
  generalize n2091 b = v2091
  generalize n2136 b = v2136
  generalize n2181 b = v2181
  generalize n2189 b = v2189
  generalize n2335 b = v2335
  norm_num <;> ring

private theorem product3_2_0 (b : ℝ) :
    traceProduct b 3 2 0 = (traceJacobian b 3 * traceProduct b 2) 2 0 := by
  change n2760 b = _
  rw [mul5_entry_nested]
  change n2760 b = (n2323 b*n1983 b+(n2434 b*n2018 b+(n2514 b*n2055 b+(n2608 b*n2100 b+(n2672 b*n2145 b+0)))))
  simp only [n2752,n2753,n2754,n2755,n2756,n2757,n2758,n2759,n2760]
  generalize n1983 b = v1983
  generalize n2018 b = v2018
  generalize n2055 b = v2055
  generalize n2100 b = v2100
  generalize n2145 b = v2145
  generalize n2323 b = v2323
  generalize n2434 b = v2434
  generalize n2514 b = v2514
  generalize n2608 b = v2608
  generalize n2672 b = v2672
  norm_num <;> ring

private theorem product3_2_1 (b : ℝ) :
    traceProduct b 3 2 1 = (traceJacobian b 3 * traceProduct b 2) 2 1 := by
  change n2769 b = _
  rw [mul5_entry_nested]
  change n2769 b = (n2323 b*n1990 b+(n2434 b*n2025 b+(n2514 b*n2064 b+(n2608 b*n2109 b+(n2672 b*n2154 b+0)))))
  simp only [n2761,n2762,n2763,n2764,n2765,n2766,n2767,n2768,n2769]
  generalize n1990 b = v1990
  generalize n2025 b = v2025
  generalize n2064 b = v2064
  generalize n2109 b = v2109
  generalize n2154 b = v2154
  generalize n2323 b = v2323
  generalize n2434 b = v2434
  generalize n2514 b = v2514
  generalize n2608 b = v2608
  generalize n2672 b = v2672
  norm_num <;> ring

private theorem product3_2_2 (b : ℝ) :
    traceProduct b 3 2 2 = (traceJacobian b 3 * traceProduct b 2) 2 2 := by
  change n2778 b = _
  rw [mul5_entry_nested]
  change n2778 b = (n2323 b*n1997 b+(n2434 b*n2032 b+(n2514 b*n2073 b+(n2608 b*n2118 b+(n2672 b*n2163 b+0)))))
  simp only [n2770,n2771,n2772,n2773,n2774,n2775,n2776,n2777,n2778]
  generalize n1997 b = v1997
  generalize n2032 b = v2032
  generalize n2073 b = v2073
  generalize n2118 b = v2118
  generalize n2163 b = v2163
  generalize n2323 b = v2323
  generalize n2434 b = v2434
  generalize n2514 b = v2514
  generalize n2608 b = v2608
  generalize n2672 b = v2672
  norm_num <;> ring

private theorem product3_2_3 (b : ℝ) :
    traceProduct b 3 2 3 = (traceJacobian b 3 * traceProduct b 2) 2 3 := by
  change n2787 b = _
  rw [mul5_entry_nested]
  change n2787 b = (n2323 b*n2004 b+(n2434 b*n2039 b+(n2514 b*n2082 b+(n2608 b*n2127 b+(n2672 b*n2172 b+0)))))
  simp only [n2779,n2780,n2781,n2782,n2783,n2784,n2785,n2786,n2787]
  generalize n2004 b = v2004
  generalize n2039 b = v2039
  generalize n2082 b = v2082
  generalize n2127 b = v2127
  generalize n2172 b = v2172
  generalize n2323 b = v2323
  generalize n2434 b = v2434
  generalize n2514 b = v2514
  generalize n2608 b = v2608
  generalize n2672 b = v2672
  norm_num <;> ring

private theorem product3_2_4 (b : ℝ) :
    traceProduct b 3 2 4 = (traceJacobian b 3 * traceProduct b 2) 2 4 := by
  change n2796 b = _
  rw [mul5_entry_nested]
  change n2796 b = (n2323 b*n2011 b+(n2434 b*n2046 b+(n2514 b*n2091 b+(n2608 b*n2136 b+(n2672 b*n2181 b+0)))))
  simp only [n2788,n2789,n2790,n2791,n2792,n2793,n2794,n2795,n2796]
  generalize n2011 b = v2011
  generalize n2046 b = v2046
  generalize n2091 b = v2091
  generalize n2136 b = v2136
  generalize n2181 b = v2181
  generalize n2323 b = v2323
  generalize n2434 b = v2434
  generalize n2514 b = v2514
  generalize n2608 b = v2608
  generalize n2672 b = v2672
  norm_num <;> ring

private theorem product3_3_0 (b : ℝ) :
    traceProduct b 3 3 0 = (traceJacobian b 3 * traceProduct b 2) 3 0 := by
  change n2805 b = _
  rw [mul5_entry_nested]
  change n2805 b = (n2324 b*n1983 b+(n2435 b*n2018 b+(n2515 b*n2055 b+(n2609 b*n2100 b+(n2679 b*n2145 b+0)))))
  simp only [n2797,n2798,n2799,n2800,n2801,n2802,n2803,n2804,n2805]
  generalize n1983 b = v1983
  generalize n2018 b = v2018
  generalize n2055 b = v2055
  generalize n2100 b = v2100
  generalize n2145 b = v2145
  generalize n2324 b = v2324
  generalize n2435 b = v2435
  generalize n2515 b = v2515
  generalize n2609 b = v2609
  generalize n2679 b = v2679
  norm_num <;> ring

private theorem product3_3_1 (b : ℝ) :
    traceProduct b 3 3 1 = (traceJacobian b 3 * traceProduct b 2) 3 1 := by
  change n2814 b = _
  rw [mul5_entry_nested]
  change n2814 b = (n2324 b*n1990 b+(n2435 b*n2025 b+(n2515 b*n2064 b+(n2609 b*n2109 b+(n2679 b*n2154 b+0)))))
  simp only [n2806,n2807,n2808,n2809,n2810,n2811,n2812,n2813,n2814]
  generalize n1990 b = v1990
  generalize n2025 b = v2025
  generalize n2064 b = v2064
  generalize n2109 b = v2109
  generalize n2154 b = v2154
  generalize n2324 b = v2324
  generalize n2435 b = v2435
  generalize n2515 b = v2515
  generalize n2609 b = v2609
  generalize n2679 b = v2679
  norm_num <;> ring

private theorem product3_3_2 (b : ℝ) :
    traceProduct b 3 3 2 = (traceJacobian b 3 * traceProduct b 2) 3 2 := by
  change n2823 b = _
  rw [mul5_entry_nested]
  change n2823 b = (n2324 b*n1997 b+(n2435 b*n2032 b+(n2515 b*n2073 b+(n2609 b*n2118 b+(n2679 b*n2163 b+0)))))
  simp only [n2815,n2816,n2817,n2818,n2819,n2820,n2821,n2822,n2823]
  generalize n1997 b = v1997
  generalize n2032 b = v2032
  generalize n2073 b = v2073
  generalize n2118 b = v2118
  generalize n2163 b = v2163
  generalize n2324 b = v2324
  generalize n2435 b = v2435
  generalize n2515 b = v2515
  generalize n2609 b = v2609
  generalize n2679 b = v2679
  norm_num <;> ring

private theorem product3_3_3 (b : ℝ) :
    traceProduct b 3 3 3 = (traceJacobian b 3 * traceProduct b 2) 3 3 := by
  change n2832 b = _
  rw [mul5_entry_nested]
  change n2832 b = (n2324 b*n2004 b+(n2435 b*n2039 b+(n2515 b*n2082 b+(n2609 b*n2127 b+(n2679 b*n2172 b+0)))))
  simp only [n2824,n2825,n2826,n2827,n2828,n2829,n2830,n2831,n2832]
  generalize n2004 b = v2004
  generalize n2039 b = v2039
  generalize n2082 b = v2082
  generalize n2127 b = v2127
  generalize n2172 b = v2172
  generalize n2324 b = v2324
  generalize n2435 b = v2435
  generalize n2515 b = v2515
  generalize n2609 b = v2609
  generalize n2679 b = v2679
  norm_num <;> ring

private theorem product3_3_4 (b : ℝ) :
    traceProduct b 3 3 4 = (traceJacobian b 3 * traceProduct b 2) 3 4 := by
  change n2841 b = _
  rw [mul5_entry_nested]
  change n2841 b = (n2324 b*n2011 b+(n2435 b*n2046 b+(n2515 b*n2091 b+(n2609 b*n2136 b+(n2679 b*n2181 b+0)))))
  simp only [n2833,n2834,n2835,n2836,n2837,n2838,n2839,n2840,n2841]
  generalize n2011 b = v2011
  generalize n2046 b = v2046
  generalize n2091 b = v2091
  generalize n2136 b = v2136
  generalize n2181 b = v2181
  generalize n2324 b = v2324
  generalize n2435 b = v2435
  generalize n2515 b = v2515
  generalize n2609 b = v2609
  generalize n2679 b = v2679
  norm_num <;> ring

private theorem product3_4_0 (b : ℝ) :
    traceProduct b 3 4 0 = (traceJacobian b 3 * traceProduct b 2) 4 0 := by
  change n2850 b = _
  rw [mul5_entry_nested]
  change n2850 b = (n2326 b*n1983 b+(n2437 b*n2018 b+(n2510 b*n2055 b+(n2611 b*n2100 b+(n2681 b*n2145 b+0)))))
  simp only [n2842,n2843,n2844,n2845,n2846,n2847,n2848,n2849,n2850]
  generalize n1983 b = v1983
  generalize n2018 b = v2018
  generalize n2055 b = v2055
  generalize n2100 b = v2100
  generalize n2145 b = v2145
  generalize n2326 b = v2326
  generalize n2437 b = v2437
  generalize n2510 b = v2510
  generalize n2611 b = v2611
  generalize n2681 b = v2681
  norm_num <;> ring

private theorem product3_4_1 (b : ℝ) :
    traceProduct b 3 4 1 = (traceJacobian b 3 * traceProduct b 2) 4 1 := by
  change n2859 b = _
  rw [mul5_entry_nested]
  change n2859 b = (n2326 b*n1990 b+(n2437 b*n2025 b+(n2510 b*n2064 b+(n2611 b*n2109 b+(n2681 b*n2154 b+0)))))
  simp only [n2851,n2852,n2853,n2854,n2855,n2856,n2857,n2858,n2859]
  generalize n1990 b = v1990
  generalize n2025 b = v2025
  generalize n2064 b = v2064
  generalize n2109 b = v2109
  generalize n2154 b = v2154
  generalize n2326 b = v2326
  generalize n2437 b = v2437
  generalize n2510 b = v2510
  generalize n2611 b = v2611
  generalize n2681 b = v2681
  norm_num <;> ring

private theorem product3_4_2 (b : ℝ) :
    traceProduct b 3 4 2 = (traceJacobian b 3 * traceProduct b 2) 4 2 := by
  change n2868 b = _
  rw [mul5_entry_nested]
  change n2868 b = (n2326 b*n1997 b+(n2437 b*n2032 b+(n2510 b*n2073 b+(n2611 b*n2118 b+(n2681 b*n2163 b+0)))))
  simp only [n2860,n2861,n2862,n2863,n2864,n2865,n2866,n2867,n2868]
  generalize n1997 b = v1997
  generalize n2032 b = v2032
  generalize n2073 b = v2073
  generalize n2118 b = v2118
  generalize n2163 b = v2163
  generalize n2326 b = v2326
  generalize n2437 b = v2437
  generalize n2510 b = v2510
  generalize n2611 b = v2611
  generalize n2681 b = v2681
  norm_num <;> ring

private theorem product3_4_3 (b : ℝ) :
    traceProduct b 3 4 3 = (traceJacobian b 3 * traceProduct b 2) 4 3 := by
  change n2877 b = _
  rw [mul5_entry_nested]
  change n2877 b = (n2326 b*n2004 b+(n2437 b*n2039 b+(n2510 b*n2082 b+(n2611 b*n2127 b+(n2681 b*n2172 b+0)))))
  simp only [n2869,n2870,n2871,n2872,n2873,n2874,n2875,n2876,n2877]
  generalize n2004 b = v2004
  generalize n2039 b = v2039
  generalize n2082 b = v2082
  generalize n2127 b = v2127
  generalize n2172 b = v2172
  generalize n2326 b = v2326
  generalize n2437 b = v2437
  generalize n2510 b = v2510
  generalize n2611 b = v2611
  generalize n2681 b = v2681
  norm_num <;> ring

private theorem product3_4_4 (b : ℝ) :
    traceProduct b 3 4 4 = (traceJacobian b 3 * traceProduct b 2) 4 4 := by
  change n2886 b = _
  rw [mul5_entry_nested]
  change n2886 b = (n2326 b*n2011 b+(n2437 b*n2046 b+(n2510 b*n2091 b+(n2611 b*n2136 b+(n2681 b*n2181 b+0)))))
  simp only [n2878,n2879,n2880,n2881,n2882,n2883,n2884,n2885,n2886]
  generalize n2011 b = v2011
  generalize n2046 b = v2046
  generalize n2091 b = v2091
  generalize n2136 b = v2136
  generalize n2181 b = v2181
  generalize n2326 b = v2326
  generalize n2437 b = v2437
  generalize n2510 b = v2510
  generalize n2611 b = v2611
  generalize n2681 b = v2681
  norm_num <;> ring

theorem traceProduct_3 (b : ℝ) : traceProduct b 3 = traceJacobian b 3 * traceProduct b 2 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact product3_0_0 b
  · exact product3_0_1 b
  · exact product3_0_2 b
  · exact product3_0_3 b
  · exact product3_0_4 b
  · exact product3_1_0 b
  · exact product3_1_1 b
  · exact product3_1_2 b
  · exact product3_1_3 b
  · exact product3_1_4 b
  · exact product3_2_0 b
  · exact product3_2_1 b
  · exact product3_2_2 b
  · exact product3_2_3 b
  · exact product3_2_4 b
  · exact product3_3_0 b
  · exact product3_3_1 b
  · exact product3_3_2 b
  · exact product3_3_3 b
  · exact product3_3_4 b
  · exact product3_4_0 b
  · exact product3_4_1 b
  · exact product3_4_2 b
  · exact product3_4_3 b
  · exact product3_4_4 b

theorem traceReturnDerivative_eq (b : ℝ) :
    traceReturnDerivative b = (1/r) • (traceJacobian b 3 * (traceJacobian b 2 * (traceJacobian b 1 * traceJacobian b 0))) := by
  rw [← traceProduct_zero b,← traceProduct_1 b,← traceProduct_2 b,← traceProduct_3 b]
  ext i j
  fin_cases i <;> fin_cases j
  · change n2887 b = (1/r)*n2688 b
    simp only [n2887,n228]
    norm_num [r]
    ring
  · change n2888 b = (1/r)*n2695 b
    simp only [n2888,n228]
    norm_num [r]
    ring
  · change n2889 b = (1/r)*n2702 b
    simp only [n2889,n228]
    norm_num [r]
    ring
  · change n2890 b = (1/r)*n2709 b
    simp only [n2890,n228]
    norm_num [r]
    ring
  · change n2891 b = (1/r)*n2716 b
    simp only [n2891,n228]
    norm_num [r]
    ring
  · change n2892 b = (1/r)*n2723 b
    simp only [n2892,n228]
    norm_num [r]
    ring
  · change n2893 b = (1/r)*n2730 b
    simp only [n2893,n228]
    norm_num [r]
    ring
  · change n2894 b = (1/r)*n2737 b
    simp only [n2894,n228]
    norm_num [r]
    ring
  · change n2895 b = (1/r)*n2744 b
    simp only [n2895,n228]
    norm_num [r]
    ring
  · change n2896 b = (1/r)*n2751 b
    simp only [n2896,n228]
    norm_num [r]
    ring
  · change n2897 b = (1/r)*n2760 b
    simp only [n2897,n228]
    norm_num [r]
    ring
  · change n2898 b = (1/r)*n2769 b
    simp only [n2898,n228]
    norm_num [r]
    ring
  · change n2899 b = (1/r)*n2778 b
    simp only [n2899,n228]
    norm_num [r]
    ring
  · change n2900 b = (1/r)*n2787 b
    simp only [n2900,n228]
    norm_num [r]
    ring
  · change n2901 b = (1/r)*n2796 b
    simp only [n2901,n228]
    norm_num [r]
    ring
  · change n2902 b = (1/r)*n2805 b
    simp only [n2902,n228]
    norm_num [r]
    ring
  · change n2903 b = (1/r)*n2814 b
    simp only [n2903,n228]
    norm_num [r]
    ring
  · change n2904 b = (1/r)*n2823 b
    simp only [n2904,n228]
    norm_num [r]
    ring
  · change n2905 b = (1/r)*n2832 b
    simp only [n2905,n228]
    norm_num [r]
    ring
  · change n2906 b = (1/r)*n2841 b
    simp only [n2906,n228]
    norm_num [r]
    ring
  · change n2907 b = (1/r)*n2850 b
    simp only [n2907,n228]
    norm_num [r]
    ring
  · change n2908 b = (1/r)*n2859 b
    simp only [n2908,n228]
    norm_num [r]
    ring
  · change n2909 b = (1/r)*n2868 b
    simp only [n2909,n228]
    norm_num [r]
    ring
  · change n2910 b = (1/r)*n2877 b
    simp only [n2910,n228]
    norm_num [r]
    ring
  · change n2911 b = (1/r)*n2886 b
    simp only [n2911,n228]
    norm_num [r]
    ring

private theorem mul4_entry_nested (A B : Matrix4) (i j : Fin 4) :
    (A*B) i j = A i 0*B 0 j+(A i 1*B 1 j+(A i 2*B 2 j+(A i 3*B 3 j+0))) := by
  simp only [Matrix.mul_apply,Fin.sum_univ_succ,Fin.sum_univ_zero]
  rfl
theorem transverseConjugator_left_inverse : transverseConjugator * transverseConjugatorInv = 1 := by
  ext i j
  rw [mul4_entry_nested]
  fin_cases i <;> fin_cases j
  · change (464*(521647187/22230591050:ℝ)+(1077*(-574350721/11115295525:ℝ)+(4501*(123292286/11115295525:ℝ)+(-1708*(27089991/11115295525:ℝ)+0)))) = 1
    norm_num
  · change (464*(-118215737/22230591050:ℝ)+(1077*(888696/11115295525:ℝ)+(4501*(8549264/11115295525:ℝ)+(-1708*(7032384/11115295525:ℝ)+0)))) = 0
    norm_num
  · change (464*(23413073/4446118210:ℝ)+(1077*(-118410819/2223059105:ℝ)+(4501*(30921059/2223059105:ℝ)+(-1708*(9999454/2223059105:ℝ)+0)))) = 0
    norm_num
  · change (464*(-183928858/11115295525:ℝ)+(1077*(2783828/11115295525:ℝ)+(4501*(23578552/11115295525:ℝ)+(-1708*(13924037/11115295525:ℝ)+0)))) = 0
    norm_num
  · change (1366*(521647187/22230591050:ℝ)+(2793*(-574350721/11115295525:ℝ)+(10000*(123292286/11115295525:ℝ)+(552*(27089991/11115295525:ℝ)+0)))) = 0
    norm_num
  · change (1366*(-118215737/22230591050:ℝ)+(2793*(888696/11115295525:ℝ)+(10000*(8549264/11115295525:ℝ)+(552*(7032384/11115295525:ℝ)+0)))) = 1
    norm_num
  · change (1366*(23413073/4446118210:ℝ)+(2793*(-118410819/2223059105:ℝ)+(10000*(30921059/2223059105:ℝ)+(552*(9999454/2223059105:ℝ)+0)))) = 0
    norm_num
  · change (1366*(-183928858/11115295525:ℝ)+(2793*(2783828/11115295525:ℝ)+(10000*(23578552/11115295525:ℝ)+(552*(13924037/11115295525:ℝ)+0)))) = 0
    norm_num
  · change (-448*(521647187/22230591050:ℝ)+(-1058*(-574350721/11115295525:ℝ)+(-4343*(123292286/11115295525:ℝ)+(1648*(27089991/11115295525:ℝ)+0)))) = 0
    norm_num
  · change (-448*(-118215737/22230591050:ℝ)+(-1058*(888696/11115295525:ℝ)+(-4343*(8549264/11115295525:ℝ)+(1648*(7032384/11115295525:ℝ)+0)))) = 0
    norm_num
  · change (-448*(23413073/4446118210:ℝ)+(-1058*(-118410819/2223059105:ℝ)+(-4343*(30921059/2223059105:ℝ)+(1648*(9999454/2223059105:ℝ)+0)))) = 1
    norm_num
  · change (-448*(-183928858/11115295525:ℝ)+(-1058*(2783828/11115295525:ℝ)+(-4343*(23578552/11115295525:ℝ)+(1648*(13924037/11115295525:ℝ)+0)))) = 0
    norm_num
  · change (16*(521647187/22230591050:ℝ)+(293*(-574350721/11115295525:ℝ)+(1787*(123292286/11115295525:ℝ)+(-2075*(27089991/11115295525:ℝ)+0)))) = 0
    norm_num
  · change (16*(-118215737/22230591050:ℝ)+(293*(888696/11115295525:ℝ)+(1787*(8549264/11115295525:ℝ)+(-2075*(7032384/11115295525:ℝ)+0)))) = 0
    norm_num
  · change (16*(23413073/4446118210:ℝ)+(293*(-118410819/2223059105:ℝ)+(1787*(30921059/2223059105:ℝ)+(-2075*(9999454/2223059105:ℝ)+0)))) = 0
    norm_num
  · change (16*(-183928858/11115295525:ℝ)+(293*(2783828/11115295525:ℝ)+(1787*(23578552/11115295525:ℝ)+(-2075*(13924037/11115295525:ℝ)+0)))) = 1
    norm_num

theorem transverseConjugator_right_inverse : transverseConjugatorInv * transverseConjugator = 1 := by
  ext i j
  rw [mul4_entry_nested]
  fin_cases i <;> fin_cases j
  · change ((521647187/22230591050:ℝ)*464+((-118215737/22230591050:ℝ)*1366+((23413073/4446118210:ℝ)*-448+((-183928858/11115295525:ℝ)*16+0)))) = 1
    norm_num
  · change ((521647187/22230591050:ℝ)*1077+((-118215737/22230591050:ℝ)*2793+((23413073/4446118210:ℝ)*-1058+((-183928858/11115295525:ℝ)*293+0)))) = 0
    norm_num
  · change ((521647187/22230591050:ℝ)*4501+((-118215737/22230591050:ℝ)*10000+((23413073/4446118210:ℝ)*-4343+((-183928858/11115295525:ℝ)*1787+0)))) = 0
    norm_num
  · change ((521647187/22230591050:ℝ)*-1708+((-118215737/22230591050:ℝ)*552+((23413073/4446118210:ℝ)*1648+((-183928858/11115295525:ℝ)*-2075+0)))) = 0
    norm_num
  · change ((-574350721/11115295525:ℝ)*464+((888696/11115295525:ℝ)*1366+((-118410819/2223059105:ℝ)*-448+((2783828/11115295525:ℝ)*16+0)))) = 0
    norm_num
  · change ((-574350721/11115295525:ℝ)*1077+((888696/11115295525:ℝ)*2793+((-118410819/2223059105:ℝ)*-1058+((2783828/11115295525:ℝ)*293+0)))) = 1
    norm_num
  · change ((-574350721/11115295525:ℝ)*4501+((888696/11115295525:ℝ)*10000+((-118410819/2223059105:ℝ)*-4343+((2783828/11115295525:ℝ)*1787+0)))) = 0
    norm_num
  · change ((-574350721/11115295525:ℝ)*-1708+((888696/11115295525:ℝ)*552+((-118410819/2223059105:ℝ)*1648+((2783828/11115295525:ℝ)*-2075+0)))) = 0
    norm_num
  · change ((123292286/11115295525:ℝ)*464+((8549264/11115295525:ℝ)*1366+((30921059/2223059105:ℝ)*-448+((23578552/11115295525:ℝ)*16+0)))) = 0
    norm_num
  · change ((123292286/11115295525:ℝ)*1077+((8549264/11115295525:ℝ)*2793+((30921059/2223059105:ℝ)*-1058+((23578552/11115295525:ℝ)*293+0)))) = 0
    norm_num
  · change ((123292286/11115295525:ℝ)*4501+((8549264/11115295525:ℝ)*10000+((30921059/2223059105:ℝ)*-4343+((23578552/11115295525:ℝ)*1787+0)))) = 1
    norm_num
  · change ((123292286/11115295525:ℝ)*-1708+((8549264/11115295525:ℝ)*552+((30921059/2223059105:ℝ)*1648+((23578552/11115295525:ℝ)*-2075+0)))) = 0
    norm_num
  · change ((27089991/11115295525:ℝ)*464+((7032384/11115295525:ℝ)*1366+((9999454/2223059105:ℝ)*-448+((13924037/11115295525:ℝ)*16+0)))) = 0
    norm_num
  · change ((27089991/11115295525:ℝ)*1077+((7032384/11115295525:ℝ)*2793+((9999454/2223059105:ℝ)*-1058+((13924037/11115295525:ℝ)*293+0)))) = 0
    norm_num
  · change ((27089991/11115295525:ℝ)*4501+((7032384/11115295525:ℝ)*10000+((9999454/2223059105:ℝ)*-4343+((13924037/11115295525:ℝ)*1787+0)))) = 0
    norm_num
  · change ((27089991/11115295525:ℝ)*-1708+((7032384/11115295525:ℝ)*552+((9999454/2223059105:ℝ)*1648+((13924037/11115295525:ℝ)*-2075+0)))) = 1
    norm_num

private theorem conjugated_0_0 (b : ℝ) :
    traceConjugatedTransverse b 0 0 =
      (transverseConjugator * traceTransverse b * transverseConjugatorInv) 0 0 := by
  rw [mul4_entry_nested]
  simp only [mul4_entry_nested]
  change n3098 b = (((464:ℝ)*(n2887 b - n136 b * n2897 b)+((1077:ℝ)*(n2892 b - n150 b * n2897 b)+((4501:ℝ)*(n2902 b - n64 b * n2897 b)+((-1708:ℝ)*(n2907 b - n61 b * n2897 b)+0))))*(521647187/22230591050:ℝ)+(((464:ℝ)*(n2888 b - n136 b * n2898 b)+((1077:ℝ)*(n2893 b - n150 b * n2898 b)+((4501:ℝ)*(n2903 b - n64 b * n2898 b)+((-1708:ℝ)*(n2908 b - n61 b * n2898 b)+0))))*(-574350721/11115295525:ℝ)+(((464:ℝ)*(n2890 b - n136 b * n2900 b)+((1077:ℝ)*(n2895 b - n150 b * n2900 b)+((4501:ℝ)*(n2905 b - n64 b * n2900 b)+((-1708:ℝ)*(n2910 b - n61 b * n2900 b)+0))))*(123292286/11115295525:ℝ)+(((464:ℝ)*(n2891 b - n136 b * n2901 b)+((1077:ℝ)*(n2896 b - n150 b * n2901 b)+((4501:ℝ)*(n2906 b - n64 b * n2901 b)+((-1708:ℝ)*(n2911 b - n61 b * n2901 b)+0))))*(27089991/11115295525:ℝ)+0))))
  simp only [n64,n2912,n2913,n2914,n2915,n2916,n2917,n2918,n2919,n2920,n2921,n2922,n2923,n2924,n2925,n2926,n2927,n2928,n2929,n2930,n2931,n2932,n2933,n2934,n2935,n2936,n2937,n2938,n2939,n2940,n2941,n2942,n2943,n2944,n2945,n2946,n2947,n2948,n2949,n2950,n2951,n2952,n2953,n2954,n2955,n2956,n2957,n2958,n2959,n2960,n2961,n2962,n2963,n2964,n2965,n2966,n2967,n2968,n2969,n2970,n2971,n2972,n2973,n2974,n2975,n2976,n2977,n2978,n2979,n2980,n2981,n2982,n2983,n2984,n2985,n2986,n2987,n2988,n2989,n2990,n2991,n3088,n3089,n3090,n3091,n3092,n3093,n3094,n3095,n3096,n3097,n3098]
  generalize n61 b = v61
  generalize n136 b = v136
  generalize n150 b = v150
  generalize n2887 b = v2887
  generalize n2888 b = v2888
  generalize n2890 b = v2890
  generalize n2891 b = v2891
  generalize n2892 b = v2892
  generalize n2893 b = v2893
  generalize n2895 b = v2895
  generalize n2896 b = v2896
  generalize n2897 b = v2897
  generalize n2898 b = v2898
  generalize n2900 b = v2900
  generalize n2901 b = v2901
  generalize n2902 b = v2902
  generalize n2903 b = v2903
  generalize n2905 b = v2905
  generalize n2906 b = v2906
  generalize n2907 b = v2907
  generalize n2908 b = v2908
  generalize n2910 b = v2910
  generalize n2911 b = v2911
  norm_num <;> ring

private theorem conjugated_0_1 (b : ℝ) :
    traceConjugatedTransverse b 0 1 =
      (transverseConjugator * traceTransverse b * transverseConjugatorInv) 0 1 := by
  rw [mul4_entry_nested]
  simp only [mul4_entry_nested]
  change n3109 b = (((464:ℝ)*(n2887 b - n136 b * n2897 b)+((1077:ℝ)*(n2892 b - n150 b * n2897 b)+((4501:ℝ)*(n2902 b - n64 b * n2897 b)+((-1708:ℝ)*(n2907 b - n61 b * n2897 b)+0))))*(-118215737/22230591050:ℝ)+(((464:ℝ)*(n2888 b - n136 b * n2898 b)+((1077:ℝ)*(n2893 b - n150 b * n2898 b)+((4501:ℝ)*(n2903 b - n64 b * n2898 b)+((-1708:ℝ)*(n2908 b - n61 b * n2898 b)+0))))*(888696/11115295525:ℝ)+(((464:ℝ)*(n2890 b - n136 b * n2900 b)+((1077:ℝ)*(n2895 b - n150 b * n2900 b)+((4501:ℝ)*(n2905 b - n64 b * n2900 b)+((-1708:ℝ)*(n2910 b - n61 b * n2900 b)+0))))*(8549264/11115295525:ℝ)+(((464:ℝ)*(n2891 b - n136 b * n2901 b)+((1077:ℝ)*(n2896 b - n150 b * n2901 b)+((4501:ℝ)*(n2906 b - n64 b * n2901 b)+((-1708:ℝ)*(n2911 b - n61 b * n2901 b)+0))))*(7032384/11115295525:ℝ)+0))))
  simp only [n64,n2912,n2913,n2914,n2915,n2916,n2917,n2918,n2919,n2920,n2921,n2922,n2923,n2924,n2925,n2926,n2927,n2928,n2929,n2930,n2931,n2932,n2933,n2934,n2935,n2936,n2937,n2938,n2939,n2940,n2941,n2942,n2943,n2944,n2945,n2946,n2947,n2948,n2949,n2950,n2951,n2952,n2953,n2954,n2955,n2956,n2957,n2958,n2959,n2960,n2961,n2962,n2963,n2964,n2965,n2966,n2967,n2968,n2969,n2970,n2971,n2972,n2973,n2974,n2975,n2976,n2977,n2978,n2979,n2980,n2981,n2982,n2983,n2984,n2985,n2986,n2987,n2988,n2989,n2990,n2991,n3099,n3100,n3101,n3102,n3103,n3104,n3105,n3106,n3107,n3108,n3109]
  generalize n61 b = v61
  generalize n136 b = v136
  generalize n150 b = v150
  generalize n2887 b = v2887
  generalize n2888 b = v2888
  generalize n2890 b = v2890
  generalize n2891 b = v2891
  generalize n2892 b = v2892
  generalize n2893 b = v2893
  generalize n2895 b = v2895
  generalize n2896 b = v2896
  generalize n2897 b = v2897
  generalize n2898 b = v2898
  generalize n2900 b = v2900
  generalize n2901 b = v2901
  generalize n2902 b = v2902
  generalize n2903 b = v2903
  generalize n2905 b = v2905
  generalize n2906 b = v2906
  generalize n2907 b = v2907
  generalize n2908 b = v2908
  generalize n2910 b = v2910
  generalize n2911 b = v2911
  norm_num <;> ring

private theorem conjugated_0_2 (b : ℝ) :
    traceConjugatedTransverse b 0 2 =
      (transverseConjugator * traceTransverse b * transverseConjugatorInv) 0 2 := by
  rw [mul4_entry_nested]
  simp only [mul4_entry_nested]
  change n3120 b = (((464:ℝ)*(n2887 b - n136 b * n2897 b)+((1077:ℝ)*(n2892 b - n150 b * n2897 b)+((4501:ℝ)*(n2902 b - n64 b * n2897 b)+((-1708:ℝ)*(n2907 b - n61 b * n2897 b)+0))))*(23413073/4446118210:ℝ)+(((464:ℝ)*(n2888 b - n136 b * n2898 b)+((1077:ℝ)*(n2893 b - n150 b * n2898 b)+((4501:ℝ)*(n2903 b - n64 b * n2898 b)+((-1708:ℝ)*(n2908 b - n61 b * n2898 b)+0))))*(-118410819/2223059105:ℝ)+(((464:ℝ)*(n2890 b - n136 b * n2900 b)+((1077:ℝ)*(n2895 b - n150 b * n2900 b)+((4501:ℝ)*(n2905 b - n64 b * n2900 b)+((-1708:ℝ)*(n2910 b - n61 b * n2900 b)+0))))*(30921059/2223059105:ℝ)+(((464:ℝ)*(n2891 b - n136 b * n2901 b)+((1077:ℝ)*(n2896 b - n150 b * n2901 b)+((4501:ℝ)*(n2906 b - n64 b * n2901 b)+((-1708:ℝ)*(n2911 b - n61 b * n2901 b)+0))))*(9999454/2223059105:ℝ)+0))))
  simp only [n64,n2912,n2913,n2914,n2915,n2916,n2917,n2918,n2919,n2920,n2921,n2922,n2923,n2924,n2925,n2926,n2927,n2928,n2929,n2930,n2931,n2932,n2933,n2934,n2935,n2936,n2937,n2938,n2939,n2940,n2941,n2942,n2943,n2944,n2945,n2946,n2947,n2948,n2949,n2950,n2951,n2952,n2953,n2954,n2955,n2956,n2957,n2958,n2959,n2960,n2961,n2962,n2963,n2964,n2965,n2966,n2967,n2968,n2969,n2970,n2971,n2972,n2973,n2974,n2975,n2976,n2977,n2978,n2979,n2980,n2981,n2982,n2983,n2984,n2985,n2986,n2987,n2988,n2989,n2990,n2991,n3110,n3111,n3112,n3113,n3114,n3115,n3116,n3117,n3118,n3119,n3120]
  generalize n61 b = v61
  generalize n136 b = v136
  generalize n150 b = v150
  generalize n2887 b = v2887
  generalize n2888 b = v2888
  generalize n2890 b = v2890
  generalize n2891 b = v2891
  generalize n2892 b = v2892
  generalize n2893 b = v2893
  generalize n2895 b = v2895
  generalize n2896 b = v2896
  generalize n2897 b = v2897
  generalize n2898 b = v2898
  generalize n2900 b = v2900
  generalize n2901 b = v2901
  generalize n2902 b = v2902
  generalize n2903 b = v2903
  generalize n2905 b = v2905
  generalize n2906 b = v2906
  generalize n2907 b = v2907
  generalize n2908 b = v2908
  generalize n2910 b = v2910
  generalize n2911 b = v2911
  norm_num <;> ring

private theorem conjugated_0_3 (b : ℝ) :
    traceConjugatedTransverse b 0 3 =
      (transverseConjugator * traceTransverse b * transverseConjugatorInv) 0 3 := by
  rw [mul4_entry_nested]
  simp only [mul4_entry_nested]
  change n3131 b = (((464:ℝ)*(n2887 b - n136 b * n2897 b)+((1077:ℝ)*(n2892 b - n150 b * n2897 b)+((4501:ℝ)*(n2902 b - n64 b * n2897 b)+((-1708:ℝ)*(n2907 b - n61 b * n2897 b)+0))))*(-183928858/11115295525:ℝ)+(((464:ℝ)*(n2888 b - n136 b * n2898 b)+((1077:ℝ)*(n2893 b - n150 b * n2898 b)+((4501:ℝ)*(n2903 b - n64 b * n2898 b)+((-1708:ℝ)*(n2908 b - n61 b * n2898 b)+0))))*(2783828/11115295525:ℝ)+(((464:ℝ)*(n2890 b - n136 b * n2900 b)+((1077:ℝ)*(n2895 b - n150 b * n2900 b)+((4501:ℝ)*(n2905 b - n64 b * n2900 b)+((-1708:ℝ)*(n2910 b - n61 b * n2900 b)+0))))*(23578552/11115295525:ℝ)+(((464:ℝ)*(n2891 b - n136 b * n2901 b)+((1077:ℝ)*(n2896 b - n150 b * n2901 b)+((4501:ℝ)*(n2906 b - n64 b * n2901 b)+((-1708:ℝ)*(n2911 b - n61 b * n2901 b)+0))))*(13924037/11115295525:ℝ)+0))))
  simp only [n64,n2912,n2913,n2914,n2915,n2916,n2917,n2918,n2919,n2920,n2921,n2922,n2923,n2924,n2925,n2926,n2927,n2928,n2929,n2930,n2931,n2932,n2933,n2934,n2935,n2936,n2937,n2938,n2939,n2940,n2941,n2942,n2943,n2944,n2945,n2946,n2947,n2948,n2949,n2950,n2951,n2952,n2953,n2954,n2955,n2956,n2957,n2958,n2959,n2960,n2961,n2962,n2963,n2964,n2965,n2966,n2967,n2968,n2969,n2970,n2971,n2972,n2973,n2974,n2975,n2976,n2977,n2978,n2979,n2980,n2981,n2982,n2983,n2984,n2985,n2986,n2987,n2988,n2989,n2990,n2991,n3121,n3122,n3123,n3124,n3125,n3126,n3127,n3128,n3129,n3130,n3131]
  generalize n61 b = v61
  generalize n136 b = v136
  generalize n150 b = v150
  generalize n2887 b = v2887
  generalize n2888 b = v2888
  generalize n2890 b = v2890
  generalize n2891 b = v2891
  generalize n2892 b = v2892
  generalize n2893 b = v2893
  generalize n2895 b = v2895
  generalize n2896 b = v2896
  generalize n2897 b = v2897
  generalize n2898 b = v2898
  generalize n2900 b = v2900
  generalize n2901 b = v2901
  generalize n2902 b = v2902
  generalize n2903 b = v2903
  generalize n2905 b = v2905
  generalize n2906 b = v2906
  generalize n2907 b = v2907
  generalize n2908 b = v2908
  generalize n2910 b = v2910
  generalize n2911 b = v2911
  norm_num <;> ring

private theorem conjugated_1_0 (b : ℝ) :
    traceConjugatedTransverse b 1 0 =
      (transverseConjugator * traceTransverse b * transverseConjugatorInv) 1 0 := by
  rw [mul4_entry_nested]
  simp only [mul4_entry_nested]
  change n3138 b = (((1366:ℝ)*(n2887 b - n136 b * n2897 b)+((2793:ℝ)*(n2892 b - n150 b * n2897 b)+((10000:ℝ)*(n2902 b - n64 b * n2897 b)+((552:ℝ)*(n2907 b - n61 b * n2897 b)+0))))*(521647187/22230591050:ℝ)+(((1366:ℝ)*(n2888 b - n136 b * n2898 b)+((2793:ℝ)*(n2893 b - n150 b * n2898 b)+((10000:ℝ)*(n2903 b - n64 b * n2898 b)+((552:ℝ)*(n2908 b - n61 b * n2898 b)+0))))*(-574350721/11115295525:ℝ)+(((1366:ℝ)*(n2890 b - n136 b * n2900 b)+((2793:ℝ)*(n2895 b - n150 b * n2900 b)+((10000:ℝ)*(n2905 b - n64 b * n2900 b)+((552:ℝ)*(n2910 b - n61 b * n2900 b)+0))))*(123292286/11115295525:ℝ)+(((1366:ℝ)*(n2891 b - n136 b * n2901 b)+((2793:ℝ)*(n2896 b - n150 b * n2901 b)+((10000:ℝ)*(n2906 b - n64 b * n2901 b)+((552:ℝ)*(n2911 b - n61 b * n2901 b)+0))))*(27089991/11115295525:ℝ)+0))))
  simp only [n64,n2912,n2913,n2914,n2915,n2916,n2917,n2918,n2919,n2920,n2921,n2922,n2923,n2924,n2925,n2926,n2927,n2928,n2929,n2930,n2931,n2932,n2933,n2934,n2935,n2936,n2937,n2938,n2939,n2940,n2941,n2942,n2943,n2944,n2945,n2946,n2947,n2948,n2949,n2950,n2951,n2952,n2953,n2954,n2955,n2956,n2957,n2958,n2959,n2992,n2993,n2994,n2995,n2996,n2997,n2998,n2999,n3000,n3001,n3002,n3003,n3004,n3005,n3006,n3007,n3008,n3009,n3010,n3011,n3012,n3013,n3014,n3015,n3016,n3017,n3018,n3019,n3020,n3021,n3022,n3023,n3088,n3090,n3093,n3096,n3132,n3133,n3134,n3135,n3136,n3137,n3138]
  generalize n61 b = v61
  generalize n136 b = v136
  generalize n150 b = v150
  generalize n2887 b = v2887
  generalize n2888 b = v2888
  generalize n2890 b = v2890
  generalize n2891 b = v2891
  generalize n2892 b = v2892
  generalize n2893 b = v2893
  generalize n2895 b = v2895
  generalize n2896 b = v2896
  generalize n2897 b = v2897
  generalize n2898 b = v2898
  generalize n2900 b = v2900
  generalize n2901 b = v2901
  generalize n2902 b = v2902
  generalize n2903 b = v2903
  generalize n2905 b = v2905
  generalize n2906 b = v2906
  generalize n2907 b = v2907
  generalize n2908 b = v2908
  generalize n2910 b = v2910
  generalize n2911 b = v2911
  norm_num <;> ring

private theorem conjugated_1_1 (b : ℝ) :
    traceConjugatedTransverse b 1 1 =
      (transverseConjugator * traceTransverse b * transverseConjugatorInv) 1 1 := by
  rw [mul4_entry_nested]
  simp only [mul4_entry_nested]
  change n3145 b = (((1366:ℝ)*(n2887 b - n136 b * n2897 b)+((2793:ℝ)*(n2892 b - n150 b * n2897 b)+((10000:ℝ)*(n2902 b - n64 b * n2897 b)+((552:ℝ)*(n2907 b - n61 b * n2897 b)+0))))*(-118215737/22230591050:ℝ)+(((1366:ℝ)*(n2888 b - n136 b * n2898 b)+((2793:ℝ)*(n2893 b - n150 b * n2898 b)+((10000:ℝ)*(n2903 b - n64 b * n2898 b)+((552:ℝ)*(n2908 b - n61 b * n2898 b)+0))))*(888696/11115295525:ℝ)+(((1366:ℝ)*(n2890 b - n136 b * n2900 b)+((2793:ℝ)*(n2895 b - n150 b * n2900 b)+((10000:ℝ)*(n2905 b - n64 b * n2900 b)+((552:ℝ)*(n2910 b - n61 b * n2900 b)+0))))*(8549264/11115295525:ℝ)+(((1366:ℝ)*(n2891 b - n136 b * n2901 b)+((2793:ℝ)*(n2896 b - n150 b * n2901 b)+((10000:ℝ)*(n2906 b - n64 b * n2901 b)+((552:ℝ)*(n2911 b - n61 b * n2901 b)+0))))*(7032384/11115295525:ℝ)+0))))
  simp only [n64,n2912,n2913,n2914,n2915,n2916,n2917,n2918,n2919,n2920,n2921,n2922,n2923,n2924,n2925,n2926,n2927,n2928,n2929,n2930,n2931,n2932,n2933,n2934,n2935,n2936,n2937,n2938,n2939,n2940,n2941,n2942,n2943,n2944,n2945,n2946,n2947,n2948,n2949,n2950,n2951,n2952,n2953,n2954,n2955,n2956,n2957,n2958,n2959,n2992,n2993,n2994,n2995,n2996,n2997,n2998,n2999,n3000,n3001,n3002,n3003,n3004,n3005,n3006,n3007,n3008,n3009,n3010,n3011,n3012,n3013,n3014,n3015,n3016,n3017,n3018,n3019,n3020,n3021,n3022,n3023,n3099,n3101,n3104,n3107,n3139,n3140,n3141,n3142,n3143,n3144,n3145]
  generalize n61 b = v61
  generalize n136 b = v136
  generalize n150 b = v150
  generalize n2887 b = v2887
  generalize n2888 b = v2888
  generalize n2890 b = v2890
  generalize n2891 b = v2891
  generalize n2892 b = v2892
  generalize n2893 b = v2893
  generalize n2895 b = v2895
  generalize n2896 b = v2896
  generalize n2897 b = v2897
  generalize n2898 b = v2898
  generalize n2900 b = v2900
  generalize n2901 b = v2901
  generalize n2902 b = v2902
  generalize n2903 b = v2903
  generalize n2905 b = v2905
  generalize n2906 b = v2906
  generalize n2907 b = v2907
  generalize n2908 b = v2908
  generalize n2910 b = v2910
  generalize n2911 b = v2911
  norm_num <;> ring

private theorem conjugated_1_2 (b : ℝ) :
    traceConjugatedTransverse b 1 2 =
      (transverseConjugator * traceTransverse b * transverseConjugatorInv) 1 2 := by
  rw [mul4_entry_nested]
  simp only [mul4_entry_nested]
  change n3152 b = (((1366:ℝ)*(n2887 b - n136 b * n2897 b)+((2793:ℝ)*(n2892 b - n150 b * n2897 b)+((10000:ℝ)*(n2902 b - n64 b * n2897 b)+((552:ℝ)*(n2907 b - n61 b * n2897 b)+0))))*(23413073/4446118210:ℝ)+(((1366:ℝ)*(n2888 b - n136 b * n2898 b)+((2793:ℝ)*(n2893 b - n150 b * n2898 b)+((10000:ℝ)*(n2903 b - n64 b * n2898 b)+((552:ℝ)*(n2908 b - n61 b * n2898 b)+0))))*(-118410819/2223059105:ℝ)+(((1366:ℝ)*(n2890 b - n136 b * n2900 b)+((2793:ℝ)*(n2895 b - n150 b * n2900 b)+((10000:ℝ)*(n2905 b - n64 b * n2900 b)+((552:ℝ)*(n2910 b - n61 b * n2900 b)+0))))*(30921059/2223059105:ℝ)+(((1366:ℝ)*(n2891 b - n136 b * n2901 b)+((2793:ℝ)*(n2896 b - n150 b * n2901 b)+((10000:ℝ)*(n2906 b - n64 b * n2901 b)+((552:ℝ)*(n2911 b - n61 b * n2901 b)+0))))*(9999454/2223059105:ℝ)+0))))
  simp only [n64,n2912,n2913,n2914,n2915,n2916,n2917,n2918,n2919,n2920,n2921,n2922,n2923,n2924,n2925,n2926,n2927,n2928,n2929,n2930,n2931,n2932,n2933,n2934,n2935,n2936,n2937,n2938,n2939,n2940,n2941,n2942,n2943,n2944,n2945,n2946,n2947,n2948,n2949,n2950,n2951,n2952,n2953,n2954,n2955,n2956,n2957,n2958,n2959,n2992,n2993,n2994,n2995,n2996,n2997,n2998,n2999,n3000,n3001,n3002,n3003,n3004,n3005,n3006,n3007,n3008,n3009,n3010,n3011,n3012,n3013,n3014,n3015,n3016,n3017,n3018,n3019,n3020,n3021,n3022,n3023,n3110,n3112,n3115,n3118,n3146,n3147,n3148,n3149,n3150,n3151,n3152]
  generalize n61 b = v61
  generalize n136 b = v136
  generalize n150 b = v150
  generalize n2887 b = v2887
  generalize n2888 b = v2888
  generalize n2890 b = v2890
  generalize n2891 b = v2891
  generalize n2892 b = v2892
  generalize n2893 b = v2893
  generalize n2895 b = v2895
  generalize n2896 b = v2896
  generalize n2897 b = v2897
  generalize n2898 b = v2898
  generalize n2900 b = v2900
  generalize n2901 b = v2901
  generalize n2902 b = v2902
  generalize n2903 b = v2903
  generalize n2905 b = v2905
  generalize n2906 b = v2906
  generalize n2907 b = v2907
  generalize n2908 b = v2908
  generalize n2910 b = v2910
  generalize n2911 b = v2911
  norm_num <;> ring

private theorem conjugated_1_3 (b : ℝ) :
    traceConjugatedTransverse b 1 3 =
      (transverseConjugator * traceTransverse b * transverseConjugatorInv) 1 3 := by
  rw [mul4_entry_nested]
  simp only [mul4_entry_nested]
  change n3159 b = (((1366:ℝ)*(n2887 b - n136 b * n2897 b)+((2793:ℝ)*(n2892 b - n150 b * n2897 b)+((10000:ℝ)*(n2902 b - n64 b * n2897 b)+((552:ℝ)*(n2907 b - n61 b * n2897 b)+0))))*(-183928858/11115295525:ℝ)+(((1366:ℝ)*(n2888 b - n136 b * n2898 b)+((2793:ℝ)*(n2893 b - n150 b * n2898 b)+((10000:ℝ)*(n2903 b - n64 b * n2898 b)+((552:ℝ)*(n2908 b - n61 b * n2898 b)+0))))*(2783828/11115295525:ℝ)+(((1366:ℝ)*(n2890 b - n136 b * n2900 b)+((2793:ℝ)*(n2895 b - n150 b * n2900 b)+((10000:ℝ)*(n2905 b - n64 b * n2900 b)+((552:ℝ)*(n2910 b - n61 b * n2900 b)+0))))*(23578552/11115295525:ℝ)+(((1366:ℝ)*(n2891 b - n136 b * n2901 b)+((2793:ℝ)*(n2896 b - n150 b * n2901 b)+((10000:ℝ)*(n2906 b - n64 b * n2901 b)+((552:ℝ)*(n2911 b - n61 b * n2901 b)+0))))*(13924037/11115295525:ℝ)+0))))
  simp only [n64,n2912,n2913,n2914,n2915,n2916,n2917,n2918,n2919,n2920,n2921,n2922,n2923,n2924,n2925,n2926,n2927,n2928,n2929,n2930,n2931,n2932,n2933,n2934,n2935,n2936,n2937,n2938,n2939,n2940,n2941,n2942,n2943,n2944,n2945,n2946,n2947,n2948,n2949,n2950,n2951,n2952,n2953,n2954,n2955,n2956,n2957,n2958,n2959,n2992,n2993,n2994,n2995,n2996,n2997,n2998,n2999,n3000,n3001,n3002,n3003,n3004,n3005,n3006,n3007,n3008,n3009,n3010,n3011,n3012,n3013,n3014,n3015,n3016,n3017,n3018,n3019,n3020,n3021,n3022,n3023,n3121,n3123,n3126,n3129,n3153,n3154,n3155,n3156,n3157,n3158,n3159]
  generalize n61 b = v61
  generalize n136 b = v136
  generalize n150 b = v150
  generalize n2887 b = v2887
  generalize n2888 b = v2888
  generalize n2890 b = v2890
  generalize n2891 b = v2891
  generalize n2892 b = v2892
  generalize n2893 b = v2893
  generalize n2895 b = v2895
  generalize n2896 b = v2896
  generalize n2897 b = v2897
  generalize n2898 b = v2898
  generalize n2900 b = v2900
  generalize n2901 b = v2901
  generalize n2902 b = v2902
  generalize n2903 b = v2903
  generalize n2905 b = v2905
  generalize n2906 b = v2906
  generalize n2907 b = v2907
  generalize n2908 b = v2908
  generalize n2910 b = v2910
  generalize n2911 b = v2911
  norm_num <;> ring

private theorem conjugated_2_0 (b : ℝ) :
    traceConjugatedTransverse b 2 0 =
      (transverseConjugator * traceTransverse b * transverseConjugatorInv) 2 0 := by
  rw [mul4_entry_nested]
  simp only [mul4_entry_nested]
  change n3166 b = (((-448:ℝ)*(n2887 b - n136 b * n2897 b)+((-1058:ℝ)*(n2892 b - n150 b * n2897 b)+((-4343:ℝ)*(n2902 b - n64 b * n2897 b)+((1648:ℝ)*(n2907 b - n61 b * n2897 b)+0))))*(521647187/22230591050:ℝ)+(((-448:ℝ)*(n2888 b - n136 b * n2898 b)+((-1058:ℝ)*(n2893 b - n150 b * n2898 b)+((-4343:ℝ)*(n2903 b - n64 b * n2898 b)+((1648:ℝ)*(n2908 b - n61 b * n2898 b)+0))))*(-574350721/11115295525:ℝ)+(((-448:ℝ)*(n2890 b - n136 b * n2900 b)+((-1058:ℝ)*(n2895 b - n150 b * n2900 b)+((-4343:ℝ)*(n2905 b - n64 b * n2900 b)+((1648:ℝ)*(n2910 b - n61 b * n2900 b)+0))))*(123292286/11115295525:ℝ)+(((-448:ℝ)*(n2891 b - n136 b * n2901 b)+((-1058:ℝ)*(n2896 b - n150 b * n2901 b)+((-4343:ℝ)*(n2906 b - n64 b * n2901 b)+((1648:ℝ)*(n2911 b - n61 b * n2901 b)+0))))*(27089991/11115295525:ℝ)+0))))
  simp only [n64,n2912,n2913,n2914,n2915,n2916,n2917,n2918,n2919,n2920,n2921,n2922,n2923,n2924,n2925,n2926,n2927,n2928,n2929,n2930,n2931,n2932,n2933,n2934,n2935,n2936,n2937,n2938,n2939,n2940,n2941,n2942,n2943,n2944,n2945,n2946,n2947,n2948,n2949,n2950,n2951,n2952,n2953,n2954,n2955,n2956,n2957,n2958,n2959,n3024,n3025,n3026,n3027,n3028,n3029,n3030,n3031,n3032,n3033,n3034,n3035,n3036,n3037,n3038,n3039,n3040,n3041,n3042,n3043,n3044,n3045,n3046,n3047,n3048,n3049,n3050,n3051,n3052,n3053,n3054,n3055,n3088,n3090,n3093,n3096,n3160,n3161,n3162,n3163,n3164,n3165,n3166]
  generalize n61 b = v61
  generalize n136 b = v136
  generalize n150 b = v150
  generalize n2887 b = v2887
  generalize n2888 b = v2888
  generalize n2890 b = v2890
  generalize n2891 b = v2891
  generalize n2892 b = v2892
  generalize n2893 b = v2893
  generalize n2895 b = v2895
  generalize n2896 b = v2896
  generalize n2897 b = v2897
  generalize n2898 b = v2898
  generalize n2900 b = v2900
  generalize n2901 b = v2901
  generalize n2902 b = v2902
  generalize n2903 b = v2903
  generalize n2905 b = v2905
  generalize n2906 b = v2906
  generalize n2907 b = v2907
  generalize n2908 b = v2908
  generalize n2910 b = v2910
  generalize n2911 b = v2911
  norm_num <;> ring

private theorem conjugated_2_1 (b : ℝ) :
    traceConjugatedTransverse b 2 1 =
      (transverseConjugator * traceTransverse b * transverseConjugatorInv) 2 1 := by
  rw [mul4_entry_nested]
  simp only [mul4_entry_nested]
  change n3173 b = (((-448:ℝ)*(n2887 b - n136 b * n2897 b)+((-1058:ℝ)*(n2892 b - n150 b * n2897 b)+((-4343:ℝ)*(n2902 b - n64 b * n2897 b)+((1648:ℝ)*(n2907 b - n61 b * n2897 b)+0))))*(-118215737/22230591050:ℝ)+(((-448:ℝ)*(n2888 b - n136 b * n2898 b)+((-1058:ℝ)*(n2893 b - n150 b * n2898 b)+((-4343:ℝ)*(n2903 b - n64 b * n2898 b)+((1648:ℝ)*(n2908 b - n61 b * n2898 b)+0))))*(888696/11115295525:ℝ)+(((-448:ℝ)*(n2890 b - n136 b * n2900 b)+((-1058:ℝ)*(n2895 b - n150 b * n2900 b)+((-4343:ℝ)*(n2905 b - n64 b * n2900 b)+((1648:ℝ)*(n2910 b - n61 b * n2900 b)+0))))*(8549264/11115295525:ℝ)+(((-448:ℝ)*(n2891 b - n136 b * n2901 b)+((-1058:ℝ)*(n2896 b - n150 b * n2901 b)+((-4343:ℝ)*(n2906 b - n64 b * n2901 b)+((1648:ℝ)*(n2911 b - n61 b * n2901 b)+0))))*(7032384/11115295525:ℝ)+0))))
  simp only [n64,n2912,n2913,n2914,n2915,n2916,n2917,n2918,n2919,n2920,n2921,n2922,n2923,n2924,n2925,n2926,n2927,n2928,n2929,n2930,n2931,n2932,n2933,n2934,n2935,n2936,n2937,n2938,n2939,n2940,n2941,n2942,n2943,n2944,n2945,n2946,n2947,n2948,n2949,n2950,n2951,n2952,n2953,n2954,n2955,n2956,n2957,n2958,n2959,n3024,n3025,n3026,n3027,n3028,n3029,n3030,n3031,n3032,n3033,n3034,n3035,n3036,n3037,n3038,n3039,n3040,n3041,n3042,n3043,n3044,n3045,n3046,n3047,n3048,n3049,n3050,n3051,n3052,n3053,n3054,n3055,n3099,n3101,n3104,n3107,n3167,n3168,n3169,n3170,n3171,n3172,n3173]
  generalize n61 b = v61
  generalize n136 b = v136
  generalize n150 b = v150
  generalize n2887 b = v2887
  generalize n2888 b = v2888
  generalize n2890 b = v2890
  generalize n2891 b = v2891
  generalize n2892 b = v2892
  generalize n2893 b = v2893
  generalize n2895 b = v2895
  generalize n2896 b = v2896
  generalize n2897 b = v2897
  generalize n2898 b = v2898
  generalize n2900 b = v2900
  generalize n2901 b = v2901
  generalize n2902 b = v2902
  generalize n2903 b = v2903
  generalize n2905 b = v2905
  generalize n2906 b = v2906
  generalize n2907 b = v2907
  generalize n2908 b = v2908
  generalize n2910 b = v2910
  generalize n2911 b = v2911
  norm_num <;> ring

private theorem conjugated_2_2 (b : ℝ) :
    traceConjugatedTransverse b 2 2 =
      (transverseConjugator * traceTransverse b * transverseConjugatorInv) 2 2 := by
  rw [mul4_entry_nested]
  simp only [mul4_entry_nested]
  change n3180 b = (((-448:ℝ)*(n2887 b - n136 b * n2897 b)+((-1058:ℝ)*(n2892 b - n150 b * n2897 b)+((-4343:ℝ)*(n2902 b - n64 b * n2897 b)+((1648:ℝ)*(n2907 b - n61 b * n2897 b)+0))))*(23413073/4446118210:ℝ)+(((-448:ℝ)*(n2888 b - n136 b * n2898 b)+((-1058:ℝ)*(n2893 b - n150 b * n2898 b)+((-4343:ℝ)*(n2903 b - n64 b * n2898 b)+((1648:ℝ)*(n2908 b - n61 b * n2898 b)+0))))*(-118410819/2223059105:ℝ)+(((-448:ℝ)*(n2890 b - n136 b * n2900 b)+((-1058:ℝ)*(n2895 b - n150 b * n2900 b)+((-4343:ℝ)*(n2905 b - n64 b * n2900 b)+((1648:ℝ)*(n2910 b - n61 b * n2900 b)+0))))*(30921059/2223059105:ℝ)+(((-448:ℝ)*(n2891 b - n136 b * n2901 b)+((-1058:ℝ)*(n2896 b - n150 b * n2901 b)+((-4343:ℝ)*(n2906 b - n64 b * n2901 b)+((1648:ℝ)*(n2911 b - n61 b * n2901 b)+0))))*(9999454/2223059105:ℝ)+0))))
  simp only [n64,n2912,n2913,n2914,n2915,n2916,n2917,n2918,n2919,n2920,n2921,n2922,n2923,n2924,n2925,n2926,n2927,n2928,n2929,n2930,n2931,n2932,n2933,n2934,n2935,n2936,n2937,n2938,n2939,n2940,n2941,n2942,n2943,n2944,n2945,n2946,n2947,n2948,n2949,n2950,n2951,n2952,n2953,n2954,n2955,n2956,n2957,n2958,n2959,n3024,n3025,n3026,n3027,n3028,n3029,n3030,n3031,n3032,n3033,n3034,n3035,n3036,n3037,n3038,n3039,n3040,n3041,n3042,n3043,n3044,n3045,n3046,n3047,n3048,n3049,n3050,n3051,n3052,n3053,n3054,n3055,n3110,n3112,n3115,n3118,n3174,n3175,n3176,n3177,n3178,n3179,n3180]
  generalize n61 b = v61
  generalize n136 b = v136
  generalize n150 b = v150
  generalize n2887 b = v2887
  generalize n2888 b = v2888
  generalize n2890 b = v2890
  generalize n2891 b = v2891
  generalize n2892 b = v2892
  generalize n2893 b = v2893
  generalize n2895 b = v2895
  generalize n2896 b = v2896
  generalize n2897 b = v2897
  generalize n2898 b = v2898
  generalize n2900 b = v2900
  generalize n2901 b = v2901
  generalize n2902 b = v2902
  generalize n2903 b = v2903
  generalize n2905 b = v2905
  generalize n2906 b = v2906
  generalize n2907 b = v2907
  generalize n2908 b = v2908
  generalize n2910 b = v2910
  generalize n2911 b = v2911
  norm_num <;> ring

private theorem conjugated_2_3 (b : ℝ) :
    traceConjugatedTransverse b 2 3 =
      (transverseConjugator * traceTransverse b * transverseConjugatorInv) 2 3 := by
  rw [mul4_entry_nested]
  simp only [mul4_entry_nested]
  change n3187 b = (((-448:ℝ)*(n2887 b - n136 b * n2897 b)+((-1058:ℝ)*(n2892 b - n150 b * n2897 b)+((-4343:ℝ)*(n2902 b - n64 b * n2897 b)+((1648:ℝ)*(n2907 b - n61 b * n2897 b)+0))))*(-183928858/11115295525:ℝ)+(((-448:ℝ)*(n2888 b - n136 b * n2898 b)+((-1058:ℝ)*(n2893 b - n150 b * n2898 b)+((-4343:ℝ)*(n2903 b - n64 b * n2898 b)+((1648:ℝ)*(n2908 b - n61 b * n2898 b)+0))))*(2783828/11115295525:ℝ)+(((-448:ℝ)*(n2890 b - n136 b * n2900 b)+((-1058:ℝ)*(n2895 b - n150 b * n2900 b)+((-4343:ℝ)*(n2905 b - n64 b * n2900 b)+((1648:ℝ)*(n2910 b - n61 b * n2900 b)+0))))*(23578552/11115295525:ℝ)+(((-448:ℝ)*(n2891 b - n136 b * n2901 b)+((-1058:ℝ)*(n2896 b - n150 b * n2901 b)+((-4343:ℝ)*(n2906 b - n64 b * n2901 b)+((1648:ℝ)*(n2911 b - n61 b * n2901 b)+0))))*(13924037/11115295525:ℝ)+0))))
  simp only [n64,n2912,n2913,n2914,n2915,n2916,n2917,n2918,n2919,n2920,n2921,n2922,n2923,n2924,n2925,n2926,n2927,n2928,n2929,n2930,n2931,n2932,n2933,n2934,n2935,n2936,n2937,n2938,n2939,n2940,n2941,n2942,n2943,n2944,n2945,n2946,n2947,n2948,n2949,n2950,n2951,n2952,n2953,n2954,n2955,n2956,n2957,n2958,n2959,n3024,n3025,n3026,n3027,n3028,n3029,n3030,n3031,n3032,n3033,n3034,n3035,n3036,n3037,n3038,n3039,n3040,n3041,n3042,n3043,n3044,n3045,n3046,n3047,n3048,n3049,n3050,n3051,n3052,n3053,n3054,n3055,n3121,n3123,n3126,n3129,n3181,n3182,n3183,n3184,n3185,n3186,n3187]
  generalize n61 b = v61
  generalize n136 b = v136
  generalize n150 b = v150
  generalize n2887 b = v2887
  generalize n2888 b = v2888
  generalize n2890 b = v2890
  generalize n2891 b = v2891
  generalize n2892 b = v2892
  generalize n2893 b = v2893
  generalize n2895 b = v2895
  generalize n2896 b = v2896
  generalize n2897 b = v2897
  generalize n2898 b = v2898
  generalize n2900 b = v2900
  generalize n2901 b = v2901
  generalize n2902 b = v2902
  generalize n2903 b = v2903
  generalize n2905 b = v2905
  generalize n2906 b = v2906
  generalize n2907 b = v2907
  generalize n2908 b = v2908
  generalize n2910 b = v2910
  generalize n2911 b = v2911
  norm_num <;> ring

private theorem conjugated_3_0 (b : ℝ) :
    traceConjugatedTransverse b 3 0 =
      (transverseConjugator * traceTransverse b * transverseConjugatorInv) 3 0 := by
  rw [mul4_entry_nested]
  simp only [mul4_entry_nested]
  change n3194 b = (((16:ℝ)*(n2887 b - n136 b * n2897 b)+((293:ℝ)*(n2892 b - n150 b * n2897 b)+((1787:ℝ)*(n2902 b - n64 b * n2897 b)+((-2075:ℝ)*(n2907 b - n61 b * n2897 b)+0))))*(521647187/22230591050:ℝ)+(((16:ℝ)*(n2888 b - n136 b * n2898 b)+((293:ℝ)*(n2893 b - n150 b * n2898 b)+((1787:ℝ)*(n2903 b - n64 b * n2898 b)+((-2075:ℝ)*(n2908 b - n61 b * n2898 b)+0))))*(-574350721/11115295525:ℝ)+(((16:ℝ)*(n2890 b - n136 b * n2900 b)+((293:ℝ)*(n2895 b - n150 b * n2900 b)+((1787:ℝ)*(n2905 b - n64 b * n2900 b)+((-2075:ℝ)*(n2910 b - n61 b * n2900 b)+0))))*(123292286/11115295525:ℝ)+(((16:ℝ)*(n2891 b - n136 b * n2901 b)+((293:ℝ)*(n2896 b - n150 b * n2901 b)+((1787:ℝ)*(n2906 b - n64 b * n2901 b)+((-2075:ℝ)*(n2911 b - n61 b * n2901 b)+0))))*(27089991/11115295525:ℝ)+0))))
  simp only [n64,n2912,n2913,n2914,n2915,n2916,n2917,n2918,n2919,n2920,n2921,n2922,n2923,n2924,n2925,n2926,n2927,n2928,n2929,n2930,n2931,n2932,n2933,n2934,n2935,n2936,n2937,n2938,n2939,n2940,n2941,n2942,n2943,n2944,n2945,n2946,n2947,n2948,n2949,n2950,n2951,n2952,n2953,n2954,n2955,n2956,n2957,n2958,n2959,n3056,n3057,n3058,n3059,n3060,n3061,n3062,n3063,n3064,n3065,n3066,n3067,n3068,n3069,n3070,n3071,n3072,n3073,n3074,n3075,n3076,n3077,n3078,n3079,n3080,n3081,n3082,n3083,n3084,n3085,n3086,n3087,n3088,n3090,n3093,n3096,n3188,n3189,n3190,n3191,n3192,n3193,n3194]
  generalize n61 b = v61
  generalize n136 b = v136
  generalize n150 b = v150
  generalize n2887 b = v2887
  generalize n2888 b = v2888
  generalize n2890 b = v2890
  generalize n2891 b = v2891
  generalize n2892 b = v2892
  generalize n2893 b = v2893
  generalize n2895 b = v2895
  generalize n2896 b = v2896
  generalize n2897 b = v2897
  generalize n2898 b = v2898
  generalize n2900 b = v2900
  generalize n2901 b = v2901
  generalize n2902 b = v2902
  generalize n2903 b = v2903
  generalize n2905 b = v2905
  generalize n2906 b = v2906
  generalize n2907 b = v2907
  generalize n2908 b = v2908
  generalize n2910 b = v2910
  generalize n2911 b = v2911
  norm_num <;> ring

private theorem conjugated_3_1 (b : ℝ) :
    traceConjugatedTransverse b 3 1 =
      (transverseConjugator * traceTransverse b * transverseConjugatorInv) 3 1 := by
  rw [mul4_entry_nested]
  simp only [mul4_entry_nested]
  change n3201 b = (((16:ℝ)*(n2887 b - n136 b * n2897 b)+((293:ℝ)*(n2892 b - n150 b * n2897 b)+((1787:ℝ)*(n2902 b - n64 b * n2897 b)+((-2075:ℝ)*(n2907 b - n61 b * n2897 b)+0))))*(-118215737/22230591050:ℝ)+(((16:ℝ)*(n2888 b - n136 b * n2898 b)+((293:ℝ)*(n2893 b - n150 b * n2898 b)+((1787:ℝ)*(n2903 b - n64 b * n2898 b)+((-2075:ℝ)*(n2908 b - n61 b * n2898 b)+0))))*(888696/11115295525:ℝ)+(((16:ℝ)*(n2890 b - n136 b * n2900 b)+((293:ℝ)*(n2895 b - n150 b * n2900 b)+((1787:ℝ)*(n2905 b - n64 b * n2900 b)+((-2075:ℝ)*(n2910 b - n61 b * n2900 b)+0))))*(8549264/11115295525:ℝ)+(((16:ℝ)*(n2891 b - n136 b * n2901 b)+((293:ℝ)*(n2896 b - n150 b * n2901 b)+((1787:ℝ)*(n2906 b - n64 b * n2901 b)+((-2075:ℝ)*(n2911 b - n61 b * n2901 b)+0))))*(7032384/11115295525:ℝ)+0))))
  simp only [n64,n2912,n2913,n2914,n2915,n2916,n2917,n2918,n2919,n2920,n2921,n2922,n2923,n2924,n2925,n2926,n2927,n2928,n2929,n2930,n2931,n2932,n2933,n2934,n2935,n2936,n2937,n2938,n2939,n2940,n2941,n2942,n2943,n2944,n2945,n2946,n2947,n2948,n2949,n2950,n2951,n2952,n2953,n2954,n2955,n2956,n2957,n2958,n2959,n3056,n3057,n3058,n3059,n3060,n3061,n3062,n3063,n3064,n3065,n3066,n3067,n3068,n3069,n3070,n3071,n3072,n3073,n3074,n3075,n3076,n3077,n3078,n3079,n3080,n3081,n3082,n3083,n3084,n3085,n3086,n3087,n3099,n3101,n3104,n3107,n3195,n3196,n3197,n3198,n3199,n3200,n3201]
  generalize n61 b = v61
  generalize n136 b = v136
  generalize n150 b = v150
  generalize n2887 b = v2887
  generalize n2888 b = v2888
  generalize n2890 b = v2890
  generalize n2891 b = v2891
  generalize n2892 b = v2892
  generalize n2893 b = v2893
  generalize n2895 b = v2895
  generalize n2896 b = v2896
  generalize n2897 b = v2897
  generalize n2898 b = v2898
  generalize n2900 b = v2900
  generalize n2901 b = v2901
  generalize n2902 b = v2902
  generalize n2903 b = v2903
  generalize n2905 b = v2905
  generalize n2906 b = v2906
  generalize n2907 b = v2907
  generalize n2908 b = v2908
  generalize n2910 b = v2910
  generalize n2911 b = v2911
  norm_num <;> ring

private theorem conjugated_3_2 (b : ℝ) :
    traceConjugatedTransverse b 3 2 =
      (transverseConjugator * traceTransverse b * transverseConjugatorInv) 3 2 := by
  rw [mul4_entry_nested]
  simp only [mul4_entry_nested]
  change n3208 b = (((16:ℝ)*(n2887 b - n136 b * n2897 b)+((293:ℝ)*(n2892 b - n150 b * n2897 b)+((1787:ℝ)*(n2902 b - n64 b * n2897 b)+((-2075:ℝ)*(n2907 b - n61 b * n2897 b)+0))))*(23413073/4446118210:ℝ)+(((16:ℝ)*(n2888 b - n136 b * n2898 b)+((293:ℝ)*(n2893 b - n150 b * n2898 b)+((1787:ℝ)*(n2903 b - n64 b * n2898 b)+((-2075:ℝ)*(n2908 b - n61 b * n2898 b)+0))))*(-118410819/2223059105:ℝ)+(((16:ℝ)*(n2890 b - n136 b * n2900 b)+((293:ℝ)*(n2895 b - n150 b * n2900 b)+((1787:ℝ)*(n2905 b - n64 b * n2900 b)+((-2075:ℝ)*(n2910 b - n61 b * n2900 b)+0))))*(30921059/2223059105:ℝ)+(((16:ℝ)*(n2891 b - n136 b * n2901 b)+((293:ℝ)*(n2896 b - n150 b * n2901 b)+((1787:ℝ)*(n2906 b - n64 b * n2901 b)+((-2075:ℝ)*(n2911 b - n61 b * n2901 b)+0))))*(9999454/2223059105:ℝ)+0))))
  simp only [n64,n2912,n2913,n2914,n2915,n2916,n2917,n2918,n2919,n2920,n2921,n2922,n2923,n2924,n2925,n2926,n2927,n2928,n2929,n2930,n2931,n2932,n2933,n2934,n2935,n2936,n2937,n2938,n2939,n2940,n2941,n2942,n2943,n2944,n2945,n2946,n2947,n2948,n2949,n2950,n2951,n2952,n2953,n2954,n2955,n2956,n2957,n2958,n2959,n3056,n3057,n3058,n3059,n3060,n3061,n3062,n3063,n3064,n3065,n3066,n3067,n3068,n3069,n3070,n3071,n3072,n3073,n3074,n3075,n3076,n3077,n3078,n3079,n3080,n3081,n3082,n3083,n3084,n3085,n3086,n3087,n3110,n3112,n3115,n3118,n3202,n3203,n3204,n3205,n3206,n3207,n3208]
  generalize n61 b = v61
  generalize n136 b = v136
  generalize n150 b = v150
  generalize n2887 b = v2887
  generalize n2888 b = v2888
  generalize n2890 b = v2890
  generalize n2891 b = v2891
  generalize n2892 b = v2892
  generalize n2893 b = v2893
  generalize n2895 b = v2895
  generalize n2896 b = v2896
  generalize n2897 b = v2897
  generalize n2898 b = v2898
  generalize n2900 b = v2900
  generalize n2901 b = v2901
  generalize n2902 b = v2902
  generalize n2903 b = v2903
  generalize n2905 b = v2905
  generalize n2906 b = v2906
  generalize n2907 b = v2907
  generalize n2908 b = v2908
  generalize n2910 b = v2910
  generalize n2911 b = v2911
  norm_num <;> ring

private theorem conjugated_3_3 (b : ℝ) :
    traceConjugatedTransverse b 3 3 =
      (transverseConjugator * traceTransverse b * transverseConjugatorInv) 3 3 := by
  rw [mul4_entry_nested]
  simp only [mul4_entry_nested]
  change n3215 b = (((16:ℝ)*(n2887 b - n136 b * n2897 b)+((293:ℝ)*(n2892 b - n150 b * n2897 b)+((1787:ℝ)*(n2902 b - n64 b * n2897 b)+((-2075:ℝ)*(n2907 b - n61 b * n2897 b)+0))))*(-183928858/11115295525:ℝ)+(((16:ℝ)*(n2888 b - n136 b * n2898 b)+((293:ℝ)*(n2893 b - n150 b * n2898 b)+((1787:ℝ)*(n2903 b - n64 b * n2898 b)+((-2075:ℝ)*(n2908 b - n61 b * n2898 b)+0))))*(2783828/11115295525:ℝ)+(((16:ℝ)*(n2890 b - n136 b * n2900 b)+((293:ℝ)*(n2895 b - n150 b * n2900 b)+((1787:ℝ)*(n2905 b - n64 b * n2900 b)+((-2075:ℝ)*(n2910 b - n61 b * n2900 b)+0))))*(23578552/11115295525:ℝ)+(((16:ℝ)*(n2891 b - n136 b * n2901 b)+((293:ℝ)*(n2896 b - n150 b * n2901 b)+((1787:ℝ)*(n2906 b - n64 b * n2901 b)+((-2075:ℝ)*(n2911 b - n61 b * n2901 b)+0))))*(13924037/11115295525:ℝ)+0))))
  simp only [n64,n2912,n2913,n2914,n2915,n2916,n2917,n2918,n2919,n2920,n2921,n2922,n2923,n2924,n2925,n2926,n2927,n2928,n2929,n2930,n2931,n2932,n2933,n2934,n2935,n2936,n2937,n2938,n2939,n2940,n2941,n2942,n2943,n2944,n2945,n2946,n2947,n2948,n2949,n2950,n2951,n2952,n2953,n2954,n2955,n2956,n2957,n2958,n2959,n3056,n3057,n3058,n3059,n3060,n3061,n3062,n3063,n3064,n3065,n3066,n3067,n3068,n3069,n3070,n3071,n3072,n3073,n3074,n3075,n3076,n3077,n3078,n3079,n3080,n3081,n3082,n3083,n3084,n3085,n3086,n3087,n3121,n3123,n3126,n3129,n3209,n3210,n3211,n3212,n3213,n3214,n3215]
  generalize n61 b = v61
  generalize n136 b = v136
  generalize n150 b = v150
  generalize n2887 b = v2887
  generalize n2888 b = v2888
  generalize n2890 b = v2890
  generalize n2891 b = v2891
  generalize n2892 b = v2892
  generalize n2893 b = v2893
  generalize n2895 b = v2895
  generalize n2896 b = v2896
  generalize n2897 b = v2897
  generalize n2898 b = v2898
  generalize n2900 b = v2900
  generalize n2901 b = v2901
  generalize n2902 b = v2902
  generalize n2903 b = v2903
  generalize n2905 b = v2905
  generalize n2906 b = v2906
  generalize n2907 b = v2907
  generalize n2908 b = v2908
  generalize n2910 b = v2910
  generalize n2911 b = v2911
  norm_num <;> ring

theorem traceConjugatedTransverse_eq (b : ℝ) :
    traceConjugatedTransverse b = transverseConjugator * traceTransverse b * transverseConjugatorInv := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact conjugated_0_0 b
  · exact conjugated_0_1 b
  · exact conjugated_0_2 b
  · exact conjugated_0_3 b
  · exact conjugated_1_0 b
  · exact conjugated_1_1 b
  · exact conjugated_1_2 b
  · exact conjugated_1_3 b
  · exact conjugated_2_0 b
  · exact conjugated_2_1 b
  · exact conjugated_2_2 b
  · exact conjugated_2_3 b
  · exact conjugated_3_0 b
  · exact conjugated_3_1 b
  · exact conjugated_3_2 b
  · exact conjugated_3_3 b

theorem traceBaseState_eq (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    traceBaseState b = pack (x0 b) (H0 b) := by
  ext i
  fin_cases i <;> simp [traceBaseState,pack,H0,trace_n136 b hb hp,trace_n150 b hb hp,trace_n15 b hb hp,trace_n64 b hb hp,trace_n61 b hb hp]

end
end BFGS.Counterexample
