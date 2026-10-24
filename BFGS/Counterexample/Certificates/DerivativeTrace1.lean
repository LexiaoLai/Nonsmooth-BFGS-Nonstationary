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

theorem jacobian1_column0 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    expandedStep (traceMetric b 1) (traceGradient b 1) (traceGradient b 2)
      (symmetricMap (traceHessian b 1)) (symmetricMap (traceHessian b 2))
      ![1,0,0,0,0] = ![n911 b,n910 b,n1044 b,n1045 b,n1047 b] := by
  have hs92 : n92 b = n91 b := by rw [trace_n92 b hb hp,trace_n91 b hb hp]
  have hs120 : n120 b = n119 b := by rw [trace_n120 b hb hp,trace_n119 b hb hp]
  have hs184 : n184 b = n183 b := by rw [trace_n184 b hb hp,trace_n183 b hb hp]
  have hs198 : n198 b = n197 b := by rw [trace_n198 b hb hp,trace_n197 b hb hp]
  have hs212 : n212 b = n211 b := by rw [trace_n212 b hb hp,trace_n211 b hb hp]
  have hs226 : n226 b = n225 b := by rw [trace_n226 b hb hp,trace_n225 b hb hp]
  have hs231 : n231 b = n230 b := by rw [trace_n231 b hb hp,trace_n230 b hb hp]
  ext i
  fin_cases i <;>
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail, expandedStep, expandedUpdate, traceMetric, traceGradient, traceHessian, addSym, outerSym, crossSym, pack, point, metric, Sym2.mulV, Sym2.scale, dot, symmetricMap_apply, div_eq_mul_inv, mul_inv_rev, n13, n15, n16, n64, n66, n122, n233, n302, n303, n320, n321, n322, n323, n903, n904, n905, n906, n907, n908, n909, n910, n911, n912, n913, n914, n915, n916, n917, n918, n919, n920, n921, n922, n923, n924, n925, n926, n927, n928, n929, n930, n931, n932, n933, n934, n935, n936, n937, n938, n939, n941, n942, n943, n945, n946, n947, n949, n950, n951, n953, n954, n955, n956, n957, n958, n959, n960, n961, n962, n963, n964, n965, n967, n968, n969, n971, n972, n973, n975, n976, n977, n979, n980, n981, n983, n984, n985, n987, n988, n989, n991, n992, n993, n995, n996, n997, n999, n1000, n1001, n1003, n1004, n1005, n1006, n1007, n1009, n1010, n1011, n1012, n1013, n1014, n1016, n1017, n1018, n1020, n1021, n1022, n1023, n1024, n1025, n1026, n1027, n1028, n1029, n1030, n1031, n1032, n1034, n1035, n1036, n1038, n1039, n1040, n1041, n1043, n1044, n1045, n1047, hs92, hs120, hs184, hs198, hs212, hs226, hs231] <;> ring <;> try simp only [true_or,or_true]

theorem jacobian1_column1 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    expandedStep (traceMetric b 1) (traceGradient b 1) (traceGradient b 2)
      (symmetricMap (traceHessian b 1)) (symmetricMap (traceHessian b 2))
      ![0,1,0,0,0] = ![n1054 b,n1056 b,n1155 b,n1156 b,n1158 b] := by
  have hs92 : n92 b = n91 b := by rw [trace_n92 b hb hp,trace_n91 b hb hp]
  have hs120 : n120 b = n119 b := by rw [trace_n120 b hb hp,trace_n119 b hb hp]
  have hs184 : n184 b = n183 b := by rw [trace_n184 b hb hp,trace_n183 b hb hp]
  have hs198 : n198 b = n197 b := by rw [trace_n198 b hb hp,trace_n197 b hb hp]
  have hs212 : n212 b = n211 b := by rw [trace_n212 b hb hp,trace_n211 b hb hp]
  have hs226 : n226 b = n225 b := by rw [trace_n226 b hb hp,trace_n225 b hb hp]
  have hs231 : n231 b = n230 b := by rw [trace_n231 b hb hp,trace_n230 b hb hp]
  ext i
  fin_cases i <;>
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail, expandedStep, expandedUpdate, traceMetric, traceGradient, traceHessian, addSym, outerSym, crossSym, pack, point, metric, Sym2.mulV, Sym2.scale, dot, symmetricMap_apply, div_eq_mul_inv, mul_inv_rev, n13, n15, n16, n64, n66, n122, n233, n302, n303, n320, n321, n322, n323, n929, n930, n931, n932, n933, n934, n935, n936, n937, n938, n939, n941, n942, n943, n945, n946, n947, n949, n950, n951, n953, n1004, n1005, n1010, n1011, n1023, n1024, n1026, n1027, n1039, n1048, n1049, n1050, n1051, n1052, n1053, n1054, n1055, n1056, n1057, n1058, n1059, n1060, n1061, n1062, n1063, n1064, n1065, n1066, n1067, n1068, n1069, n1070, n1071, n1072, n1073, n1074, n1075, n1076, n1077, n1078, n1079, n1080, n1081, n1082, n1083, n1084, n1085, n1087, n1088, n1089, n1091, n1092, n1093, n1095, n1096, n1097, n1099, n1100, n1101, n1103, n1104, n1105, n1107, n1108, n1109, n1111, n1112, n1113, n1115, n1116, n1117, n1119, n1120, n1121, n1123, n1124, n1125, n1127, n1128, n1129, n1130, n1132, n1133, n1134, n1136, n1137, n1138, n1139, n1140, n1141, n1142, n1143, n1144, n1146, n1147, n1148, n1150, n1151, n1152, n1154, n1155, n1156, n1158, hs92, hs120, hs184, hs198, hs212, hs226, hs231] <;> ring <;> try simp only [true_or,or_true]

theorem jacobian1_column2 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    expandedStep (traceMetric b 1) (traceGradient b 1) (traceGradient b 2)
      (symmetricMap (traceHessian b 1)) (symmetricMap (traceHessian b 2))
      ![0,0,1,0,0] = ![n66 b,n66 b,n1172 b,n1173 b,n1171 b] := by
  have hs92 : n92 b = n91 b := by rw [trace_n92 b hb hp,trace_n91 b hb hp]
  have hs120 : n120 b = n119 b := by rw [trace_n120 b hb hp,trace_n119 b hb hp]
  have hs184 : n184 b = n183 b := by rw [trace_n184 b hb hp,trace_n183 b hb hp]
  have hs198 : n198 b = n197 b := by rw [trace_n198 b hb hp,trace_n197 b hb hp]
  have hs212 : n212 b = n211 b := by rw [trace_n212 b hb hp,trace_n211 b hb hp]
  have hs226 : n226 b = n225 b := by rw [trace_n226 b hb hp,trace_n225 b hb hp]
  have hs231 : n231 b = n230 b := by rw [trace_n231 b hb hp,trace_n230 b hb hp]
  ext i
  fin_cases i <;>
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail, expandedStep, expandedUpdate, traceMetric, traceGradient, traceHessian, addSym, outerSym, crossSym, pack, point, metric, Sym2.mulV, Sym2.scale, dot, symmetricMap_apply, div_eq_mul_inv, mul_inv_rev, n15, n16, n64, n66, n122, n233, n302, n303, n320, n321, n322, n323, n362, n950, n951, n953, n1004, n1005, n1010, n1011, n1159, n1160, n1162, n1163, n1164, n1166, n1167, n1168, n1169, n1171, n1172, n1173, hs92, hs120, hs184, hs198, hs212, hs226, hs231] <;> ring <;> try simp only [true_or,or_true]

theorem jacobian1_column3 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    expandedStep (traceMetric b 1) (traceGradient b 1) (traceGradient b 2)
      (symmetricMap (traceHessian b 1)) (symmetricMap (traceHessian b 2))
      ![0,0,0,1,0] = ![n16 b,n66 b,n1255 b,n1256 b,n1251 b] := by
  have hs92 : n92 b = n91 b := by rw [trace_n92 b hb hp,trace_n91 b hb hp]
  have hs120 : n120 b = n119 b := by rw [trace_n120 b hb hp,trace_n119 b hb hp]
  have hs184 : n184 b = n183 b := by rw [trace_n184 b hb hp,trace_n183 b hb hp]
  have hs198 : n198 b = n197 b := by rw [trace_n198 b hb hp,trace_n197 b hb hp]
  have hs212 : n212 b = n211 b := by rw [trace_n212 b hb hp,trace_n211 b hb hp]
  have hs226 : n226 b = n225 b := by rw [trace_n226 b hb hp,trace_n225 b hb hp]
  have hs231 : n231 b = n230 b := by rw [trace_n231 b hb hp,trace_n230 b hb hp]
  ext i
  fin_cases i <;>
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail, expandedStep, expandedUpdate, traceMetric, traceGradient, traceHessian, addSym, outerSym, crossSym, pack, point, metric, Sym2.mulV, Sym2.scale, dot, symmetricMap_apply, div_eq_mul_inv, mul_inv_rev, n13, n15, n16, n64, n66, n122, n233, n302, n303, n320, n321, n322, n323, n929, n930, n931, n932, n933, n934, n935, n936, n937, n938, n939, n941, n942, n943, n945, n946, n947, n949, n950, n951, n953, n1004, n1005, n1010, n1011, n1023, n1024, n1026, n1027, n1039, n1175, n1176, n1177, n1178, n1179, n1180, n1181, n1182, n1183, n1184, n1185, n1186, n1187, n1188, n1189, n1190, n1191, n1192, n1193, n1194, n1195, n1196, n1197, n1198, n1199, n1200, n1202, n1203, n1204, n1206, n1207, n1209, n1211, n1212, n1213, n1214, n1216, n1217, n1218, n1219, n1220, n1222, n1223, n1224, n1226, n1227, n1229, n1230, n1231, n1233, n1234, n1235, n1237, n1238, n1239, n1240, n1241, n1242, n1243, n1244, n1245, n1247, n1248, n1249, n1251, n1252, n1253, n1255, n1256, hs92, hs120, hs184, hs198, hs212, hs226, hs231] <;> ring <;> try simp only [true_or,or_true]

theorem jacobian1_column4 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    expandedStep (traceMetric b 1) (traceGradient b 1) (traceGradient b 2)
      (symmetricMap (traceHessian b 1)) (symmetricMap (traceHessian b 2))
      ![0,0,0,0,1] = ![n66 b,n16 b,n1319 b,n1326 b,n1328 b] := by
  have hs92 : n92 b = n91 b := by rw [trace_n92 b hb hp,trace_n91 b hb hp]
  have hs120 : n120 b = n119 b := by rw [trace_n120 b hb hp,trace_n119 b hb hp]
  have hs184 : n184 b = n183 b := by rw [trace_n184 b hb hp,trace_n183 b hb hp]
  have hs198 : n198 b = n197 b := by rw [trace_n198 b hb hp,trace_n197 b hb hp]
  have hs212 : n212 b = n211 b := by rw [trace_n212 b hb hp,trace_n211 b hb hp]
  have hs226 : n226 b = n225 b := by rw [trace_n226 b hb hp,trace_n225 b hb hp]
  have hs231 : n231 b = n230 b := by rw [trace_n231 b hb hp,trace_n230 b hb hp]
  ext i
  fin_cases i <;>
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail, expandedStep, expandedUpdate, traceMetric, traceGradient, traceHessian, addSym, outerSym, crossSym, pack, point, metric, Sym2.mulV, Sym2.scale, dot, symmetricMap_apply, div_eq_mul_inv, mul_inv_rev, n13, n15, n16, n64, n66, n122, n233, n302, n303, n320, n321, n322, n323, n929, n930, n931, n932, n933, n934, n935, n936, n937, n938, n939, n941, n942, n943, n945, n946, n947, n949, n950, n951, n953, n1004, n1005, n1010, n1011, n1023, n1024, n1026, n1027, n1039, n1199, n1200, n1201, n1207, n1208, n1212, n1258, n1259, n1260, n1261, n1262, n1263, n1264, n1265, n1266, n1267, n1268, n1269, n1270, n1271, n1272, n1273, n1274, n1275, n1276, n1277, n1278, n1279, n1280, n1282, n1283, n1284, n1285, n1286, n1288, n1290, n1291, n1292, n1294, n1295, n1296, n1298, n1299, n1300, n1301, n1302, n1304, n1305, n1306, n1308, n1309, n1310, n1311, n1312, n1313, n1314, n1315, n1316, n1318, n1319, n1320, n1322, n1323, n1325, n1326, n1328, hs92, hs120, hs184, hs198, hs212, hs226, hs231] <;> ring <;> try simp only [true_or,or_true]

end
end BFGS.Counterexample
