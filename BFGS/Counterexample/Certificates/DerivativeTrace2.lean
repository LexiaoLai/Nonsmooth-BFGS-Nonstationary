import BFGS.Counterexample.DerivativeCore
import BFGS.Counterexample.TraceBridge
import BFGS.Counterexample.Certificates.IntervalTrace35

namespace BFGS.Counterexample
noncomputable section
open BFGS.Algorithm Trace
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

attribute [local irreducible] n0 n15 n21 n34 n55 n56 n61 n63 n64 n65 n66 n90 n91 n92 n93 n118 n119 n120 n121 n122 n123 n182 n183 n184 n185 n196 n197 n198 n199 n210 n211 n212 n213 n224 n225 n226 n227 n229 n230 n231 n232 n233

lemma trace2c (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    dot (-(traceMetric b 2).mulV (traceGradient b 2)) (traceGradient b 3-traceGradient b 2) = 4/9 := by
  rw [traceMetric_eq b hb hp,traceGradient_eq b hb hp]
  change dot (s2 b) (y2 b) = 4/9
  exact curvature2 b hb hp
lemma node329c (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) : n329 b = 4/9 := by
  rw [trace_n329 b hb hp]
  change dot (s2 b) (y2 b) = 4/9
  exact curvature2 b hb hp

theorem jacobian2_column0 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    expandedStep (traceMetric b 2) (traceGradient b 2) (traceGradient b 3)
      (symmetricMap (traceHessian b 2)) (symmetricMap (traceHessian b 3))
      ![1,0,0,0,0] = ![n1481 b,n1480 b,n1614 b,n1615 b,n1617 b] := by
  have hs92 : n92 b = n91 b := by rw [trace_n92 b hb hp,trace_n91 b hb hp]
  have hs120 : n120 b = n119 b := by rw [trace_n120 b hb hp,trace_n119 b hb hp]
  have hs184 : n184 b = n183 b := by rw [trace_n184 b hb hp,trace_n183 b hb hp]
  have hs198 : n198 b = n197 b := by rw [trace_n198 b hb hp,trace_n197 b hb hp]
  have hs212 : n212 b = n211 b := by rw [trace_n212 b hb hp,trace_n211 b hb hp]
  have hs226 : n226 b = n225 b := by rw [trace_n226 b hb hp,trace_n225 b hb hp]
  have hs231 : n231 b = n230 b := by rw [trace_n231 b hb hp,trace_n230 b hb hp]
  ext i
  fin_cases i <;>
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail, expandedStep, expandedUpdate, traceMetric, traceGradient, traceHessian, addSym, outerSym, crossSym, pack, point, metric, Sym2.mulV, Sym2.scale, dot, symmetricMap_apply, div_eq_mul_inv, mul_inv_rev, n13, n15, n16, n56, n64, n66, n122, n233, n304, n305, n306, n307, n308, n309, n310, n311, n324, n325, n326, n327, n328, n329, n1473, n1474, n1475, n1476, n1477, n1478, n1479, n1480, n1481, n1482, n1483, n1484, n1485, n1486, n1487, n1488, n1489, n1490, n1491, n1492, n1493, n1494, n1495, n1496, n1497, n1498, n1499, n1500, n1501, n1502, n1503, n1504, n1505, n1506, n1507, n1508, n1509, n1511, n1512, n1513, n1515, n1516, n1517, n1519, n1520, n1521, n1523, n1524, n1525, n1526, n1527, n1528, n1529, n1530, n1531, n1532, n1533, n1534, n1535, n1537, n1538, n1539, n1541, n1542, n1543, n1545, n1546, n1547, n1549, n1550, n1551, n1553, n1554, n1555, n1557, n1558, n1559, n1561, n1562, n1563, n1565, n1566, n1567, n1569, n1570, n1571, n1573, n1574, n1575, n1576, n1577, n1579, n1580, n1581, n1582, n1583, n1584, n1586, n1587, n1588, n1590, n1591, n1592, n1593, n1594, n1595, n1596, n1597, n1598, n1599, n1600, n1601, n1602, n1604, n1605, n1606, n1608, n1609, n1610, n1611, n1613, n1614, n1615, n1617, hs92, hs120, hs184, hs198, hs212, hs226, hs231]
  all_goals
    generalize n21 b = v21
    generalize n34 b = v34
    generalize n55 b = v55
    generalize n90 b = v90
    generalize n91 b = v91
    generalize n93 b = v93
    generalize n210 b = v210
    generalize n211 b = v211
    generalize n213 b = v213
    generalize n224 b = v224
    generalize n225 b = v225
    generalize n227 b = v227
    ring <;> try simp only [true_or,or_true]

theorem jacobian2_column1 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    expandedStep (traceMetric b 2) (traceGradient b 2) (traceGradient b 3)
      (symmetricMap (traceHessian b 2)) (symmetricMap (traceHessian b 3))
      ![0,1,0,0,0] = ![n1624 b,n1626 b,n1725 b,n1726 b,n1728 b] := by
  have hs92 : n92 b = n91 b := by rw [trace_n92 b hb hp,trace_n91 b hb hp]
  have hs120 : n120 b = n119 b := by rw [trace_n120 b hb hp,trace_n119 b hb hp]
  have hs184 : n184 b = n183 b := by rw [trace_n184 b hb hp,trace_n183 b hb hp]
  have hs198 : n198 b = n197 b := by rw [trace_n198 b hb hp,trace_n197 b hb hp]
  have hs212 : n212 b = n211 b := by rw [trace_n212 b hb hp,trace_n211 b hb hp]
  have hs226 : n226 b = n225 b := by rw [trace_n226 b hb hp,trace_n225 b hb hp]
  have hs231 : n231 b = n230 b := by rw [trace_n231 b hb hp,trace_n230 b hb hp]
  ext i
  fin_cases i <;>
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail, expandedStep, expandedUpdate, traceMetric, traceGradient, traceHessian, addSym, outerSym, crossSym, pack, point, metric, Sym2.mulV, Sym2.scale, dot, symmetricMap_apply, div_eq_mul_inv, mul_inv_rev, n13, n15, n16, n56, n64, n66, n122, n233, n304, n305, n306, n307, n308, n309, n310, n311, n324, n325, n326, n327, n328, n329, n1499, n1500, n1501, n1502, n1503, n1504, n1505, n1506, n1507, n1508, n1509, n1511, n1512, n1513, n1515, n1516, n1517, n1519, n1520, n1521, n1523, n1574, n1575, n1580, n1581, n1593, n1594, n1596, n1597, n1609, n1618, n1619, n1620, n1621, n1622, n1623, n1624, n1625, n1626, n1627, n1628, n1629, n1630, n1631, n1632, n1633, n1634, n1635, n1636, n1637, n1638, n1639, n1640, n1641, n1642, n1643, n1644, n1645, n1646, n1647, n1648, n1649, n1650, n1651, n1652, n1653, n1654, n1655, n1657, n1658, n1659, n1661, n1662, n1663, n1665, n1666, n1667, n1669, n1670, n1671, n1673, n1674, n1675, n1677, n1678, n1679, n1681, n1682, n1683, n1685, n1686, n1687, n1689, n1690, n1691, n1693, n1694, n1695, n1697, n1698, n1699, n1700, n1702, n1703, n1704, n1706, n1707, n1708, n1709, n1710, n1711, n1712, n1713, n1714, n1716, n1717, n1718, n1720, n1721, n1722, n1724, n1725, n1726, n1728, hs92, hs120, hs184, hs198, hs212, hs226, hs231]
  all_goals
    generalize n21 b = v21
    generalize n34 b = v34
    generalize n55 b = v55
    generalize n90 b = v90
    generalize n91 b = v91
    generalize n93 b = v93
    generalize n210 b = v210
    generalize n211 b = v211
    generalize n213 b = v213
    generalize n224 b = v224
    generalize n225 b = v225
    generalize n227 b = v227
    ring <;> try simp only [true_or,or_true]

theorem jacobian2_column2 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    expandedStep (traceMetric b 2) (traceGradient b 2) (traceGradient b 3)
      (symmetricMap (traceHessian b 2)) (symmetricMap (traceHessian b 3))
      ![0,0,1,0,0] = ![n56 b,n66 b,n1805 b,n1806 b,n1801 b] := by
  have hs92 : n92 b = n91 b := by rw [trace_n92 b hb hp,trace_n91 b hb hp]
  have hs120 : n120 b = n119 b := by rw [trace_n120 b hb hp,trace_n119 b hb hp]
  have hs184 : n184 b = n183 b := by rw [trace_n184 b hb hp,trace_n183 b hb hp]
  have hs198 : n198 b = n197 b := by rw [trace_n198 b hb hp,trace_n197 b hb hp]
  have hs212 : n212 b = n211 b := by rw [trace_n212 b hb hp,trace_n211 b hb hp]
  have hs226 : n226 b = n225 b := by rw [trace_n226 b hb hp,trace_n225 b hb hp]
  have hs231 : n231 b = n230 b := by rw [trace_n231 b hb hp,trace_n230 b hb hp]
  ext i
  fin_cases i <;>
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail, expandedStep, expandedUpdate, traceMetric, traceGradient, traceHessian, addSym, outerSym, crossSym, pack, point, metric, Sym2.mulV, Sym2.scale, dot, symmetricMap_apply, div_eq_mul_inv, mul_inv_rev, n13, n15, n16, n56, n64, n66, n122, n233, n304, n305, n306, n307, n308, n309, n310, n311, n324, n325, n326, n327, n328, n329, n1499, n1500, n1501, n1502, n1503, n1504, n1505, n1506, n1507, n1508, n1509, n1511, n1512, n1513, n1515, n1516, n1517, n1519, n1520, n1521, n1523, n1574, n1575, n1580, n1581, n1593, n1594, n1596, n1597, n1609, n1729, n1730, n1731, n1732, n1733, n1734, n1735, n1736, n1737, n1738, n1739, n1740, n1741, n1742, n1743, n1744, n1745, n1746, n1747, n1748, n1749, n1750, n1751, n1753, n1754, n1755, n1757, n1758, n1760, n1762, n1763, n1764, n1765, n1767, n1768, n1769, n1770, n1771, n1773, n1774, n1775, n1777, n1778, n1779, n1780, n1781, n1783, n1784, n1785, n1787, n1788, n1789, n1790, n1791, n1792, n1793, n1794, n1795, n1797, n1798, n1799, n1801, n1802, n1803, n1805, n1806, hs92, hs120, hs184, hs198, hs212, hs226, hs231]
  all_goals
    generalize n21 b = v21
    generalize n34 b = v34
    generalize n55 b = v55
    generalize n90 b = v90
    generalize n91 b = v91
    generalize n93 b = v93
    generalize n210 b = v210
    generalize n211 b = v211
    generalize n213 b = v213
    generalize n224 b = v224
    generalize n225 b = v225
    generalize n227 b = v227
    ring <;> try simp only [true_or,or_true]

theorem jacobian2_column3 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    expandedStep (traceMetric b 2) (traceGradient b 2) (traceGradient b 3)
      (symmetricMap (traceHessian b 2)) (symmetricMap (traceHessian b 3))
      ![0,0,0,1,0] = ![n324 b,n56 b,n1902 b,n1903 b,n1905 b] := by
  have hs92 : n92 b = n91 b := by rw [trace_n92 b hb hp,trace_n91 b hb hp]
  have hs120 : n120 b = n119 b := by rw [trace_n120 b hb hp,trace_n119 b hb hp]
  have hs184 : n184 b = n183 b := by rw [trace_n184 b hb hp,trace_n183 b hb hp]
  have hs198 : n198 b = n197 b := by rw [trace_n198 b hb hp,trace_n197 b hb hp]
  have hs212 : n212 b = n211 b := by rw [trace_n212 b hb hp,trace_n211 b hb hp]
  have hs226 : n226 b = n225 b := by rw [trace_n226 b hb hp,trace_n225 b hb hp]
  have hs231 : n231 b = n230 b := by rw [trace_n231 b hb hp,trace_n230 b hb hp]
  ext i
  fin_cases i <;>
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail, expandedStep, expandedUpdate, traceMetric, traceGradient, traceHessian, addSym, outerSym, crossSym, pack, point, metric, Sym2.mulV, Sym2.scale, dot, symmetricMap_apply, div_eq_mul_inv, mul_inv_rev, n13, n15, n16, n56, n64, n66, n122, n233, n304, n305, n306, n307, n308, n309, n310, n311, n324, n325, n326, n327, n328, n329, n1499, n1500, n1501, n1502, n1503, n1504, n1505, n1506, n1507, n1508, n1509, n1511, n1512, n1513, n1515, n1516, n1517, n1519, n1520, n1521, n1523, n1574, n1575, n1580, n1581, n1593, n1594, n1596, n1597, n1609, n1750, n1751, n1752, n1758, n1759, n1763, n1808, n1809, n1810, n1811, n1812, n1813, n1814, n1815, n1816, n1817, n1818, n1819, n1820, n1821, n1822, n1823, n1824, n1825, n1826, n1827, n1828, n1829, n1830, n1831, n1832, n1833, n1834, n1835, n1836, n1837, n1838, n1839, n1841, n1842, n1844, n1845, n1846, n1848, n1849, n1851, n1852, n1854, n1855, n1856, n1857, n1858, n1860, n1861, n1862, n1864, n1865, n1866, n1868, n1869, n1870, n1872, n1873, n1875, n1876, n1877, n1879, n1880, n1881, n1883, n1884, n1885, n1886, n1887, n1888, n1889, n1890, n1891, n1893, n1894, n1895, n1897, n1898, n1899, n1901, n1902, n1903, n1905, hs92, hs120, hs184, hs198, hs212, hs226, hs231]
  all_goals
    generalize n21 b = v21
    generalize n34 b = v34
    generalize n55 b = v55
    generalize n90 b = v90
    generalize n91 b = v91
    generalize n93 b = v93
    generalize n210 b = v210
    generalize n211 b = v211
    generalize n213 b = v213
    generalize n224 b = v224
    generalize n225 b = v225
    generalize n227 b = v227
    ring <;> try simp only [true_or,or_true]

theorem jacobian2_column4 (b : ℝ) (hb : 1/2 < b) (hp : quartic b = 0) :
    expandedStep (traceMetric b 2) (traceGradient b 2) (traceGradient b 3)
      (symmetricMap (traceHessian b 2)) (symmetricMap (traceHessian b 3))
      ![0,0,0,0,1] = ![n66 b,n324 b,n1967 b,n1974 b,n1976 b] := by
  have hs92 : n92 b = n91 b := by rw [trace_n92 b hb hp,trace_n91 b hb hp]
  have hs120 : n120 b = n119 b := by rw [trace_n120 b hb hp,trace_n119 b hb hp]
  have hs184 : n184 b = n183 b := by rw [trace_n184 b hb hp,trace_n183 b hb hp]
  have hs198 : n198 b = n197 b := by rw [trace_n198 b hb hp,trace_n197 b hb hp]
  have hs212 : n212 b = n211 b := by rw [trace_n212 b hb hp,trace_n211 b hb hp]
  have hs226 : n226 b = n225 b := by rw [trace_n226 b hb hp,trace_n225 b hb hp]
  have hs231 : n231 b = n230 b := by rw [trace_n231 b hb hp,trace_n230 b hb hp]
  ext i
  fin_cases i <;>
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail, expandedStep, expandedUpdate, traceMetric, traceGradient, traceHessian, addSym, outerSym, crossSym, pack, point, metric, Sym2.mulV, Sym2.scale, dot, symmetricMap_apply, div_eq_mul_inv, mul_inv_rev, n13, n15, n16, n56, n64, n66, n122, n233, n304, n305, n306, n307, n308, n309, n310, n311, n324, n325, n326, n327, n328, n329, n1499, n1500, n1501, n1502, n1503, n1504, n1505, n1506, n1507, n1508, n1509, n1511, n1512, n1513, n1515, n1516, n1517, n1519, n1520, n1521, n1523, n1574, n1575, n1580, n1581, n1593, n1594, n1596, n1597, n1609, n1838, n1839, n1840, n1849, n1850, n1856, n1906, n1907, n1908, n1909, n1910, n1911, n1912, n1913, n1914, n1915, n1916, n1917, n1918, n1919, n1920, n1921, n1922, n1923, n1924, n1925, n1926, n1927, n1928, n1930, n1931, n1932, n1933, n1934, n1936, n1938, n1939, n1940, n1942, n1943, n1944, n1946, n1947, n1948, n1949, n1950, n1952, n1953, n1954, n1956, n1957, n1958, n1959, n1960, n1961, n1962, n1963, n1964, n1966, n1967, n1968, n1970, n1971, n1973, n1974, n1976, hs92, hs120, hs184, hs198, hs212, hs226, hs231]
  all_goals
    generalize n21 b = v21
    generalize n34 b = v34
    generalize n55 b = v55
    generalize n90 b = v90
    generalize n91 b = v91
    generalize n93 b = v93
    generalize n210 b = v210
    generalize n211 b = v211
    generalize n213 b = v213
    generalize n224 b = v224
    generalize n225 b = v225
    generalize n227 b = v227
    ring <;> try simp only [true_or,or_true]

end
end BFGS.Counterexample
