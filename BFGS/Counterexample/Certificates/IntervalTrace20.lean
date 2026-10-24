import BFGS.Counterexample.Certificates.IntervalTrace19

/-! Generated arithmetic proofs. Each bound is checked by the Lean kernel. -/
namespace BFGS.Counterexample.Trace
noncomputable section
open BFGS RationalInterval
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false

def n1800 (b : ℝ) : ℝ := (n1786 b) + (n1796 b)
def i1800 : RationalInterval := ⟨(-227497518748344942767701722249 / 200000000000000000000000000000 : ℚ), (-1137487492836324859954868537321 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1800 (b : ℝ) (hb : rootInterval.Contains b) : i1800.Contains (n1800 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1786 b hb) (b1796 b hb))
    (by norm_num [i1800, i1786, i1796, RationalInterval.add]) (by norm_num [i1800, i1786, i1796, RationalInterval.add])

def n1801 (b : ℝ) : ℝ := (n1787 b) + (n1797 b)
def i1801 : RationalInterval := ⟨(-94547241380867730522890283373 / 500000000000000000000000000000 : ℚ), (-189094428281220459761428090339 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1801 (b : ℝ) (hb : rootInterval.Contains b) : i1801.Contains (n1801 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1787 b hb) (b1797 b hb))
    (by norm_num [i1801, i1787, i1797, RationalInterval.add]) (by norm_num [i1801, i1787, i1797, RationalInterval.add])

def n1802 (b : ℝ) : ℝ := (n1609 b) * (n1753 b)
def i1802 : RationalInterval := ⟨(894822506140031375839353612121 / 125000000000000000000000000000 : ℚ), (894822524398266008545094512533 / 125000000000000000000000000000 : ℚ)⟩
theorem b1802 (b : ℝ) (hb : rootInterval.Contains b) : i1802.Contains (n1802 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1609 b hb) (b1753 b hb))
    (by norm_num [i1802, i1609, i1753, RationalInterval.mul]) (by norm_num [i1802, i1609, i1753, RationalInterval.mul])

def n1803 (b : ℝ) : ℝ := (n1609 b) * (n1750 b)
def i1803 : RationalInterval := ⟨(103656913505121279717191702251 / 50000000000000000000000000000 : ℚ), (414627662598378210738883302069 / 200000000000000000000000000000 : ℚ)⟩
theorem b1803 (b : ℝ) (hb : rootInterval.Contains b) : i1803.Contains (n1803 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1609 b hb) (b1750 b hb))
    (by norm_num [i1803, i1609, i1750, RationalInterval.mul]) (by norm_num [i1803, i1609, i1750, RationalInterval.mul])

def n1804 (b : ℝ) : ℝ := (n1609 b) * (n1752 b)
def i1804 : RationalInterval := ⟨(103656913505121279717191702251 / 50000000000000000000000000000 : ℚ), (414627662598378210738883302069 / 200000000000000000000000000000 : ℚ)⟩
theorem b1804 (b : ℝ) (hb : rootInterval.Contains b) : i1804.Contains (n1804 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1609 b hb) (b1752 b hb))
    (by norm_num [i1804, i1609, i1752, RationalInterval.mul]) (by norm_num [i1804, i1609, i1752, RationalInterval.mul])

def n1805 (b : ℝ) : ℝ := (n1798 b) + (n1802 b)
def i1805 : RationalInterval := ⟨(1109012119895693017095281382209 / 200000000000000000000000000000 : ℚ), (22180243700701226643331732773 / 4000000000000000000000000000 : ℚ)⟩
theorem b1805 (b : ℝ) (hb : rootInterval.Contains b) : i1805.Contains (n1805 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1798 b hb) (b1802 b hb))
    (by norm_num [i1805, i1798, i1802, RationalInterval.add]) (by norm_num [i1805, i1798, i1802, RationalInterval.add])

def n1806 (b : ℝ) : ℝ := (n1799 b) + (n1803 b)
def i1806 : RationalInterval := ⟨(37426027054428035220213017351 / 40000000000000000000000000000 : ℚ), (29239088129861443554360874157 / 31250000000000000000000000000 : ℚ)⟩
theorem b1806 (b : ℝ) (hb : rootInterval.Contains b) : i1806.Contains (n1806 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1799 b hb) (b1803 b hb))
    (by norm_num [i1806, i1799, i1803, RationalInterval.add]) (by norm_num [i1806, i1799, i1803, RationalInterval.add])

def n1807 (b : ℝ) : ℝ := (n1800 b) + (n1804 b)
def i1807 : RationalInterval := ⟨(37426027054428035220213017351 / 40000000000000000000000000000 : ℚ), (29239088129861443554360874157 / 31250000000000000000000000000 : ℚ)⟩
theorem b1807 (b : ℝ) (hb : rootInterval.Contains b) : i1807.Contains (n1807 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1800 b hb) (b1804 b hb))
    (by norm_num [i1807, i1800, i1804, RationalInterval.add]) (by norm_num [i1807, i1800, i1804, RationalInterval.add])

def n1808 (b : ℝ) : ℝ := (n224 b) * (n324 b)
def i1808 : RationalInterval := ⟨(-3825773005418404156765775703 / 250000000000000000000000000000 : ℚ), (-3060618365378038519954689811 / 200000000000000000000000000000 : ℚ)⟩
theorem b1808 (b : ℝ) (hb : rootInterval.Contains b) : i1808.Contains (n1808 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b224 b hb) (b324 b hb))
    (by norm_num [i1808, i224, i324, RationalInterval.mul]) (by norm_num [i1808, i224, i324, RationalInterval.mul])

def n1809 (b : ℝ) : ℝ := (n225 b) * (n56 b)
def i1809 : RationalInterval := ⟨(49176271504343288767623647219 / 1000000000000000000000000000000 : ℚ), (6147034001438126477260932877 / 125000000000000000000000000000 : ℚ)⟩
theorem b1809 (b : ℝ) (hb : rootInterval.Contains b) : i1809.Contains (n1809 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b225 b hb) (b56 b hb))
    (by norm_num [i1809, i225, i56, RationalInterval.mul]) (by norm_num [i1809, i225, i56, RationalInterval.mul])

def n1810 (b : ℝ) : ℝ := (n1808 b) + (n1809 b)
def i1810 : RationalInterval := ⟨(33873179482669672140560544407 / 1000000000000000000000000000000 : ℚ), (33873180184614819218314013961 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1810 (b : ℝ) (hb : rootInterval.Contains b) : i1810.Contains (n1810 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1808 b hb) (b1809 b hb))
    (by norm_num [i1810, i1808, i1809, RationalInterval.add]) (by norm_num [i1810, i1808, i1809, RationalInterval.add])

def n1811 (b : ℝ) : ℝ := (n226 b) * (n324 b)
def i1811 : RationalInterval := ⟨(-3830409291397728227794289233 / 1000000000000000000000000000000 : ℚ), (-1915204613406375324961220069 / 500000000000000000000000000000 : ℚ)⟩
theorem b1811 (b : ℝ) (hb : rootInterval.Contains b) : i1811.Contains (n1811 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b226 b hb) (b324 b hb))
    (by norm_num [i1811, i226, i324, RationalInterval.mul]) (by norm_num [i1811, i226, i324, RationalInterval.mul])

def n1812 (b : ℝ) : ℝ := (n227 b) * (n56 b)
def i1812 : RationalInterval := ⟨(12308966465161961587412514903 / 1000000000000000000000000000000 : ℚ), (12308966642975878572942364231 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1812 (b : ℝ) (hb : rootInterval.Contains b) : i1812.Contains (n1812 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b227 b hb) (b56 b hb))
    (by norm_num [i1812, i227, i56, RationalInterval.mul]) (by norm_num [i1812, i227, i56, RationalInterval.mul])

def n1813 (b : ℝ) : ℝ := (n1811 b) + (n1812 b)
def i1813 : RationalInterval := ⟨(847855717376423335961822567 / 100000000000000000000000000000 : ℚ), (8478557416163127923019924093 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1813 (b : ℝ) (hb : rootInterval.Contains b) : i1813.Contains (n1813 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1811 b hb) (b1812 b hb))
    (by norm_num [i1813, i1811, i1812, RationalInterval.add]) (by norm_num [i1813, i1811, i1812, RationalInterval.add])

def n1814 (b : ℝ) : ℝ := (n324 b) * (n325 b)
def i1814 : RationalInterval := ⟨(4807971526618709596735548839 / 1000000000000000000000000000000 : ℚ), (150249113016179197255583607 / 31250000000000000000000000000 : ℚ)⟩
theorem b1814 (b : ℝ) (hb : rootInterval.Contains b) : i1814.Contains (n1814 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b324 b hb) (b325 b hb))
    (by norm_num [i1814, i324, i325, RationalInterval.mul]) (by norm_num [i1814, i324, i325, RationalInterval.mul])

def n1815 (b : ℝ) : ℝ := (n56 b) * (n326 b)
def i1815 : RationalInterval := ⟨(502403985453217702741311174049 / 500000000000000000000000000000 : ℚ), (502403986122938513428815833733 / 500000000000000000000000000000 : ℚ)⟩
theorem b1815 (b : ℝ) (hb : rootInterval.Contains b) : i1815.Contains (n1815 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b56 b hb) (b326 b hb))
    (by norm_num [i1815, i56, i326, RationalInterval.mul]) (by norm_num [i1815, i56, i326, RationalInterval.mul])

def n1816 (b : ℝ) : ℝ := (n1814 b) + (n1815 b)
def i1816 : RationalInterval := ⟨(1009615942433054115079357896937 / 1000000000000000000000000000000 : ℚ), (100961594386239476116981034289 / 100000000000000000000000000000 : ℚ)⟩
theorem b1816 (b : ℝ) (hb : rootInterval.Contains b) : i1816.Contains (n1816 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1814 b hb) (b1815 b hb))
    (by norm_num [i1816, i1814, i1815, RationalInterval.add]) (by norm_num [i1816, i1814, i1815, RationalInterval.add])

def n1817 (b : ℝ) : ℝ := (n310 b) * (n1810 b)
def i1817 : RationalInterval := ⟨(7551650378227795961352839743 / 250000000000000000000000000000 : ℚ), (241652817658636297103989997 / 8000000000000000000000000000 : ℚ)⟩
theorem b1817 (b : ℝ) (hb : rootInterval.Contains b) : i1817.Contains (n1817 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b310 b hb) (b1810 b hb))
    (by norm_num [i1817, i310, i1810, RationalInterval.mul]) (by norm_num [i1817, i310, i1810, RationalInterval.mul])

def n1818 (b : ℝ) : ℝ := (n311 b) * (n1813 b)
def i1818 : RationalInterval := ⟨(4379244920481164470552976589 / 1000000000000000000000000000000 : ℚ), (218962252842484121883466977 / 50000000000000000000000000000 : ℚ)⟩
theorem b1818 (b : ℝ) (hb : rootInterval.Contains b) : i1818.Contains (n1818 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b311 b hb) (b1813 b hb))
    (by norm_num [i1818, i311, i1813, RationalInterval.mul]) (by norm_num [i1818, i311, i1813, RationalInterval.mul])

def n1819 (b : ℝ) : ℝ := (n1817 b) + (n1818 b)
def i1819 : RationalInterval := ⟨(34585846433392348315964335561 / 1000000000000000000000000000000 : ℚ), (6917169452835843915133617833 / 200000000000000000000000000000 : ℚ)⟩
theorem b1819 (b : ℝ) (hb : rootInterval.Contains b) : i1819.Contains (n1819 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1817 b hb) (b1818 b hb))
    (by norm_num [i1819, i1817, i1818, RationalInterval.add]) (by norm_num [i1819, i1817, i1818, RationalInterval.add])

def n1820 (b : ℝ) : ℝ := (n1816 b) + (n1819 b)
def i1820 : RationalInterval := ⟨(522100894433223231697661116249 / 500000000000000000000000000000 : ℚ), (208840358225314796149095686411 / 200000000000000000000000000000 : ℚ)⟩
theorem b1820 (b : ℝ) (hb : rootInterval.Contains b) : i1820.Contains (n1820 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1816 b hb) (b1819 b hb))
    (by norm_num [i1820, i1816, i1819, RationalInterval.add]) (by norm_num [i1820, i1816, i1819, RationalInterval.add])

def n1821 (b : ℝ) : ℝ := (n90 b) * (n1810 b)
def i1821 : RationalInterval := ⟨(15162407854216002428273017797 / 500000000000000000000000000000 : ℚ), (30324816378094689751459679841 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1821 (b : ℝ) (hb : rootInterval.Contains b) : i1821.Contains (n1821 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b90 b hb) (b1810 b hb))
    (by norm_num [i1821, i90, i1810, RationalInterval.mul]) (by norm_num [i1821, i90, i1810, RationalInterval.mul])

def n1822 (b : ℝ) : ℝ := (n91 b) * (n1813 b)
def i1822 : RationalInterval := ⟨(223009230338856894380055831 / 50000000000000000000000000000 : ℚ), (892036949323907803029644911 / 200000000000000000000000000000 : ℚ)⟩
theorem b1822 (b : ℝ) (hb : rootInterval.Contains b) : i1822.Contains (n1822 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b91 b hb) (b1813 b hb))
    (by norm_num [i1822, i91, i1813, RationalInterval.mul]) (by norm_num [i1822, i91, i1813, RationalInterval.mul])

def n1823 (b : ℝ) : ℝ := (n1821 b) + (n1822 b)
def i1823 : RationalInterval := ⟨(17392500157604571372073576107 / 500000000000000000000000000000 : ℚ), (8696250281178557191651976099 / 250000000000000000000000000000 : ℚ)⟩
theorem b1823 (b : ℝ) (hb : rootInterval.Contains b) : i1823.Contains (n1823 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1821 b hb) (b1822 b hb))
    (by norm_num [i1823, i1821, i1822, RationalInterval.add]) (by norm_num [i1823, i1821, i1822, RationalInterval.add])

def n1824 (b : ℝ) : ℝ := (n92 b) * (n1810 b)
def i1824 : RationalInterval := ⟨(4454786077154317527822107367 / 250000000000000000000000000000 : ℚ), (55684827200798517480386131 / 3125000000000000000000000000 : ℚ)⟩
theorem b1824 (b : ℝ) (hb : rootInterval.Contains b) : i1824.Contains (n1824 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b92 b hb) (b1810 b hb))
    (by norm_num [i1824, i92, i1810, RationalInterval.mul]) (by norm_num [i1824, i92, i1810, RationalInterval.mul])

def n1825 (b : ℝ) : ℝ := (n93 b) * (n1813 b)
def i1825 : RationalInterval := ⟨(3402462949982271019780864233 / 1000000000000000000000000000000 : ℚ), (3402463055748846147232843701 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1825 (b : ℝ) (hb : rootInterval.Contains b) : i1825.Contains (n1825 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b93 b hb) (b1813 b hb))
    (by norm_num [i1825, i93, i1813, RationalInterval.mul]) (by norm_num [i1825, i93, i1813, RationalInterval.mul])

def n1826 (b : ℝ) : ℝ := (n1824 b) + (n1825 b)
def i1826 : RationalInterval := ⟨(21221607258599541131069293701 / 1000000000000000000000000000000 : ℚ), (21221607760004371740956405621 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1826 (b : ℝ) (hb : rootInterval.Contains b) : i1826.Contains (n1826 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1824 b hb) (b1825 b hb))
    (by norm_num [i1826, i1824, i1825, RationalInterval.add]) (by norm_num [i1826, i1824, i1825, RationalInterval.add])

def n1827 (b : ℝ) : ℝ := (n326 b) + (n1823 b)
def i1827 : RationalInterval := ⟨(498677773844924045857352166319 / 500000000000000000000000000000 : ℚ), (498677774718182645136730119893 / 500000000000000000000000000000 : ℚ)⟩
theorem b1827 (b : ℝ) (hb : rootInterval.Contains b) : i1827.Contains (n1827 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b326 b hb) (b1823 b hb))
    (by norm_num [i1827, i326, i1823, RationalInterval.add]) (by norm_num [i1827, i326, i1823, RationalInterval.add])

def n1828 (b : ℝ) : ℝ := (n325 b) + (n1826 b)
def i1828 : RationalInterval := ⟨(-37910289867653204109560596097 / 1000000000000000000000000000000 : ℚ), (-189551443345313500484677891 / 5000000000000000000000000000 : ℚ)⟩
theorem b1828 (b : ℝ) (hb : rootInterval.Contains b) : i1828.Contains (n1828 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b325 b hb) (b1826 b hb))
    (by norm_num [i1828, i325, i1826, RationalInterval.add]) (by norm_num [i1828, i325, i1826, RationalInterval.add])

def n1829 (b : ℝ) : ℝ := (n1810 b) * (n1501 b)
def i1829 : RationalInterval := ⟨(1919877449325285962413815329 / 125000000000000000000000000000 : ℚ), (1535902000056746851225067689 / 100000000000000000000000000000 : ℚ)⟩
theorem b1829 (b : ℝ) (hb : rootInterval.Contains b) : i1829.Contains (n1829 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1810 b hb) (b1501 b hb))
    (by norm_num [i1829, i1810, i1501, RationalInterval.mul]) (by norm_num [i1829, i1810, i1501, RationalInterval.mul])

def n1830 (b : ℝ) : ℝ := (n1813 b) * (n1504 b)
def i1830 : RationalInterval := ⟨(3011371446294652889645518907 / 1000000000000000000000000000000 : ℚ), (1505685773625180008166566477 / 500000000000000000000000000000 : ℚ)⟩
theorem b1830 (b : ℝ) (hb : rootInterval.Contains b) : i1830.Contains (n1830 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1813 b hb) (b1504 b hb))
    (by norm_num [i1830, i1813, i1504, RationalInterval.mul]) (by norm_num [i1830, i1813, i1504, RationalInterval.mul])

def n1831 (b : ℝ) : ℝ := (n1829 b) + (n1830 b)
def i1831 : RationalInterval := ⟨(18370391040896940588956041539 / 1000000000000000000000000000000 : ℚ), (4592597886954457132145952461 / 250000000000000000000000000000 : ℚ)⟩
theorem b1831 (b : ℝ) (hb : rootInterval.Contains b) : i1831.Contains (n1831 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1829 b hb) (b1830 b hb))
    (by norm_num [i1831, i1829, i1830, RationalInterval.add]) (by norm_num [i1831, i1829, i1830, RationalInterval.add])

def n1832 (b : ℝ) : ℝ := (n1831 b) * (n13 b)
def i1832 : RationalInterval := ⟨(18370391040896940588956041539 / 500000000000000000000000000000 : ℚ), (4592597886954457132145952461 / 125000000000000000000000000000 : ℚ)⟩
theorem b1832 (b : ℝ) (hb : rootInterval.Contains b) : i1832.Contains (n1832 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1831 b hb) (b13 b hb))
    (by norm_num [i1832, i1831, i13, RationalInterval.mul]) (by norm_num [i1832, i1831, i13, RationalInterval.mul])

def n1833 (b : ℝ) : ℝ := (n325 b) * (n326 b)
def i1833 : RationalInterval := ⟨(-56918622639525248681088164051 / 1000000000000000000000000000000 : ℚ), (-56918621913027549567509513279 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1833 (b : ℝ) (hb : rootInterval.Contains b) : i1833.Contains (n1833 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b325 b hb) (b326 b hb))
    (by norm_num [i1833, i325, i326, RationalInterval.mul]) (by norm_num [i1833, i325, i326, RationalInterval.mul])

def n1834 (b : ℝ) : ℝ := (n326 b) * (n325 b)
def i1834 : RationalInterval := ⟨(-56918622639525248681088164051 / 1000000000000000000000000000000 : ℚ), (-56918621913027549567509513279 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1834 (b : ℝ) (hb : rootInterval.Contains b) : i1834.Contains (n1834 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b326 b hb) (b325 b hb))
    (by norm_num [i1834, i326, i325, RationalInterval.mul]) (by norm_num [i1834, i326, i325, RationalInterval.mul])

def n1835 (b : ℝ) : ℝ := (n1833 b) + (n1834 b)
def i1835 : RationalInterval := ⟨(-56918622639525248681088164051 / 500000000000000000000000000000 : ℚ), (-56918621913027549567509513279 / 500000000000000000000000000000 : ℚ)⟩
theorem b1835 (b : ℝ) (hb : rootInterval.Contains b) : i1835.Contains (n1835 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1833 b hb) (b1834 b hb))
    (by norm_num [i1835, i1833, i1834, RationalInterval.add]) (by norm_num [i1835, i1833, i1834, RationalInterval.add])

def n1836 (b : ℝ) : ℝ := (n1832 b) + (n1835 b)
def i1836 : RationalInterval := ⟨(-2409264474914269255758257657 / 31250000000000000000000000000 : ℚ), (-7709646073041944207785140687 / 100000000000000000000000000000 : ℚ)⟩
theorem b1836 (b : ℝ) (hb : rootInterval.Contains b) : i1836.Contains (n1836 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1832 b hb) (b1835 b hb))
    (by norm_num [i1836, i1832, i1835, RationalInterval.add]) (by norm_num [i1836, i1832, i1835, RationalInterval.add])

def n1837 (b : ℝ) : ℝ := (n324 b) * (n310 b)
def i1837 : RationalInterval := ⟨(-18127002524344205341089600729 / 250000000000000000000000000000 : ℚ), (-72508009432204235440582074143 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1837 (b : ℝ) (hb : rootInterval.Contains b) : i1837.Contains (n1837 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b324 b hb) (b310 b hb))
    (by norm_num [i1837, i324, i310, RationalInterval.mul]) (by norm_num [i1837, i324, i310, RationalInterval.mul])

def n1838 (b : ℝ) : ℝ := (n324 b) * (n311 b)
def i1838 : RationalInterval := ⟨(-41996912693038953512671704771 / 1000000000000000000000000000000 : ℚ), (-41996912295846609291020274869 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1838 (b : ℝ) (hb : rootInterval.Contains b) : i1838.Contains (n1838 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b324 b hb) (b311 b hb))
    (by norm_num [i1838, i324, i311, RationalInterval.mul]) (by norm_num [i1838, i324, i311, RationalInterval.mul])

def n1839 (b : ℝ) : ℝ := (n310 b) * (n324 b)
def i1839 : RationalInterval := ⟨(-18127002524344205341089600729 / 250000000000000000000000000000 : ℚ), (-72508009432204235440582074143 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1839 (b : ℝ) (hb : rootInterval.Contains b) : i1839.Contains (n1839 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b310 b hb) (b324 b hb))
    (by norm_num [i1839, i310, i324, RationalInterval.mul]) (by norm_num [i1839, i310, i324, RationalInterval.mul])

def n1840 (b : ℝ) : ℝ := (n311 b) * (n324 b)
def i1840 : RationalInterval := ⟨(-41996912693038953512671704771 / 1000000000000000000000000000000 : ℚ), (-41996912295846609291020274869 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1840 (b : ℝ) (hb : rootInterval.Contains b) : i1840.Contains (n1840 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b311 b hb) (b324 b hb))
    (by norm_num [i1840, i311, i324, RationalInterval.mul]) (by norm_num [i1840, i311, i324, RationalInterval.mul])

def n1841 (b : ℝ) : ℝ := (n1837 b) + (n1839 b)
def i1841 : RationalInterval := ⟨(-18127002524344205341089600729 / 125000000000000000000000000000 : ℚ), (-72508009432204235440582074143 / 500000000000000000000000000000 : ℚ)⟩
theorem b1841 (b : ℝ) (hb : rootInterval.Contains b) : i1841.Contains (n1841 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1837 b hb) (b1839 b hb))
    (by norm_num [i1841, i1837, i1839, RationalInterval.add]) (by norm_num [i1841, i1837, i1839, RationalInterval.add])

def n1842 (b : ℝ) : ℝ := (n1838 b) + (n1751 b)
def i1842 : RationalInterval := ⟨(222222221869071946766068231319 / 250000000000000000000000000000 : ℚ), (177777778063560571782973102347 / 200000000000000000000000000000 : ℚ)⟩
theorem b1842 (b : ℝ) (hb : rootInterval.Contains b) : i1842.Contains (n1842 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1838 b hb) (b1751 b hb))
    (by norm_num [i1842, i1838, i1751, RationalInterval.add]) (by norm_num [i1842, i1838, i1751, RationalInterval.add])

def n1843 (b : ℝ) : ℝ := (n1749 b) + (n1840 b)
def i1843 : RationalInterval := ⟨(222222221869071946766068231319 / 250000000000000000000000000000 : ℚ), (177777778063560571782973102347 / 200000000000000000000000000000 : ℚ)⟩
theorem b1843 (b : ℝ) (hb : rootInterval.Contains b) : i1843.Contains (n1843 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1749 b hb) (b1840 b hb))
    (by norm_num [i1843, i1749, i1840, RationalInterval.add]) (by norm_num [i1843, i1749, i1840, RationalInterval.add])

def n1844 (b : ℝ) : ℝ := (n1750 b) + (n1752 b)
def i1844 : RationalInterval := ⟨(269586281662537047031989837787 / 250000000000000000000000000000 : ℚ), (539172564893892670092876089403 / 500000000000000000000000000000 : ℚ)⟩
theorem b1844 (b : ℝ) (hb : rootInterval.Contains b) : i1844.Contains (n1844 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1750 b hb) (b1752 b hb))
    (by norm_num [i1844, i1750, i1752, RationalInterval.add]) (by norm_num [i1844, i1750, i1752, RationalInterval.add])

def n1845 (b : ℝ) : ℝ := (n1827 b) * (n310 b)
def i1845 : RationalInterval := ⟨(889397513190991658707329313863 / 1000000000000000000000000000000 : ℚ), (44469875838201363594963076349 / 50000000000000000000000000000 : ℚ)⟩
theorem b1845 (b : ℝ) (hb : rootInterval.Contains b) : i1845.Contains (n1845 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1827 b hb) (b310 b hb))
    (by norm_num [i1845, i1827, i310, RationalInterval.mul]) (by norm_num [i1845, i1827, i310, RationalInterval.mul])

def n1846 (b : ℝ) : ℝ := (n1827 b) * (n311 b)
def i1846 : RationalInterval := ⟨(515142391166463157963027687871 / 1000000000000000000000000000000 : ℚ), (515142393382214924404568845947 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1846 (b : ℝ) (hb : rootInterval.Contains b) : i1846.Contains (n1846 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1827 b hb) (b311 b hb))
    (by norm_num [i1846, i1827, i311, RationalInterval.mul]) (by norm_num [i1846, i1827, i311, RationalInterval.mul])

def n1847 (b : ℝ) : ℝ := (n1828 b) * (n310 b)
def i1847 : RationalInterval := ⟨(-16903358931100279854083089599 / 500000000000000000000000000000 : ℚ), (-16903358358368610651581683271 / 500000000000000000000000000000 : ℚ)⟩
theorem b1847 (b : ℝ) (hb : rootInterval.Contains b) : i1847.Contains (n1847 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1828 b hb) (b310 b hb))
    (by norm_num [i1847, i1828, i310, RationalInterval.mul]) (by norm_num [i1847, i1828, i310, RationalInterval.mul])

def n1848 (b : ℝ) : ℝ := (n1828 b) * (n311 b)
def i1848 : RationalInterval := ⟨(-9790489192782314443202431713 / 500000000000000000000000000000 : ℚ), (-76488194205271076230239893 / 3906250000000000000000000000 : ℚ)⟩
theorem b1848 (b : ℝ) (hb : rootInterval.Contains b) : i1848.Contains (n1848 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1828 b hb) (b311 b hb))
    (by norm_num [i1848, i1828, i311, RationalInterval.mul]) (by norm_num [i1848, i1828, i311, RationalInterval.mul])

def n1849 (b : ℝ) : ℝ := (n1501 b) * (n324 b)
def i1849 : RationalInterval := ⟨(-4608479173042898571606516001 / 125000000000000000000000000000 : ℚ), (-9216958229799742451352152441 / 250000000000000000000000000000 : ℚ)⟩
theorem b1849 (b : ℝ) (hb : rootInterval.Contains b) : i1849.Contains (n1849 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1501 b hb) (b324 b hb))
    (by norm_num [i1849, i1501, i324, RationalInterval.mul]) (by norm_num [i1849, i1501, i324, RationalInterval.mul])

def n1850 (b : ℝ) : ℝ := (n1504 b) * (n324 b)
def i1850 : RationalInterval := ⟨(-28879020542219458007574378129 / 1000000000000000000000000000000 : ℚ), (-14439510100106222959817174313 / 500000000000000000000000000000 : ℚ)⟩
theorem b1850 (b : ℝ) (hb : rootInterval.Contains b) : i1850.Contains (n1850 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1504 b hb) (b324 b hb))
    (by norm_num [i1850, i1504, i324, RationalInterval.mul]) (by norm_num [i1850, i1504, i324, RationalInterval.mul])

def n1851 (b : ℝ) : ℝ := (n1845 b) + (n1849 b)
def i1851 : RationalInterval := ⟨(170505935961329694026895437171 / 200000000000000000000000000000 : ℚ), (26641552620150884440432903663 / 31250000000000000000000000000 : ℚ)⟩
theorem b1851 (b : ℝ) (hb : rootInterval.Contains b) : i1851.Contains (n1851 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1845 b hb) (b1849 b hb))
    (by norm_num [i1851, i1845, i1849, RationalInterval.add]) (by norm_num [i1851, i1845, i1849, RationalInterval.add])

def n1852 (b : ℝ) : ℝ := (n1846 b) + (n1758 b)
def i1852 : RationalInterval := ⟨(98846585455000707431927514771 / 100000000000000000000000000000 : ℚ), (494232929819074117658137840063 / 500000000000000000000000000000 : ℚ)⟩
theorem b1852 (b : ℝ) (hb : rootInterval.Contains b) : i1852.Contains (n1852 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1846 b hb) (b1758 b hb))
    (by norm_num [i1852, i1846, i1758, RationalInterval.add]) (by norm_num [i1852, i1846, i1758, RationalInterval.add])

def n1853 (b : ℝ) : ℝ := (n1847 b) + (n1850 b)
def i1853 : RationalInterval := ⟨(-62685738404420017715740557327 / 1000000000000000000000000000000 : ℚ), (-1958929278654677100712428599 / 31250000000000000000000000000 : ℚ)⟩
theorem b1853 (b : ℝ) (hb : rootInterval.Contains b) : i1853.Contains (n1853 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1847 b hb) (b1850 b hb))
    (by norm_num [i1853, i1847, i1850, RationalInterval.add]) (by norm_num [i1853, i1847, i1850, RationalInterval.add])

def n1854 (b : ℝ) : ℝ := (n1848 b) + (n1759 b)
def i1854 : RationalInterval := ⟨(10974344533239572820549438179 / 31250000000000000000000000000 : ℚ), (351179027695771254429001557339 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1854 (b : ℝ) (hb : rootInterval.Contains b) : i1854.Contains (n1854 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1848 b hb) (b1759 b hb))
    (by norm_num [i1854, i1848, i1759, RationalInterval.add]) (by norm_num [i1854, i1848, i1759, RationalInterval.add])

def n1855 (b : ℝ) : ℝ := (n324 b) * (n1501 b)
def i1855 : RationalInterval := ⟨(-4608479173042898571606516001 / 125000000000000000000000000000 : ℚ), (-9216958229799742451352152441 / 250000000000000000000000000000 : ℚ)⟩
theorem b1855 (b : ℝ) (hb : rootInterval.Contains b) : i1855.Contains (n1855 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b324 b hb) (b1501 b hb))
    (by norm_num [i1855, i324, i1501, RationalInterval.mul]) (by norm_num [i1855, i324, i1501, RationalInterval.mul])

def n1856 (b : ℝ) : ℝ := (n324 b) * (n1504 b)
def i1856 : RationalInterval := ⟨(-28879020542219458007574378129 / 1000000000000000000000000000000 : ℚ), (-14439510100106222959817174313 / 500000000000000000000000000000 : ℚ)⟩
theorem b1856 (b : ℝ) (hb : rootInterval.Contains b) : i1856.Contains (n1856 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b324 b hb) (b1504 b hb))
    (by norm_num [i1856, i324, i1504, RationalInterval.mul]) (by norm_num [i1856, i324, i1504, RationalInterval.mul])

def n1857 (b : ℝ) : ℝ := (n310 b) * (n1827 b)
def i1857 : RationalInterval := ⟨(889397513190991658707329313863 / 1000000000000000000000000000000 : ℚ), (44469875838201363594963076349 / 50000000000000000000000000000 : ℚ)⟩
theorem b1857 (b : ℝ) (hb : rootInterval.Contains b) : i1857.Contains (n1857 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b310 b hb) (b1827 b hb))
    (by norm_num [i1857, i310, i1827, RationalInterval.mul]) (by norm_num [i1857, i310, i1827, RationalInterval.mul])

def n1858 (b : ℝ) : ℝ := (n310 b) * (n1828 b)
def i1858 : RationalInterval := ⟨(-16903358931100279854083089599 / 500000000000000000000000000000 : ℚ), (-16903358358368610651581683271 / 500000000000000000000000000000 : ℚ)⟩
theorem b1858 (b : ℝ) (hb : rootInterval.Contains b) : i1858.Contains (n1858 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b310 b hb) (b1828 b hb))
    (by norm_num [i1858, i310, i1828, RationalInterval.mul]) (by norm_num [i1858, i310, i1828, RationalInterval.mul])

def n1859 (b : ℝ) : ℝ := (n311 b) * (n1827 b)
def i1859 : RationalInterval := ⟨(515142391166463157963027687871 / 1000000000000000000000000000000 : ℚ), (515142393382214924404568845947 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1859 (b : ℝ) (hb : rootInterval.Contains b) : i1859.Contains (n1859 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b311 b hb) (b1827 b hb))
    (by norm_num [i1859, i311, i1827, RationalInterval.mul]) (by norm_num [i1859, i311, i1827, RationalInterval.mul])

def n1860 (b : ℝ) : ℝ := (n311 b) * (n1828 b)
def i1860 : RationalInterval := ⟨(-9790489192782314443202431713 / 500000000000000000000000000000 : ℚ), (-76488194205271076230239893 / 3906250000000000000000000000 : ℚ)⟩
theorem b1860 (b : ℝ) (hb : rootInterval.Contains b) : i1860.Contains (n1860 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b311 b hb) (b1828 b hb))
    (by norm_num [i1860, i311, i1828, RationalInterval.mul]) (by norm_num [i1860, i311, i1828, RationalInterval.mul])

def n1861 (b : ℝ) : ℝ := (n1855 b) + (n1857 b)
def i1861 : RationalInterval := ⟨(170505935961329694026895437171 / 200000000000000000000000000000 : ℚ), (26641552620150884440432903663 / 31250000000000000000000000000 : ℚ)⟩
theorem b1861 (b : ℝ) (hb : rootInterval.Contains b) : i1861.Contains (n1861 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1855 b hb) (b1857 b hb))
    (by norm_num [i1861, i1855, i1857, RationalInterval.add]) (by norm_num [i1861, i1855, i1857, RationalInterval.add])

def n1862 (b : ℝ) : ℝ := (n1856 b) + (n1858 b)
def i1862 : RationalInterval := ⟨(-62685738404420017715740557327 / 1000000000000000000000000000000 : ℚ), (-1958929278654677100712428599 / 31250000000000000000000000000 : ℚ)⟩
theorem b1862 (b : ℝ) (hb : rootInterval.Contains b) : i1862.Contains (n1862 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1856 b hb) (b1858 b hb))
    (by norm_num [i1862, i1856, i1858, RationalInterval.add]) (by norm_num [i1862, i1856, i1858, RationalInterval.add])

def n1863 (b : ℝ) : ℝ := (n1762 b) + (n1859 b)
def i1863 : RationalInterval := ⟨(98846585455000707431927514771 / 100000000000000000000000000000 : ℚ), (494232929819074117658137840063 / 500000000000000000000000000000 : ℚ)⟩
theorem b1863 (b : ℝ) (hb : rootInterval.Contains b) : i1863.Contains (n1863 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1762 b hb) (b1859 b hb))
    (by norm_num [i1863, i1762, i1859, RationalInterval.add]) (by norm_num [i1863, i1762, i1859, RationalInterval.add])

def n1864 (b : ℝ) : ℝ := (n1763 b) + (n1860 b)
def i1864 : RationalInterval := ⟨(10974344533239572820549438179 / 31250000000000000000000000000 : ℚ), (351179027695771254429001557339 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1864 (b : ℝ) (hb : rootInterval.Contains b) : i1864.Contains (n1864 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1763 b hb) (b1860 b hb))
    (by norm_num [i1864, i1763, i1860, RationalInterval.add]) (by norm_num [i1864, i1763, i1860, RationalInterval.add])

def n1865 (b : ℝ) : ℝ := (n1851 b) + (n1861 b)
def i1865 : RationalInterval := ⟨(170505935961329694026895437171 / 100000000000000000000000000000 : ℚ), (26641552620150884440432903663 / 15625000000000000000000000000 : ℚ)⟩
theorem b1865 (b : ℝ) (hb : rootInterval.Contains b) : i1865.Contains (n1865 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1851 b hb) (b1861 b hb))
    (by norm_num [i1865, i1851, i1861, RationalInterval.add]) (by norm_num [i1865, i1851, i1861, RationalInterval.add])

def n1866 (b : ℝ) : ℝ := (n1852 b) + (n1862 b)
def i1866 : RationalInterval := ⟨(925780116145587056603534590383 / 1000000000000000000000000000000 : ℚ), (462890061360599284046738982479 / 500000000000000000000000000000 : ℚ)⟩
theorem b1866 (b : ℝ) (hb : rootInterval.Contains b) : i1866.Contains (n1866 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1852 b hb) (b1862 b hb))
    (by norm_num [i1866, i1852, i1862, RationalInterval.add]) (by norm_num [i1866, i1852, i1862, RationalInterval.add])

def n1867 (b : ℝ) : ℝ := (n1853 b) + (n1863 b)
def i1867 : RationalInterval := ⟨(925780116145587056603534590383 / 1000000000000000000000000000000 : ℚ), (462890061360599284046738982479 / 500000000000000000000000000000 : ℚ)⟩
theorem b1867 (b : ℝ) (hb : rootInterval.Contains b) : i1867.Contains (n1867 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1853 b hb) (b1863 b hb))
    (by norm_num [i1867, i1853, i1863, RationalInterval.add]) (by norm_num [i1867, i1853, i1863, RationalInterval.add])

def n1868 (b : ℝ) : ℝ := (n1854 b) + (n1864 b)
def i1868 : RationalInterval := ⟨(10974344533239572820549438179 / 15625000000000000000000000000 : ℚ), (351179027695771254429001557339 / 500000000000000000000000000000 : ℚ)⟩
theorem b1868 (b : ℝ) (hb : rootInterval.Contains b) : i1868.Contains (n1868 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1854 b hb) (b1864 b hb))
    (by norm_num [i1868, i1854, i1864, RationalInterval.add]) (by norm_num [i1868, i1854, i1864, RationalInterval.add])

def n1869 (b : ℝ) : ℝ := (n1575 b) * (n1865 b)
def i1869 : RationalInterval := ⟨(-3836383588026308510489093437903 / 1000000000000000000000000000000 : ℚ), (-3836383548334931854938279246947 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1869 (b : ℝ) (hb : rootInterval.Contains b) : i1869.Contains (n1869 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1575 b hb) (b1865 b hb))
    (by norm_num [i1869, i1575, i1865, RationalInterval.mul]) (by norm_num [i1869, i1575, i1865, RationalInterval.mul])

def n1870 (b : ℝ) : ℝ := (n1575 b) * (n1866 b)
def i1870 : RationalInterval := ⟨(-2083005281945722206129132771557 / 1000000000000000000000000000000 : ℚ), (-520751313866579565013771069903 / 250000000000000000000000000000 : ℚ)⟩
theorem b1870 (b : ℝ) (hb : rootInterval.Contains b) : i1870.Contains (n1870 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1575 b hb) (b1866 b hb))
    (by norm_num [i1870, i1575, i1866, RationalInterval.mul]) (by norm_num [i1870, i1575, i1866, RationalInterval.mul])

def n1871 (b : ℝ) : ℝ := (n1575 b) * (n1867 b)
def i1871 : RationalInterval := ⟨(-2083005281945722206129132771557 / 1000000000000000000000000000000 : ℚ), (-520751313866579565013771069903 / 250000000000000000000000000000 : ℚ)⟩
theorem b1871 (b : ℝ) (hb : rootInterval.Contains b) : i1871.Contains (n1871 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1575 b hb) (b1867 b hb))
    (by norm_num [i1871, i1575, i1867, RationalInterval.mul]) (by norm_num [i1871, i1575, i1867, RationalInterval.mul])

def n1872 (b : ℝ) : ℝ := (n1575 b) * (n1868 b)
def i1872 : RationalInterval := ⟨(-1580305629048703015363165697107 / 1000000000000000000000000000000 : ℚ), (-1580305608339764442299852431397 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1872 (b : ℝ) (hb : rootInterval.Contains b) : i1872.Contains (n1872 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1575 b hb) (b1868 b hb))
    (by norm_num [i1872, i1575, i1868, RationalInterval.mul]) (by norm_num [i1872, i1575, i1868, RationalInterval.mul])

def n1873 (b : ℝ) : ℝ := (n1870 b) + (n15 b)
def i1873 : RationalInterval := ⟨(-1083005281945722206129132771557 / 1000000000000000000000000000000 : ℚ), (-270751313866579565013771069903 / 250000000000000000000000000000 : ℚ)⟩
theorem b1873 (b : ℝ) (hb : rootInterval.Contains b) : i1873.Contains (n1873 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1870 b hb) (b15 b hb))
    (by norm_num [i1873, i1870, i15, RationalInterval.add]) (by norm_num [i1873, i1870, i15, RationalInterval.add])

def n1874 (b : ℝ) : ℝ := (n1871 b) + (n15 b)
def i1874 : RationalInterval := ⟨(-1083005281945722206129132771557 / 1000000000000000000000000000000 : ℚ), (-270751313866579565013771069903 / 250000000000000000000000000000 : ℚ)⟩
theorem b1874 (b : ℝ) (hb : rootInterval.Contains b) : i1874.Contains (n1874 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1871 b hb) (b15 b hb))
    (by norm_num [i1874, i1871, i15, RationalInterval.add]) (by norm_num [i1874, i1871, i15, RationalInterval.add])

def n1875 (b : ℝ) : ℝ := (n1820 b) * (n1581 b)
def i1875 : RationalInterval := ⟨(1057254305277378880063397301619 / 200000000000000000000000000000 : ℚ), (528627159713374484933454246199 / 100000000000000000000000000000 : ℚ)⟩
theorem b1875 (b : ℝ) (hb : rootInterval.Contains b) : i1875.Contains (n1875 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1820 b hb) (b1581 b hb))
    (by norm_num [i1875, i1820, i1581, RationalInterval.mul]) (by norm_num [i1875, i1820, i1581, RationalInterval.mul])

def n1876 (b : ℝ) : ℝ := (n1875 b) * (n1516 b)
def i1876 : RationalInterval := ⟨(4274968279030513486982927663449 / 1000000000000000000000000000000 : ℚ), (4274968370336640756660161784009 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1876 (b : ℝ) (hb : rootInterval.Contains b) : i1876.Contains (n1876 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1875 b hb) (b1516 b hb))
    (by norm_num [i1876, i1875, i1516, RationalInterval.mul]) (by norm_num [i1876, i1875, i1516, RationalInterval.mul])

def n1877 (b : ℝ) : ℝ := (n1875 b) * (n1517 b)
def i1877 : RationalInterval := ⟨(364044511452601386480681120291 / 125000000000000000000000000000 : ℚ), (2912356152879725871151209696959 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1877 (b : ℝ) (hb : rootInterval.Contains b) : i1877.Contains (n1877 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1875 b hb) (b1517 b hb))
    (by norm_num [i1877, i1875, i1517, RationalInterval.mul]) (by norm_num [i1877, i1875, i1517, RationalInterval.mul])

def n1878 (b : ℝ) : ℝ := (n1875 b) * (n1518 b)
def i1878 : RationalInterval := ⟨(364044511452601386480681120291 / 125000000000000000000000000000 : ℚ), (2912356152879725871151209696959 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1878 (b : ℝ) (hb : rootInterval.Contains b) : i1878.Contains (n1878 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1875 b hb) (b1518 b hb))
    (by norm_num [i1878, i1875, i1518, RationalInterval.mul]) (by norm_num [i1878, i1875, i1518, RationalInterval.mul])

def n1879 (b : ℝ) : ℝ := (n1875 b) * (n1519 b)
def i1879 : RationalInterval := ⟨(969770845088245155366939076797 / 500000000000000000000000000000 : ℚ), (1939541730651639828056289649963 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1879 (b : ℝ) (hb : rootInterval.Contains b) : i1879.Contains (n1879 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1875 b hb) (b1519 b hb))
    (by norm_num [i1879, i1875, i1519, RationalInterval.mul]) (by norm_num [i1879, i1875, i1519, RationalInterval.mul])

def n1880 (b : ℝ) : ℝ := (n1869 b) + (n1876 b)
def i1880 : RationalInterval := ⟨(219292345502102488246917112773 / 500000000000000000000000000000 : ℚ), (219292411000854450860941268531 / 500000000000000000000000000000 : ℚ)⟩
theorem b1880 (b : ℝ) (hb : rootInterval.Contains b) : i1880.Contains (n1880 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1869 b hb) (b1876 b hb))
    (by norm_num [i1880, i1869, i1876, RationalInterval.add]) (by norm_num [i1880, i1869, i1876, RationalInterval.add])

def n1881 (b : ℝ) : ℝ := (n1873 b) + (n1877 b)
def i1881 : RationalInterval := ⟨(1829350809675088885716316190771 / 1000000000000000000000000000000 : ℚ), (1829350897413407611096125417347 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1881 (b : ℝ) (hb : rootInterval.Contains b) : i1881.Contains (n1881 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1873 b hb) (b1877 b hb))
    (by norm_num [i1881, i1873, i1877, RationalInterval.add]) (by norm_num [i1881, i1873, i1877, RationalInterval.add])

def n1882 (b : ℝ) : ℝ := (n1874 b) + (n1878 b)
def i1882 : RationalInterval := ⟨(1829350809675088885716316190771 / 1000000000000000000000000000000 : ℚ), (1829350897413407611096125417347 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1882 (b : ℝ) (hb : rootInterval.Contains b) : i1882.Contains (n1882 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1874 b hb) (b1878 b hb))
    (by norm_num [i1882, i1874, i1878, RationalInterval.add]) (by norm_num [i1882, i1874, i1878, RationalInterval.add])

def n1883 (b : ℝ) : ℝ := (n1872 b) + (n1879 b)
def i1883 : RationalInterval := ⟨(359236061127787295370712456487 / 1000000000000000000000000000000 : ℚ), (179618061155937692878218609283 / 500000000000000000000000000000 : ℚ)⟩
theorem b1883 (b : ℝ) (hb : rootInterval.Contains b) : i1883.Contains (n1883 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1872 b hb) (b1879 b hb))
    (by norm_num [i1883, i1872, i1879, RationalInterval.add]) (by norm_num [i1883, i1872, i1879, RationalInterval.add])

def n1884 (b : ℝ) : ℝ := (n1820 b) + (n1836 b)
def i1884 : RationalInterval := ⟨(483552662834594923605528993737 / 500000000000000000000000000000 : ℚ), (193421066079230907733525405037 / 200000000000000000000000000000 : ℚ)⟩
theorem b1884 (b : ℝ) (hb : rootInterval.Contains b) : i1884.Contains (n1884 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1820 b hb) (b1836 b hb))
    (by norm_num [i1884, i1820, i1836, RationalInterval.add]) (by norm_num [i1884, i1820, i1836, RationalInterval.add])

def n1885 (b : ℝ) : ℝ := (n1884 b) * (n1581 b)
def i1885 : RationalInterval := ⟨(2447985341823637222159637095599 / 500000000000000000000000000000 : ℚ), (2447985381251915197807871016177 / 500000000000000000000000000000 : ℚ)⟩
theorem b1885 (b : ℝ) (hb : rootInterval.Contains b) : i1885.Contains (n1885 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1884 b hb) (b1581 b hb))
    (by norm_num [i1885, i1884, i1581, RationalInterval.mul]) (by norm_num [i1885, i1884, i1581, RationalInterval.mul])

def n1886 (b : ℝ) : ℝ := (n1594 b) * (n1820 b)
def i1886 : RationalInterval := ⟨(198271317404952683371221966049 / 125000000000000000000000000000 : ℚ), (39654263826945700961914999191 / 25000000000000000000000000000 : ℚ)⟩
theorem b1886 (b : ℝ) (hb : rootInterval.Contains b) : i1886.Contains (n1886 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1594 b hb) (b1820 b hb))
    (by norm_num [i1886, i1594, i1820, RationalInterval.mul]) (by norm_num [i1886, i1594, i1820, RationalInterval.mul])

def n1887 (b : ℝ) : ℝ := (n1886 b) * (n1597 b)
def i1887 : RationalInterval := ⟨(18067473646009135676323179527541 / 1000000000000000000000000000000 : ℚ), (18067474107674594062720616165407 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1887 (b : ℝ) (hb : rootInterval.Contains b) : i1887.Contains (n1887 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1886 b hb) (b1597 b hb))
    (by norm_num [i1887, i1886, i1597, RationalInterval.mul]) (by norm_num [i1887, i1886, i1597, RationalInterval.mul])

def n1888 (b : ℝ) : ℝ := -(n1887 b)
def i1888 : RationalInterval := ⟨(-18067474107674594062720616165407 / 1000000000000000000000000000000 : ℚ), (-18067473646009135676323179527541 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1888 (b : ℝ) (hb : rootInterval.Contains b) : i1888.Contains (n1888 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b1887 b hb))
    (by norm_num [i1888, i1887, RationalInterval.neg]) (by norm_num [i1888, i1887, RationalInterval.neg])

def n1889 (b : ℝ) : ℝ := (n1885 b) + (n1888 b)
def i1889 : RationalInterval := ⟨(-13171503424027319618401341974209 / 1000000000000000000000000000000 : ℚ), (-13171502883505305280707437495187 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1889 (b : ℝ) (hb : rootInterval.Contains b) : i1889.Contains (n1889 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1885 b hb) (b1888 b hb))
    (by norm_num [i1889, i1885, i1888, RationalInterval.add]) (by norm_num [i1889, i1885, i1888, RationalInterval.add])

