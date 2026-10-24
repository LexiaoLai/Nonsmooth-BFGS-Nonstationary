import BFGS.Counterexample.Certificates.IntervalTrace23

/-! Generated arithmetic proofs. Each bound is checked by the Lean kernel. -/
namespace BFGS.Counterexample.Trace
noncomputable section
open BFGS RationalInterval
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false

def n2160 (b : ℝ) : ℝ := (n1905 b) * (n1423 b)
def i2160 : RationalInterval := ⟨(-11026585592008545758282523511423 / 1000000000000000000000000000000 : ℚ), (-11026580005541924304236463505191 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2160 (b : ℝ) (hb : rootInterval.Contains b) : i2160.Contains (n2160 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1905 b hb) (b1423 b hb))
    (by norm_num [i2160, i1905, i1423, RationalInterval.mul]) (by norm_num [i2160, i1905, i1423, RationalInterval.mul])

def n2161 (b : ℝ) : ℝ := (n2159 b) + (n2160 b)
def i2161 : RationalInterval := ⟨(-27641118679665173619654764110387 / 1000000000000000000000000000000 : ℚ), (-6910274186936263462597690005973 / 250000000000000000000000000000 : ℚ)⟩
theorem b2161 (b : ℝ) (hb : rootInterval.Contains b) : i2161.Contains (n2161 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2159 b hb) (b2160 b hb))
    (by norm_num [i2161, i2159, i2160, RationalInterval.add]) (by norm_num [i2161, i2159, i2160, RationalInterval.add])

def n2162 (b : ℝ) : ℝ := (n1976 b) * (n1460 b)
def i2162 : RationalInterval := ⟨(466703155004964940107865885481 / 1000000000000000000000000000000 : ℚ), (23335188096224921899015357671 / 50000000000000000000000000000 : ℚ)⟩
theorem b2162 (b : ℝ) (hb : rootInterval.Contains b) : i2162.Contains (n2162 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1976 b hb) (b1460 b hb))
    (by norm_num [i2162, i1976, i1460, RationalInterval.mul]) (by norm_num [i2162, i1976, i1460, RationalInterval.mul])

def n2163 (b : ℝ) : ℝ := (n2161 b) + (n2162 b)
def i2163 : RationalInterval := ⟨(-13587207762330104339773449112453 / 500000000000000000000000000000 : ℚ), (-3396799123227569426551306608809 / 125000000000000000000000000000 : ℚ)⟩
theorem b2163 (b : ℝ) (hb : rootInterval.Contains b) : i2163.Contains (n2163 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2161 b hb) (b2162 b hb))
    (by norm_num [i2163, i2161, i2162, RationalInterval.add]) (by norm_num [i2163, i2161, i2162, RationalInterval.add])

def n2164 (b : ℝ) : ℝ := (n1617 b) * (n1344 b)
def i2164 : RationalInterval := ⟨(873231880681847598267822409909 / 250000000000000000000000000000 : ℚ), (6822128892882573448810024043 / 1953125000000000000000000000 : ℚ)⟩
theorem b2164 (b : ℝ) (hb : rootInterval.Contains b) : i2164.Contains (n2164 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1617 b hb) (b1344 b hb))
    (by norm_num [i2164, i1617, i1344, RationalInterval.mul]) (by norm_num [i2164, i1617, i1344, RationalInterval.mul])

def n2165 (b : ℝ) : ℝ := (n1728 b) * (n1361 b)
def i2165 : RationalInterval := ⟨(7143365855993113831096874122069 / 1000000000000000000000000000000 : ℚ), (1785842861684075864509669297859 / 250000000000000000000000000000 : ℚ)⟩
theorem b2165 (b : ℝ) (hb : rootInterval.Contains b) : i2165.Contains (n2165 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1728 b hb) (b1361 b hb))
    (by norm_num [i2165, i1728, i1361, RationalInterval.mul]) (by norm_num [i2165, i1728, i1361, RationalInterval.mul])

def n2166 (b : ℝ) : ℝ := (n2164 b) + (n2165 b)
def i2166 : RationalInterval := ⟨(2127258675744100844833632752341 / 200000000000000000000000000000 : ℚ), (2659075359973045265957352375363 / 250000000000000000000000000000 : ℚ)⟩
theorem b2166 (b : ℝ) (hb : rootInterval.Contains b) : i2166.Contains (n2166 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2164 b hb) (b2165 b hb))
    (by norm_num [i2166, i2164, i2165, RationalInterval.add]) (by norm_num [i2166, i2164, i2165, RationalInterval.add])

def n2167 (b : ℝ) : ℝ := (n1801 b) * (n1393 b)
def i2167 : RationalInterval := ⟨(-394103781263224999256296252533 / 250000000000000000000000000000 : ℚ), (-1576414320906711566163461832317 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2167 (b : ℝ) (hb : rootInterval.Contains b) : i2167.Contains (n2167 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1801 b hb) (b1393 b hb))
    (by norm_num [i2167, i1801, i1393, RationalInterval.mul]) (by norm_num [i2167, i1801, i1393, RationalInterval.mul])

def n2168 (b : ℝ) : ℝ := (n2166 b) + (n2167 b)
def i2168 : RationalInterval := ⟨(9059878253667604227142978751573 / 1000000000000000000000000000000 : ℚ), (1811977423797093899533189533827 / 200000000000000000000000000000 : ℚ)⟩
theorem b2168 (b : ℝ) (hb : rootInterval.Contains b) : i2168.Contains (n2168 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2166 b hb) (b2167 b hb))
    (by norm_num [i2168, i2166, i2167, RationalInterval.add]) (by norm_num [i2168, i2166, i2167, RationalInterval.add])

def n2169 (b : ℝ) : ℝ := (n1905 b) * (n1430 b)
def i2169 : RationalInterval := ⟨(5895638050485842727146695670099 / 1000000000000000000000000000000 : ℚ), (1473910266425213026395737543353 / 250000000000000000000000000000 : ℚ)⟩
theorem b2169 (b : ℝ) (hb : rootInterval.Contains b) : i2169.Contains (n2169 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1905 b hb) (b1430 b hb))
    (by norm_num [i2169, i1905, i1430, RationalInterval.mul]) (by norm_num [i2169, i1905, i1430, RationalInterval.mul])

def n2170 (b : ℝ) : ℝ := (n2168 b) + (n2169 b)
def i2170 : RationalInterval := ⟨(1869439538019180869286209302709 / 125000000000000000000000000000 : ℚ), (14955528184686321603248897842547 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2170 (b : ℝ) (hb : rootInterval.Contains b) : i2170.Contains (n2170 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2168 b hb) (b2169 b hb))
    (by norm_num [i2170, i2168, i2169, RationalInterval.add]) (by norm_num [i2170, i2168, i2169, RationalInterval.add])

def n2171 (b : ℝ) : ℝ := (n1976 b) * (n1467 b)
def i2171 : RationalInterval := ⟨(-1651597911375868542144485597 / 7812500000000000000000000000 : ℚ), (-211404249378042682706540709199 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2171 (b : ℝ) (hb : rootInterval.Contains b) : i2171.Contains (n2171 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1976 b hb) (b1467 b hb))
    (by norm_num [i2171, i1976, i1467, RationalInterval.mul]) (by norm_num [i2171, i1976, i1467, RationalInterval.mul])

def n2172 (b : ℝ) : ℝ := (n2170 b) + (n2171 b)
def i2172 : RationalInterval := ⟨(1843013971437166972611897533157 / 125000000000000000000000000000 : ℚ), (3686030983827069730135589283337 / 250000000000000000000000000000 : ℚ)⟩
theorem b2172 (b : ℝ) (hb : rootInterval.Contains b) : i2172.Contains (n2172 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2170 b hb) (b2171 b hb))
    (by norm_num [i2172, i2170, i2171, RationalInterval.add]) (by norm_num [i2172, i2170, i2171, RationalInterval.add])

def n2173 (b : ℝ) : ℝ := (n1617 b) * (n1345 b)
def i2173 : RationalInterval := ⟨(199196872462306482943492080527 / 50000000000000000000000000000 : ℚ), (995985062289356261365877489829 / 250000000000000000000000000000 : ℚ)⟩
theorem b2173 (b : ℝ) (hb : rootInterval.Contains b) : i2173.Contains (n2173 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1617 b hb) (b1345 b hb))
    (by norm_num [i2173, i1617, i1345, RationalInterval.mul]) (by norm_num [i2173, i1617, i1345, RationalInterval.mul])

def n2174 (b : ℝ) : ℝ := (n1728 b) * (n1345 b)
def i2174 : RationalInterval := ⟨(32955290907502289773313423597 / 3125000000000000000000000000 : ℚ), (1318212664142030633825396153557 / 125000000000000000000000000000 : ℚ)⟩
theorem b2174 (b : ℝ) (hb : rootInterval.Contains b) : i2174.Contains (n2174 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1728 b hb) (b1345 b hb))
    (by norm_num [i2174, i1728, i1345, RationalInterval.mul]) (by norm_num [i2174, i1728, i1345, RationalInterval.mul])

def n2175 (b : ℝ) : ℝ := (n2173 b) + (n2174 b)
def i2175 : RationalInterval := ⟨(726481526982343119316506858079 / 50000000000000000000000000000 : ℚ), (3632410390573417529016669796943 / 250000000000000000000000000000 : ℚ)⟩
theorem b2175 (b : ℝ) (hb : rootInterval.Contains b) : i2175.Contains (n2175 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2173 b hb) (b2174 b hb))
    (by norm_num [i2175, i2173, i2174, RationalInterval.add]) (by norm_num [i2175, i2173, i2174, RationalInterval.add])

def n2176 (b : ℝ) : ℝ := (n1801 b) * (n1398 b)
def i2176 : RationalInterval := ⟨(-2105699362482412108372338298219 / 1000000000000000000000000000000 : ℚ), (-2105698322065316393294334040977 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2176 (b : ℝ) (hb : rootInterval.Contains b) : i2176.Contains (n2176 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1801 b hb) (b1398 b hb))
    (by norm_num [i2176, i1801, i1398, RationalInterval.mul]) (by norm_num [i2176, i1801, i1398, RationalInterval.mul])

def n2177 (b : ℝ) : ℝ := (n2175 b) + (n2176 b)
def i2177 : RationalInterval := ⟨(12423931177164450277957798863361 / 1000000000000000000000000000000 : ℚ), (2484788648045670744554469029359 / 200000000000000000000000000000 : ℚ)⟩
theorem b2177 (b : ℝ) (hb : rootInterval.Contains b) : i2177.Contains (n2177 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2175 b hb) (b2176 b hb))
    (by norm_num [i2177, i2175, i2176, RationalInterval.add]) (by norm_num [i2177, i2175, i2176, RationalInterval.add])

def n2178 (b : ℝ) : ℝ := (n1905 b) * (n1435 b)
def i2178 : RationalInterval := ⟨(2039827986490412928385933311049 / 250000000000000000000000000000 : ℚ), (509957246695180276032648070757 / 62500000000000000000000000000 : ℚ)⟩
theorem b2178 (b : ℝ) (hb : rootInterval.Contains b) : i2178.Contains (n2178 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1905 b hb) (b1435 b hb))
    (by norm_num [i2178, i1905, i1435, RationalInterval.mul]) (by norm_num [i2178, i1905, i1435, RationalInterval.mul])

def n2179 (b : ℝ) : ℝ := (n2177 b) + (n2178 b)
def i2179 : RationalInterval := ⟨(20583243123126101991501532107557 / 1000000000000000000000000000000 : ℚ), (20583259187351238139294714278907 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2179 (b : ℝ) (hb : rootInterval.Contains b) : i2179.Contains (n2179 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2177 b hb) (b2178 b hb))
    (by norm_num [i2179, i2177, i2178, RationalInterval.add]) (by norm_num [i2179, i2177, i2178, RationalInterval.add])

def n2180 (b : ℝ) : ℝ := (n1976 b) * (n1472 b)
def i2180 : RationalInterval := ⟨(-421973295633344088756834567563 / 1000000000000000000000000000000 : ℚ), (-421972767143224362125354919409 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2180 (b : ℝ) (hb : rootInterval.Contains b) : i2180.Contains (n2180 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1976 b hb) (b1472 b hb))
    (by norm_num [i2180, i1976, i1472, RationalInterval.mul]) (by norm_num [i2180, i1976, i1472, RationalInterval.mul])

def n2181 (b : ℝ) : ℝ := (n2179 b) + (n2180 b)
def i2181 : RationalInterval := ⟨(10080634913746378951372348769997 / 500000000000000000000000000000 : ℚ), (10080643210104006888584679679749 / 500000000000000000000000000000 : ℚ)⟩
theorem b2181 (b : ℝ) (hb : rootInterval.Contains b) : i2181.Contains (n2181 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2179 b hb) (b2180 b hb))
    (by norm_num [i2181, i2179, i2180, RationalInterval.add]) (by norm_num [i2181, i2179, i2180, RationalInterval.add])

def n2182 (b : ℝ) : ℝ := (n118 b) * (n224 b)
def i2182 : RationalInterval := ⟨(40151811335838773212922995507 / 100000000000000000000000000000 : ℚ), (200759058146391916017651467809 / 500000000000000000000000000000 : ℚ)⟩
theorem b2182 (b : ℝ) (hb : rootInterval.Contains b) : i2182.Contains (n2182 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b118 b hb) (b224 b hb))
    (by norm_num [i2182, i118, i224, RationalInterval.mul]) (by norm_num [i2182, i118, i224, RationalInterval.mul])

def n2183 (b : ℝ) : ℝ := (n119 b) * (n226 b)
def i2183 : RationalInterval := ⟨(9963459255787942028849857797 / 200000000000000000000000000000 : ℚ), (9963459390971083921986137837 / 200000000000000000000000000000 : ℚ)⟩
theorem b2183 (b : ℝ) (hb : rootInterval.Contains b) : i2183.Contains (n2183 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b119 b hb) (b226 b hb))
    (by norm_num [i2183, i119, i226, RationalInterval.mul]) (by norm_num [i2183, i119, i226, RationalInterval.mul])

def n2184 (b : ℝ) : ℝ := (n2182 b) + (n2183 b)
def i2184 : RationalInterval := ⟨(90267081927465488454695848811 / 200000000000000000000000000000 : ℚ), (451335413247639251645233624803 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2184 (b : ℝ) (hb : rootInterval.Contains b) : i2184.Contains (n2184 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2182 b hb) (b2183 b hb))
    (by norm_num [i2184, i2182, i2183, RationalInterval.add]) (by norm_num [i2184, i2182, i2183, RationalInterval.add])

def n2185 (b : ℝ) : ℝ := (n120 b) * (n224 b)
def i2185 : RationalInterval := ⟨(99513996421925974864231185923 / 500000000000000000000000000000 : ℚ), (99513997188783856349254187381 / 500000000000000000000000000000 : ℚ)⟩
theorem b2185 (b : ℝ) (hb : rootInterval.Contains b) : i2185.Contains (n2185 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b120 b hb) (b224 b hb))
    (by norm_num [i2185, i120, i224, RationalInterval.mul]) (by norm_num [i2185, i120, i224, RationalInterval.mul])

def n2186 (b : ℝ) : ℝ := (n121 b) * (n226 b)
def i2186 : RationalInterval := ⟨(566775022708119323020260271 / 20000000000000000000000000000 : ℚ), (1133550061617942052290496019 / 40000000000000000000000000000 : ℚ)⟩
theorem b2186 (b : ℝ) (hb : rootInterval.Contains b) : i2186.Contains (n2186 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b121 b hb) (b226 b hb))
    (by norm_num [i2186, i121, i226, RationalInterval.mul]) (by norm_num [i2186, i121, i226, RationalInterval.mul])

def n2187 (b : ℝ) : ℝ := (n2185 b) + (n2186 b)
def i2187 : RationalInterval := ⟨(56841685994814478969868846349 / 250000000000000000000000000000 : ℚ), (227366745918016264005770775237 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2187 (b : ℝ) (hb : rootInterval.Contains b) : i2187.Contains (n2187 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2185 b hb) (b2186 b hb))
    (by norm_num [i2187, i2185, i2186, RationalInterval.add]) (by norm_num [i2187, i2185, i2186, RationalInterval.add])

def n2188 (b : ℝ) : ℝ := -(n2184 b)
def i2188 : RationalInterval := ⟨(-451335413247639251645233624803 / 1000000000000000000000000000000 : ℚ), (-90267081927465488454695848811 / 200000000000000000000000000000 : ℚ)⟩
theorem b2188 (b : ℝ) (hb : rootInterval.Contains b) : i2188.Contains (n2188 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b2184 b hb))
    (by norm_num [i2188, i2184, RationalInterval.neg]) (by norm_num [i2188, i2184, RationalInterval.neg])

def n2189 (b : ℝ) : ℝ := -(n2187 b)
def i2189 : RationalInterval := ⟨(-227366745918016264005770775237 / 1000000000000000000000000000000 : ℚ), (-56841685994814478969868846349 / 250000000000000000000000000000 : ℚ)⟩
theorem b2189 (b : ℝ) (hb : rootInterval.Contains b) : i2189.Contains (n2189 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b2187 b hb))
    (by norm_num [i2189, i2187, RationalInterval.neg]) (by norm_num [i2189, i2187, RationalInterval.neg])

def n2190 (b : ℝ) : ℝ := (n2188 b) + (n15 b)
def i2190 : RationalInterval := ⟨(548664586752360748354766375197 / 1000000000000000000000000000000 : ℚ), (109732918072534511545304151189 / 200000000000000000000000000000 : ℚ)⟩
theorem b2190 (b : ℝ) (hb : rootInterval.Contains b) : i2190.Contains (n2190 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2188 b hb) (b15 b hb))
    (by norm_num [i2190, i2188, i15, RationalInterval.add]) (by norm_num [i2190, i2188, i15, RationalInterval.add])

def n2191 (b : ℝ) : ℝ := (n229 b) * (n2190 b)
def i2191 : RationalInterval := ⟨(416980757156700524481914986521 / 500000000000000000000000000000 : ℚ), (416980760154262746448592793653 / 500000000000000000000000000000 : ℚ)⟩
theorem b2191 (b : ℝ) (hb : rootInterval.Contains b) : i2191.Contains (n2191 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b229 b hb) (b2190 b hb))
    (by norm_num [i2191, i229, i2190, RationalInterval.mul]) (by norm_num [i2191, i229, i2190, RationalInterval.mul])

def n2192 (b : ℝ) : ℝ := (n230 b) * (n2189 b)
def i2192 : RationalInterval := ⟨(131830319571357660305201035159 / 500000000000000000000000000000 : ℚ), (131830320803680470683959912163 / 500000000000000000000000000000 : ℚ)⟩
theorem b2192 (b : ℝ) (hb : rootInterval.Contains b) : i2192.Contains (n2192 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b230 b hb) (b2189 b hb))
    (by norm_num [i2192, i230, i2189, RationalInterval.mul]) (by norm_num [i2192, i230, i2189, RationalInterval.mul])

def n2193 (b : ℝ) : ℝ := (n2191 b) + (n2192 b)
def i2193 : RationalInterval := ⟨(6860138459100727309838950271 / 6250000000000000000000000000 : ℚ), (68601385119742902141569088227 / 62500000000000000000000000000 : ℚ)⟩
theorem b2193 (b : ℝ) (hb : rootInterval.Contains b) : i2193.Contains (n2193 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2191 b hb) (b2192 b hb))
    (by norm_num [i2193, i2191, i2192, RationalInterval.add]) (by norm_num [i2193, i2191, i2192, RationalInterval.add])

def n2194 (b : ℝ) : ℝ := (n231 b) * (n2190 b)
def i2194 : RationalInterval := ⟨(-159061582794548111252613371003 / 250000000000000000000000000000 : ℚ), (-636246326469355108945373982167 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2194 (b : ℝ) (hb : rootInterval.Contains b) : i2194.Contains (n2194 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b231 b hb) (b2190 b hb))
    (by norm_num [i2194, i231, i2190, RationalInterval.mul]) (by norm_num [i2194, i231, i2190, RationalInterval.mul])

def n2195 (b : ℝ) : ℝ := (n232 b) * (n2189 b)
def i2195 : RationalInterval := ⟨(-201152105719111744334186933397 / 1000000000000000000000000000000 : ℚ), (-201152103796091482562995351833 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2195 (b : ℝ) (hb : rootInterval.Contains b) : i2195.Contains (n2195 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b232 b hb) (b2189 b hb))
    (by norm_num [i2195, i232, i2189, RationalInterval.mul]) (by norm_num [i2195, i232, i2189, RationalInterval.mul])

def n2196 (b : ℝ) : ℝ := (n2194 b) + (n2195 b)
def i2196 : RationalInterval := ⟨(-837398436897304189344640417409 / 1000000000000000000000000000000 : ℚ), (-418699215132723295754184667 / 500000000000000000000000000 : ℚ)⟩
theorem b2196 (b : ℝ) (hb : rootInterval.Contains b) : i2196.Contains (n2196 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2194 b hb) (b2195 b hb))
    (by norm_num [i2196, i2194, i2195, RationalInterval.add]) (by norm_num [i2196, i2194, i2195, RationalInterval.add])

def n2197 (b : ℝ) : ℝ := -(n224 b)
def i2197 : RationalInterval := ⟨(-94104222665375805166330169407 / 500000000000000000000000000000 : ℚ), (-94104222117613192144445658683 / 500000000000000000000000000000 : ℚ)⟩
theorem b2197 (b : ℝ) (hb : rootInterval.Contains b) : i2197.Contains (n2197 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b224 b hb))
    (by norm_num [i2197, i224, RationalInterval.neg]) (by norm_num [i2197, i224, RationalInterval.neg])

def n2198 (b : ℝ) : ℝ := -(n226 b)
def i2198 : RationalInterval := ⟨(-47109131716218335954434337871 / 1000000000000000000000000000000 : ℚ), (-2944320702957190077038693799 / 62500000000000000000000000000 : ℚ)⟩
theorem b2198 (b : ℝ) (hb : rootInterval.Contains b) : i2198.Contains (n2198 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b226 b hb))
    (by norm_num [i2198, i226, RationalInterval.neg]) (by norm_num [i2198, i226, RationalInterval.neg])

def n2199 (b : ℝ) : ℝ := (n2193 b) + (n2197 b)
def i2199 : RationalInterval := ⟨(454706854062682379620785852273 / 500000000000000000000000000000 : ℚ), (454706858840330024988107047133 / 500000000000000000000000000000 : ℚ)⟩
theorem b2199 (b : ℝ) (hb : rootInterval.Contains b) : i2199.Contains (n2199 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2193 b hb) (b2197 b hb))
    (by norm_num [i2199, i2193, i2197, RationalInterval.add]) (by norm_num [i2199, i2193, i2197, RationalInterval.add])

def n2200 (b : ℝ) : ℝ := (n2196 b) + (n2198 b)
def i2200 : RationalInterval := ⟨(-11056344607669031566238434441 / 12500000000000000000000000000 : ℚ), (-27640861297273801023155888587 / 31250000000000000000000000000 : ℚ)⟩
theorem b2200 (b : ℝ) (hb : rootInterval.Contains b) : i2200.Contains (n2200 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2196 b hb) (b2198 b hb))
    (by norm_num [i2200, i2196, i2198, RationalInterval.add]) (by norm_num [i2200, i2196, i2198, RationalInterval.add])

def n2201 (b : ℝ) : ℝ := (n2188 b) * (n332 b)
def i2201 : RationalInterval := ⟨(-189832732593014295855347536413 / 200000000000000000000000000000 : ℚ), (-474581827613646785244767868737 / 500000000000000000000000000000 : ℚ)⟩
theorem b2201 (b : ℝ) (hb : rootInterval.Contains b) : i2201.Contains (n2201 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2188 b hb) (b332 b hb))
    (by norm_num [i2201, i2188, i332, RationalInterval.mul]) (by norm_num [i2201, i2188, i332, RationalInterval.mul])

def n2202 (b : ℝ) : ℝ := (n2189 b) * (n331 b)
def i2202 : RationalInterval := ⟨(237343556056762450417412006929 / 1000000000000000000000000000000 : ℚ), (118671779082969141575607148357 / 500000000000000000000000000000 : ℚ)⟩
theorem b2202 (b : ℝ) (hb : rootInterval.Contains b) : i2202.Contains (n2202 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2189 b hb) (b331 b hb))
    (by norm_num [i2202, i2189, i331, RationalInterval.mul]) (by norm_num [i2202, i2189, i331, RationalInterval.mul])

def n2203 (b : ℝ) : ℝ := (n2201 b) + (n2202 b)
def i2203 : RationalInterval := ⟨(-5561094585221164287963481837 / 7812500000000000000000000000 : ℚ), (-17795502426533882183458036019 / 25000000000000000000000000000 : ℚ)⟩
theorem b2203 (b : ℝ) (hb : rootInterval.Contains b) : i2203.Contains (n2203 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2201 b hb) (b2202 b hb))
    (by norm_num [i2203, i2201, i2202, RationalInterval.add]) (by norm_num [i2203, i2201, i2202, RationalInterval.add])

def n2204 (b : ℝ) : ℝ := (n318 b) * (n2199 b)
def i2204 : RationalInterval := ⟨(568038862351612472108860336351 / 500000000000000000000000000000 : ℚ), (28401943610923775044440773997 / 25000000000000000000000000000 : ℚ)⟩
theorem b2204 (b : ℝ) (hb : rootInterval.Contains b) : i2204.Contains (n2204 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b318 b hb) (b2199 b hb))
    (by norm_num [i2204, i318, i2199, RationalInterval.mul]) (by norm_num [i2204, i318, i2199, RationalInterval.mul])

def n2205 (b : ℝ) : ℝ := (n319 b) * (n2200 b)
def i2205 : RationalInterval := ⟨(-119069997429097158926601889681 / 250000000000000000000000000000 : ℚ), (-59534997629615165285227375217 / 125000000000000000000000000000 : ℚ)⟩
theorem b2205 (b : ℝ) (hb : rootInterval.Contains b) : i2205.Contains (n2205 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b319 b hb) (b2200 b hb))
    (by norm_num [i2205, i319, i2200, RationalInterval.mul]) (by norm_num [i2205, i319, i2200, RationalInterval.mul])

def n2206 (b : ℝ) : ℝ := (n2204 b) + (n2205 b)
def i2206 : RationalInterval := ⟨(329898867493418154255656556989 / 500000000000000000000000000000 : ℚ), (5154670026562731871061030923 / 7812500000000000000000000000 : ℚ)⟩
theorem b2206 (b : ℝ) (hb : rootInterval.Contains b) : i2206.Contains (n2206 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2204 b hb) (b2205 b hb))
    (by norm_num [i2206, i2204, i2205, RationalInterval.add]) (by norm_num [i2206, i2204, i2205, RationalInterval.add])

def n2207 (b : ℝ) : ℝ := (n2203 b) + (n2206 b)
def i2207 : RationalInterval := ⟨(-26011185960736360174006280579 / 500000000000000000000000000000 : ℚ), (-6502791707665700980313685327 / 125000000000000000000000000000 : ℚ)⟩
theorem b2207 (b : ℝ) (hb : rootInterval.Contains b) : i2207.Contains (n2207 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2203 b hb) (b2206 b hb))
    (by norm_num [i2207, i2203, i2206, RationalInterval.add]) (by norm_num [i2207, i2203, i2206, RationalInterval.add])

def n2208 (b : ℝ) : ℝ := (n118 b) * (n332 b)
def i2208 : RationalInterval := ⟨(112162514921085956305198061267 / 25000000000000000000000000000 : ℚ), (2243250302101714314270155797779 / 500000000000000000000000000000 : ℚ)⟩
theorem b2208 (b : ℝ) (hb : rootInterval.Contains b) : i2208.Contains (n2208 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b118 b hb) (b332 b hb))
    (by norm_num [i2208, i118, i332, RationalInterval.mul]) (by norm_num [i2208, i118, i332, RationalInterval.mul])

def n2209 (b : ℝ) : ℝ := (n119 b) * (n331 b)
def i2209 : RationalInterval := ⟨(-220777879630351291342709418197 / 200000000000000000000000000000 : ℚ), (-1103889393764985359329008226549 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2209 (b : ℝ) (hb : rootInterval.Contains b) : i2209.Contains (n2209 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b119 b hb) (b331 b hb))
    (by norm_num [i2209, i119, i331, RationalInterval.mul]) (by norm_num [i2209, i119, i331, RationalInterval.mul])

def n2210 (b : ℝ) : ℝ := (n2208 b) + (n2209 b)
def i2210 : RationalInterval := ⟨(676522239738336359098875071939 / 200000000000000000000000000000 : ℚ), (3382611210438443269211303369009 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2210 (b : ℝ) (hb : rootInterval.Contains b) : i2210.Contains (n2210 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2208 b hb) (b2209 b hb))
    (by norm_num [i2210, i2208, i2209, RationalInterval.add]) (by norm_num [i2210, i2208, i2209, RationalInterval.add])

def n2211 (b : ℝ) : ℝ := (n120 b) * (n332 b)
def i2211 : RationalInterval := ⟨(2223907661882920102312145959581 / 1000000000000000000000000000000 : ℚ), (2223907666415803590650954813817 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2211 (b : ℝ) (hb : rootInterval.Contains b) : i2211.Contains (n2211 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b120 b hb) (b332 b hb))
    (by norm_num [i2211, i120, i332, RationalInterval.mul]) (by norm_num [i2211, i120, i332, RationalInterval.mul])

def n2212 (b : ℝ) : ℝ := (n121 b) * (n331 b)
def i2212 : RationalInterval := ⟨(-627951520748034972340751293349 / 1000000000000000000000000000000 : ℚ), (-627951517797342275346339988583 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2212 (b : ℝ) (hb : rootInterval.Contains b) : i2212.Contains (n2212 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b121 b hb) (b331 b hb))
    (by norm_num [i2212, i121, i331, RationalInterval.mul]) (by norm_num [i2212, i121, i331, RationalInterval.mul])

def n2213 (b : ℝ) : ℝ := (n2211 b) + (n2212 b)
def i2213 : RationalInterval := ⟨(199494517641860641246424333279 / 125000000000000000000000000000 : ℚ), (797978074309230657652307412617 / 500000000000000000000000000000 : ℚ)⟩
theorem b2213 (b : ℝ) (hb : rootInterval.Contains b) : i2213.Contains (n2213 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2211 b hb) (b2212 b hb))
    (by norm_num [i2213, i2211, i2212, RationalInterval.add]) (by norm_num [i2213, i2211, i2212, RationalInterval.add])

def n2214 (b : ℝ) : ℝ := (n332 b) * (n2210 b)
def i2214 : RationalInterval := ⟨(7113670988374049667885548998267 / 1000000000000000000000000000000 : ℚ), (7113671014166226919271771545189 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2214 (b : ℝ) (hb : rootInterval.Contains b) : i2214.Contains (n2214 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b332 b hb) (b2210 b hb))
    (by norm_num [i2214, i332, i2210, RationalInterval.mul]) (by norm_num [i2214, i332, i2210, RationalInterval.mul])

def n2215 (b : ℝ) : ℝ := (n331 b) * (n2213 b)
def i2215 : RationalInterval := ⟨(-83299320984805844727281805391 / 50000000000000000000000000000 : ℚ), (-416496602821274869484642569503 / 250000000000000000000000000000 : ℚ)⟩
theorem b2215 (b : ℝ) (hb : rootInterval.Contains b) : i2215.Contains (n2215 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b331 b hb) (b2213 b hb))
    (by norm_num [i2215, i331, i2213, RationalInterval.mul]) (by norm_num [i2215, i331, i2213, RationalInterval.mul])

def n2216 (b : ℝ) : ℝ := (n2214 b) + (n2215 b)
def i2216 : RationalInterval := ⟨(5447684568677932773339912890447 / 1000000000000000000000000000000 : ℚ), (5447684602881127441333201267177 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2216 (b : ℝ) (hb : rootInterval.Contains b) : i2216.Contains (n2216 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2214 b hb) (b2215 b hb))
    (by norm_num [i2216, i2214, i2215, RationalInterval.add]) (by norm_num [i2216, i2214, i2215, RationalInterval.add])

def n2217 (b : ℝ) : ℝ := (n2210 b) * (n318 b)
def i2217 : RationalInterval := ⟨(4225699700620237822357787527781 / 1000000000000000000000000000000 : ℚ), (2112849872147786307277672860181 / 500000000000000000000000000000 : ℚ)⟩
theorem b2217 (b : ℝ) (hb : rootInterval.Contains b) : i2217.Contains (n2217 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2210 b hb) (b318 b hb))
    (by norm_num [i2217, i2210, i318, RationalInterval.mul]) (by norm_num [i2217, i2210, i318, RationalInterval.mul])

def n2218 (b : ℝ) : ℝ := (n2210 b) * (n319 b)
def i2218 : RationalInterval := ⟨(364286314254399388277400934251 / 200000000000000000000000000000 : ℚ), (182143159616772590810430706023 / 100000000000000000000000000000 : ℚ)⟩
theorem b2218 (b : ℝ) (hb : rootInterval.Contains b) : i2218.Contains (n2218 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2210 b hb) (b319 b hb))
    (by norm_num [i2218, i2210, i319, RationalInterval.mul]) (by norm_num [i2218, i2210, i319, RationalInterval.mul])

def n2219 (b : ℝ) : ℝ := (n2213 b) * (n318 b)
def i2219 : RationalInterval := ⟨(1993735310284893018808078822337 / 1000000000000000000000000000000 : ℚ), (398747066663321264629642860109 / 200000000000000000000000000000 : ℚ)⟩
theorem b2219 (b : ℝ) (hb : rootInterval.Contains b) : i2219.Contains (n2219 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2213 b hb) (b318 b hb))
    (by norm_num [i2219, i2213, i318, RationalInterval.mul]) (by norm_num [i2219, i2213, i318, RationalInterval.mul])

def n2220 (b : ℝ) : ℝ := (n2213 b) * (n319 b)
def i2220 : RationalInterval := ⟨(429686524858789585331571384023 / 500000000000000000000000000000 : ℚ), (859373062509017714726560070413 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2220 (b : ℝ) (hb : rootInterval.Contains b) : i2220.Contains (n2220 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2213 b hb) (b319 b hb))
    (by norm_num [i2220, i2213, i319, RationalInterval.mul]) (by norm_num [i2220, i2213, i319, RationalInterval.mul])

def n2221 (b : ℝ) : ℝ := (n318 b) * (n2210 b)
def i2221 : RationalInterval := ⟨(4225699700620237822357787527781 / 1000000000000000000000000000000 : ℚ), (2112849872147786307277672860181 / 500000000000000000000000000000 : ℚ)⟩
theorem b2221 (b : ℝ) (hb : rootInterval.Contains b) : i2221.Contains (n2221 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b318 b hb) (b2210 b hb))
    (by norm_num [i2221, i318, i2210, RationalInterval.mul]) (by norm_num [i2221, i318, i2210, RationalInterval.mul])

def n2222 (b : ℝ) : ℝ := (n318 b) * (n2213 b)
def i2222 : RationalInterval := ⟨(1993735310284893018808078822337 / 1000000000000000000000000000000 : ℚ), (398747066663321264629642860109 / 200000000000000000000000000000 : ℚ)⟩
theorem b2222 (b : ℝ) (hb : rootInterval.Contains b) : i2222.Contains (n2222 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b318 b hb) (b2213 b hb))
    (by norm_num [i2222, i318, i2213, RationalInterval.mul]) (by norm_num [i2222, i318, i2213, RationalInterval.mul])

def n2223 (b : ℝ) : ℝ := (n319 b) * (n2210 b)
def i2223 : RationalInterval := ⟨(364286314254399388277400934251 / 200000000000000000000000000000 : ℚ), (182143159616772590810430706023 / 100000000000000000000000000000 : ℚ)⟩
theorem b2223 (b : ℝ) (hb : rootInterval.Contains b) : i2223.Contains (n2223 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b319 b hb) (b2210 b hb))
    (by norm_num [i2223, i319, i2210, RationalInterval.mul]) (by norm_num [i2223, i319, i2210, RationalInterval.mul])

def n2224 (b : ℝ) : ℝ := (n319 b) * (n2213 b)
def i2224 : RationalInterval := ⟨(429686524858789585331571384023 / 500000000000000000000000000000 : ℚ), (859373062509017714726560070413 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2224 (b : ℝ) (hb : rootInterval.Contains b) : i2224.Contains (n2224 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b319 b hb) (b2213 b hb))
    (by norm_num [i2224, i319, i2213, RationalInterval.mul]) (by norm_num [i2224, i319, i2213, RationalInterval.mul])

def n2225 (b : ℝ) : ℝ := (n2217 b) + (n2221 b)
def i2225 : RationalInterval := ⟨(4225699700620237822357787527781 / 500000000000000000000000000000 : ℚ), (2112849872147786307277672860181 / 250000000000000000000000000000 : ℚ)⟩
theorem b2225 (b : ℝ) (hb : rootInterval.Contains b) : i2225.Contains (n2225 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2217 b hb) (b2221 b hb))
    (by norm_num [i2225, i2217, i2221, RationalInterval.add]) (by norm_num [i2225, i2217, i2221, RationalInterval.add])

def n2226 (b : ℝ) : ℝ := (n2218 b) + (n2222 b)
def i2226 : RationalInterval := ⟨(476895860194611245024385436699 / 125000000000000000000000000000 : ℚ), (152606677179373289250100854431 / 40000000000000000000000000000 : ℚ)⟩
theorem b2226 (b : ℝ) (hb : rootInterval.Contains b) : i2226.Contains (n2226 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2218 b hb) (b2222 b hb))
    (by norm_num [i2226, i2218, i2222, RationalInterval.add]) (by norm_num [i2226, i2218, i2222, RationalInterval.add])

def n2227 (b : ℝ) : ℝ := (n2219 b) + (n2223 b)
def i2227 : RationalInterval := ⟨(476895860194611245024385436699 / 125000000000000000000000000000 : ℚ), (152606677179373289250100854431 / 40000000000000000000000000000 : ℚ)⟩
theorem b2227 (b : ℝ) (hb : rootInterval.Contains b) : i2227.Contains (n2227 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2219 b hb) (b2223 b hb))
    (by norm_num [i2227, i2219, i2223, RationalInterval.add]) (by norm_num [i2227, i2219, i2223, RationalInterval.add])

def n2228 (b : ℝ) : ℝ := (n2220 b) + (n2224 b)
def i2228 : RationalInterval := ⟨(429686524858789585331571384023 / 250000000000000000000000000000 : ℚ), (859373062509017714726560070413 / 500000000000000000000000000000 : ℚ)⟩
theorem b2228 (b : ℝ) (hb : rootInterval.Contains b) : i2228.Contains (n2228 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2220 b hb) (b2224 b hb))
    (by norm_num [i2228, i2220, i2224, RationalInterval.add]) (by norm_num [i2228, i2220, i2224, RationalInterval.add])

def n2229 (b : ℝ) : ℝ := (n318 b) * (n318 b)
def i2229 : RationalInterval := ⟨(1560605368889393134626349700689 / 1000000000000000000000000000000 : ℚ), (1560605390310122765454126377613 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2229 (b : ℝ) (hb : rootInterval.Contains b) : i2229.Contains (n2229 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b318 b hb) (b318 b hb))
    (by norm_num [i2229, i318, i318, RationalInterval.mul]) (by norm_num [i2229, i318, i318, RationalInterval.mul])

def n2230 (b : ℝ) : ℝ := (n318 b) * (n319 b)
def i2230 : RationalInterval := ⟨(168169539400451321343927219471 / 250000000000000000000000000000 : ℚ), (42042385567292250963746374631 / 62500000000000000000000000000 : ℚ)⟩
theorem b2230 (b : ℝ) (hb : rootInterval.Contains b) : i2230.Contains (n2230 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b318 b hb) (b319 b hb))
    (by norm_num [i2230, i318, i319, RationalInterval.mul]) (by norm_num [i2230, i318, i319, RationalInterval.mul])

def n2231 (b : ℝ) : ℝ := (n319 b) * (n318 b)
def i2231 : RationalInterval := ⟨(168169539400451321343927219471 / 250000000000000000000000000000 : ℚ), (42042385567292250963746374631 / 62500000000000000000000000000 : ℚ)⟩
theorem b2231 (b : ℝ) (hb : rootInterval.Contains b) : i2231.Contains (n2231 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b319 b hb) (b318 b hb))
    (by norm_num [i2231, i319, i318, RationalInterval.mul]) (by norm_num [i2231, i319, i318, RationalInterval.mul])

def n2232 (b : ℝ) : ℝ := (n319 b) * (n319 b)
def i2232 : RationalInterval := ⟨(289948960022211441864748612333 / 1000000000000000000000000000000 : ℚ), (289948965934578342810598767903 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2232 (b : ℝ) (hb : rootInterval.Contains b) : i2232.Contains (n2232 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b319 b hb) (b319 b hb))
    (by norm_num [i2232, i319, i319, RationalInterval.mul]) (by norm_num [i2232, i319, i319, RationalInterval.mul])

def n2233 (b : ℝ) : ℝ := (n118 b) * (n2199 b)
def i2233 : RationalInterval := ⟨(970057634322681192355371936491 / 500000000000000000000000000000 : ℚ), (30314301436189862608071639711 / 15625000000000000000000000000 : ℚ)⟩
theorem b2233 (b : ℝ) (hb : rootInterval.Contains b) : i2233.Contains (n2233 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b118 b hb) (b2199 b hb))
    (by norm_num [i2233, i118, i2199, RationalInterval.mul]) (by norm_num [i2233, i118, i2199, RationalInterval.mul])

def n2234 (b : ℝ) : ℝ := (n119 b) * (n2200 b)
def i2234 : RationalInterval := ⟨(-935355303720596919208627639969 / 1000000000000000000000000000000 : ℚ), (-467677646415472024423822947759 / 500000000000000000000000000000 : ℚ)⟩
theorem b2234 (b : ℝ) (hb : rootInterval.Contains b) : i2234.Contains (n2234 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b119 b hb) (b2200 b hb))
    (by norm_num [i2234, i119, i2200, RationalInterval.mul]) (by norm_num [i2234, i119, i2200, RationalInterval.mul])

def n2235 (b : ℝ) : ℝ := (n2233 b) + (n2234 b)
def i2235 : RationalInterval := ⟨(1004759964924765465502116233013 / 1000000000000000000000000000000 : ℚ), (502379999542603579034469522993 / 500000000000000000000000000000 : ℚ)⟩
theorem b2235 (b : ℝ) (hb : rootInterval.Contains b) : i2235.Contains (n2235 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2233 b hb) (b2234 b hb))
    (by norm_num [i2235, i2233, i2234, RationalInterval.add]) (by norm_num [i2235, i2233, i2234, RationalInterval.add])

def n2236 (b : ℝ) : ℝ := (n120 b) * (n2199 b)
def i2236 : RationalInterval := ⟨(480846610598035505234038686753 / 500000000000000000000000000000 : ℚ), (12021165413920970318684963507 / 12500000000000000000000000000 : ℚ)⟩
theorem b2236 (b : ℝ) (hb : rootInterval.Contains b) : i2236.Contains (n2236 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b120 b hb) (b2199 b hb))
    (by norm_num [i2236, i120, i2199, RationalInterval.mul]) (by norm_num [i2236, i120, i2199, RationalInterval.mul])

def n2237 (b : ℝ) : ℝ := (n121 b) * (n2200 b)
def i2237 : RationalInterval := ⟨(-532080284849644285428556871019 / 1000000000000000000000000000000 : ℚ), (-66510034783658714188244358659 / 125000000000000000000000000000 : ℚ)⟩
theorem b2237 (b : ℝ) (hb : rootInterval.Contains b) : i2237.Contains (n2237 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b121 b hb) (b2200 b hb))
    (by norm_num [i2237, i121, i2200, RationalInterval.mul]) (by norm_num [i2237, i121, i2200, RationalInterval.mul])

def n2238 (b : ℝ) : ℝ := (n2236 b) + (n2237 b)
def i2238 : RationalInterval := ⟨(429612936346426725039520502487 / 1000000000000000000000000000000 : ℚ), (53701619355550988998605276411 / 125000000000000000000000000000 : ℚ)⟩
theorem b2238 (b : ℝ) (hb : rootInterval.Contains b) : i2238.Contains (n2238 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2236 b hb) (b2237 b hb))
    (by norm_num [i2238, i2236, i2237, RationalInterval.add]) (by norm_num [i2238, i2236, i2237, RationalInterval.add])

def n2239 (b : ℝ) : ℝ := (n2199 b) * (n2210 b)
def i2239 : RationalInterval := ⟨(615238598669717465785692909137 / 200000000000000000000000000000 : ℚ), (3076193036353102208694215901383 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2239 (b : ℝ) (hb : rootInterval.Contains b) : i2239.Contains (n2239 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2199 b hb) (b2210 b hb))
    (by norm_num [i2239, i2199, i2210, RationalInterval.mul]) (by norm_num [i2239, i2199, i2210, RationalInterval.mul])

def n2240 (b : ℝ) : ℝ := (n2200 b) * (n2213 b)
def i2240 : RationalInterval := ⟨(-1411635292628316824469149880611 / 1000000000000000000000000000000 : ℚ), (-1411635274676534095037497370377 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2240 (b : ℝ) (hb : rootInterval.Contains b) : i2240.Contains (n2240 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2200 b hb) (b2213 b hb))
    (by norm_num [i2240, i2200, i2213, RationalInterval.mul]) (by norm_num [i2240, i2200, i2213, RationalInterval.mul])

def n2241 (b : ℝ) : ℝ := (n2239 b) + (n2240 b)
def i2241 : RationalInterval := ⟨(832278850360135252229657332537 / 500000000000000000000000000000 : ℚ), (832278880838284056828359265503 / 500000000000000000000000000000 : ℚ)⟩
theorem b2241 (b : ℝ) (hb : rootInterval.Contains b) : i2241.Contains (n2241 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2239 b hb) (b2240 b hb))
    (by norm_num [i2241, i2239, i2240, RationalInterval.add]) (by norm_num [i2241, i2239, i2240, RationalInterval.add])

def n2242 (b : ℝ) : ℝ := (n2241 b) * (n13 b)
def i2242 : RationalInterval := ⟨(832278850360135252229657332537 / 250000000000000000000000000000 : ℚ), (832278880838284056828359265503 / 250000000000000000000000000000 : ℚ)⟩
theorem b2242 (b : ℝ) (hb : rootInterval.Contains b) : i2242.Contains (n2242 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2241 b hb) (b13 b hb))
    (by norm_num [i2242, i2241, i13, RationalInterval.mul]) (by norm_num [i2242, i2241, i13, RationalInterval.mul])

def n2243 (b : ℝ) : ℝ := (n2188 b) * (n318 b)
def i2243 : RationalInterval := ⟨(-563827121032002840255877030329 / 1000000000000000000000000000000 : ℚ), (-22553084506093189177876678369 / 40000000000000000000000000000 : ℚ)⟩
theorem b2243 (b : ℝ) (hb : rootInterval.Contains b) : i2243.Contains (n2243 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2188 b hb) (b318 b hb))
    (by norm_num [i2243, i2188, i318, RationalInterval.mul]) (by norm_num [i2243, i2188, i318, RationalInterval.mul])

def n2244 (b : ℝ) : ℝ := (n2188 b) * (n319 b)
def i2244 : RationalInterval := ⟨(-243030171372285141971597880403 / 1000000000000000000000000000000 : ℚ), (-243030166950422355973952247671 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2244 (b : ℝ) (hb : rootInterval.Contains b) : i2244.Contains (n2244 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2188 b hb) (b319 b hb))
    (by norm_num [i2244, i2188, i319, RationalInterval.mul]) (by norm_num [i2244, i2188, i319, RationalInterval.mul])

def n2245 (b : ℝ) : ℝ := (n2189 b) * (n318 b)
def i2245 : RationalInterval := ⟨(-4438063619322881273468888063 / 15625000000000000000000000000 : ℚ), (-71009016816339843687640904703 / 250000000000000000000000000000 : ℚ)⟩
theorem b2245 (b : ℝ) (hb : rootInterval.Contains b) : i2245.Contains (n2245 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2189 b hb) (b318 b hb))
    (by norm_num [i2245, i2189, i318, RationalInterval.mul]) (by norm_num [i2245, i2189, i318, RationalInterval.mul])

def n2246 (b : ℝ) : ℝ := (n2189 b) * (n319 b)
def i2246 : RationalInterval := ⟨(-61214982918364352662765140333 / 500000000000000000000000000000 : ℚ), (-12242996354452883800310424683 / 100000000000000000000000000000 : ℚ)⟩
theorem b2246 (b : ℝ) (hb : rootInterval.Contains b) : i2246.Contains (n2246 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2189 b hb) (b319 b hb))
    (by norm_num [i2246, i2189, i319, RationalInterval.mul]) (by norm_num [i2246, i2189, i319, RationalInterval.mul])

def n2247 (b : ℝ) : ℝ := (n318 b) * (n2188 b)
def i2247 : RationalInterval := ⟨(-563827121032002840255877030329 / 1000000000000000000000000000000 : ℚ), (-22553084506093189177876678369 / 40000000000000000000000000000 : ℚ)⟩
theorem b2247 (b : ℝ) (hb : rootInterval.Contains b) : i2247.Contains (n2247 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b318 b hb) (b2188 b hb))
    (by norm_num [i2247, i318, i2188, RationalInterval.mul]) (by norm_num [i2247, i318, i2188, RationalInterval.mul])

def n2248 (b : ℝ) : ℝ := (n318 b) * (n2189 b)
def i2248 : RationalInterval := ⟨(-4438063619322881273468888063 / 15625000000000000000000000000 : ℚ), (-71009016816339843687640904703 / 250000000000000000000000000000 : ℚ)⟩
theorem b2248 (b : ℝ) (hb : rootInterval.Contains b) : i2248.Contains (n2248 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b318 b hb) (b2189 b hb))
    (by norm_num [i2248, i318, i2189, RationalInterval.mul]) (by norm_num [i2248, i318, i2189, RationalInterval.mul])

def n2249 (b : ℝ) : ℝ := (n319 b) * (n2188 b)
def i2249 : RationalInterval := ⟨(-243030171372285141971597880403 / 1000000000000000000000000000000 : ℚ), (-243030166950422355973952247671 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2249 (b : ℝ) (hb : rootInterval.Contains b) : i2249.Contains (n2249 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b319 b hb) (b2188 b hb))
    (by norm_num [i2249, i319, i2188, RationalInterval.mul]) (by norm_num [i2249, i319, i2188, RationalInterval.mul])

