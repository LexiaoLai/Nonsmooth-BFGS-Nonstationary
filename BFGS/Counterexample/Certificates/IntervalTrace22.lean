import BFGS.Counterexample.Certificates.IntervalTrace21

/-! Generated arithmetic proofs. Each bound is checked by the Lean kernel. -/
namespace BFGS.Counterexample.Trace
noncomputable section
open BFGS RationalInterval
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false

def n1980 (b : ℝ) : ℝ := (n56 b) * (n1370 b)
def i1980 : RationalInterval := ⟨(360953231934962242069319855489 / 250000000000000000000000000000 : ℚ), (1443813889329978498653163298857 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1980 (b : ℝ) (hb : rootInterval.Contains b) : i1980.Contains (n1980 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b56 b hb) (b1370 b hb))
    (by norm_num [i1980, i56, i1370, RationalInterval.mul]) (by norm_num [i1980, i56, i1370, RationalInterval.mul])

def n1981 (b : ℝ) : ℝ := (n1979 b) + (n1980 b)
def i1981 : RationalInterval := ⟨(-22954812956935090710179551231 / 25000000000000000000000000000 : ℚ), (-229547813945339296220635775947 / 250000000000000000000000000000 : ℚ)⟩
theorem b1981 (b : ℝ) (hb : rootInterval.Contains b) : i1981.Contains (n1981 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1979 b hb) (b1980 b hb))
    (by norm_num [i1981, i1979, i1980, RationalInterval.add]) (by norm_num [i1981, i1979, i1980, RationalInterval.add])

def n1982 (b : ℝ) : ℝ := (n324 b) * (n1407 b)
def i1982 : RationalInterval := ⟨(-35468222755041106198847952427 / 500000000000000000000000000000 : ℚ), (-70936393244357476534712653097 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1982 (b : ℝ) (hb : rootInterval.Contains b) : i1982.Contains (n1982 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b324 b hb) (b1407 b hb))
    (by norm_num [i1982, i324, i1407, RationalInterval.mul]) (by norm_num [i1982, i324, i1407, RationalInterval.mul])

def n1983 (b : ℝ) : ℝ := (n1981 b) + (n1982 b)
def i1983 : RationalInterval := ⟨(-494564481893742920402438977047 / 500000000000000000000000000000 : ℚ), (-197825529805142932283451151377 / 200000000000000000000000000000 : ℚ)⟩
theorem b1983 (b : ℝ) (hb : rootInterval.Contains b) : i1983.Contains (n1983 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1981 b hb) (b1982 b hb))
    (by norm_num [i1983, i1981, i1982, RationalInterval.add]) (by norm_num [i1983, i1981, i1982, RationalInterval.add])

def n1984 (b : ℝ) : ℝ := (n1481 b) * (n1338 b)
def i1984 : RationalInterval := ⟨(-4543464705248902807438202738629 / 1000000000000000000000000000000 : ℚ), (-4543464480644282631601299283513 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1984 (b : ℝ) (hb : rootInterval.Contains b) : i1984.Contains (n1984 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1481 b hb) (b1338 b hb))
    (by norm_num [i1984, i1481, i1338, RationalInterval.mul]) (by norm_num [i1984, i1481, i1338, RationalInterval.mul])

def n1985 (b : ℝ) : ℝ := (n1624 b) * (n1355 b)
def i1985 : RationalInterval := ⟨(-358596647310305543483450472717 / 200000000000000000000000000000 : ℚ), (-1792983057875359640761083789703 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1985 (b : ℝ) (hb : rootInterval.Contains b) : i1985.Contains (n1985 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1624 b hb) (b1355 b hb))
    (by norm_num [i1985, i1624, i1355, RationalInterval.mul]) (by norm_num [i1985, i1624, i1355, RationalInterval.mul])

def n1986 (b : ℝ) : ℝ := (n1984 b) + (n1985 b)
def i1986 : RationalInterval := ⟨(-3168223970900215262427727551107 / 500000000000000000000000000000 : ℚ), (-99006992789369410505662235519 / 15625000000000000000000000000 : ℚ)⟩
theorem b1986 (b : ℝ) (hb : rootInterval.Contains b) : i1986.Contains (n1986 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1984 b hb) (b1985 b hb))
    (by norm_num [i1986, i1984, i1985, RationalInterval.add]) (by norm_num [i1986, i1984, i1985, RationalInterval.add])

def n1987 (b : ℝ) : ℝ := (n56 b) * (n1379 b)
def i1987 : RationalInterval := ⟨(4168278017304731953529821186081 / 1000000000000000000000000000000 : ℚ), (833656212059421607446081301909 / 200000000000000000000000000000 : ℚ)⟩
theorem b1987 (b : ℝ) (hb : rootInterval.Contains b) : i1987.Contains (n1987 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b56 b hb) (b1379 b hb))
    (by norm_num [i1987, i56, i1379, RationalInterval.mul]) (by norm_num [i1987, i56, i1379, RationalInterval.mul])

def n1988 (b : ℝ) : ℝ := (n1986 b) + (n1987 b)
def i1988 : RationalInterval := ⟨(-2168169924495698571325633916133 / 1000000000000000000000000000000 : ℚ), (-2168166478222534235131976563671 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1988 (b : ℝ) (hb : rootInterval.Contains b) : i1988.Contains (n1988 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1986 b hb) (b1987 b hb))
    (by norm_num [i1988, i1986, i1987, RationalInterval.add]) (by norm_num [i1988, i1986, i1987, RationalInterval.add])

def n1989 (b : ℝ) : ℝ := (n324 b) * (n1416 b)
def i1989 : RationalInterval := ⟨(-108314442389583178757558361533 / 500000000000000000000000000000 : ℚ), (-108314363564868414069157668279 / 500000000000000000000000000000 : ℚ)⟩
theorem b1989 (b : ℝ) (hb : rootInterval.Contains b) : i1989.Contains (n1989 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b324 b hb) (b1416 b hb))
    (by norm_num [i1989, i324, i1416, RationalInterval.mul]) (by norm_num [i1989, i324, i1416, RationalInterval.mul])

def n1990 (b : ℝ) : ℝ := (n1988 b) + (n1989 b)
def i1990 : RationalInterval := ⟨(-2384798809274864928840750639199 / 1000000000000000000000000000000 : ℚ), (-2384795205352271063270291900229 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1990 (b : ℝ) (hb : rootInterval.Contains b) : i1990.Contains (n1990 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1988 b hb) (b1989 b hb))
    (by norm_num [i1990, i1988, i1989, RationalInterval.add]) (by norm_num [i1990, i1988, i1989, RationalInterval.add])

def n1991 (b : ℝ) : ℝ := (n1481 b) * (n1341 b)
def i1991 : RationalInterval := ⟨(2538601265748697446924284503273 / 200000000000000000000000000000 : ℚ), (6346503228035427979443812636309 / 500000000000000000000000000000 : ℚ)⟩
theorem b1991 (b : ℝ) (hb : rootInterval.Contains b) : i1991.Contains (n1991 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1481 b hb) (b1341 b hb))
    (by norm_num [i1991, i1481, i1341, RationalInterval.mul]) (by norm_num [i1991, i1481, i1341, RationalInterval.mul])

def n1992 (b : ℝ) : ℝ := (n1624 b) * (n1358 b)
def i1992 : RationalInterval := ⟨(2861482928363879539808495920637 / 200000000000000000000000000000 : ℚ), (715370741354036335471895180693 / 50000000000000000000000000000 : ℚ)⟩
theorem b1992 (b : ℝ) (hb : rootInterval.Contains b) : i1992.Contains (n1992 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1624 b hb) (b1358 b hb))
    (by norm_num [i1992, i1624, i1358, RationalInterval.mul]) (by norm_num [i1992, i1624, i1358, RationalInterval.mul])

def n1993 (b : ℝ) : ℝ := (n1991 b) + (n1992 b)
def i1993 : RationalInterval := ⟨(540008419411257698673278042391 / 20000000000000000000000000000 : ℚ), (13500210641575791334162764443239 / 500000000000000000000000000000 : ℚ)⟩
theorem b1993 (b : ℝ) (hb : rootInterval.Contains b) : i1993.Contains (n1993 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1991 b hb) (b1992 b hb))
    (by norm_num [i1993, i1991, i1992, RationalInterval.add]) (by norm_num [i1993, i1991, i1992, RationalInterval.add])

def n1994 (b : ℝ) : ℝ := (n56 b) * (n1386 b)
def i1994 : RationalInterval := ⟨(-8323680286072941813328307319337 / 500000000000000000000000000000 : ℚ), (-16647357042665757075627877439809 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1994 (b : ℝ) (hb : rootInterval.Contains b) : i1994.Contains (n1994 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b56 b hb) (b1386 b hb))
    (by norm_num [i1994, i56, i1386, RationalInterval.mul]) (by norm_num [i1994, i56, i1386, RationalInterval.mul])

def n1995 (b : ℝ) : ℝ := (n1993 b) + (n1994 b)
def i1995 : RationalInterval := ⟨(2588265099604250326751821870219 / 250000000000000000000000000000 : ℚ), (10353064240485825592697651446669 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1995 (b : ℝ) (hb : rootInterval.Contains b) : i1995.Contains (n1995 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1993 b hb) (b1994 b hb))
    (by norm_num [i1995, i1993, i1994, RationalInterval.add]) (by norm_num [i1995, i1993, i1994, RationalInterval.add])

def n1996 (b : ℝ) : ℝ := (n324 b) * (n1423 b)
def i1996 : RationalInterval := ⟨(904150458864037876110840032939 / 1000000000000000000000000000000 : ℚ), (22603766034006148497319080509 / 25000000000000000000000000000 : ℚ)⟩
theorem b1996 (b : ℝ) (hb : rootInterval.Contains b) : i1996.Contains (n1996 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b324 b hb) (b1423 b hb))
    (by norm_num [i1996, i324, i1423, RationalInterval.mul]) (by norm_num [i1996, i324, i1423, RationalInterval.mul])

def n1997 (b : ℝ) : ℝ := (n1995 b) + (n1996 b)
def i1997 : RationalInterval := ⟨(2251442171456207836623625502763 / 200000000000000000000000000000 : ℚ), (11257214881846071532590414667029 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1997 (b : ℝ) (hb : rootInterval.Contains b) : i1997.Contains (n1997 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1995 b hb) (b1996 b hb))
    (by norm_num [i1997, i1995, i1996, RationalInterval.add]) (by norm_num [i1997, i1995, i1996, RationalInterval.add])

def n1998 (b : ℝ) : ℝ := (n1481 b) * (n1344 b)
def i1998 : RationalInterval := ⟨(-6443392005015766843929163913417 / 1000000000000000000000000000000 : ℚ), (-6443391936232161729689720313427 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1998 (b : ℝ) (hb : rootInterval.Contains b) : i1998.Contains (n1998 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1481 b hb) (b1344 b hb))
    (by norm_num [i1998, i1481, i1344, RationalInterval.mul]) (by norm_num [i1998, i1481, i1344, RationalInterval.mul])

def n1999 (b : ℝ) : ℝ := (n1624 b) * (n1361 b)
def i1999 : RationalInterval := ⟨(-4008182353263008849427566847609 / 500000000000000000000000000000 : ℚ), (-2004091150366715524530718486473 / 250000000000000000000000000000 : ℚ)⟩
theorem b1999 (b : ℝ) (hb : rootInterval.Contains b) : i1999.Contains (n1999 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1624 b hb) (b1361 b hb))
    (by norm_num [i1999, i1624, i1361, RationalInterval.mul]) (by norm_num [i1999, i1624, i1361, RationalInterval.mul])

def n2000 (b : ℝ) : ℝ := (n1998 b) + (n1999 b)
def i2000 : RationalInterval := ⟨(-2891951342308356908556859521727 / 200000000000000000000000000000 : ℚ), (-14459756537699023827812594259319 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2000 (b : ℝ) (hb : rootInterval.Contains b) : i2000.Contains (n2000 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1998 b hb) (b1999 b hb))
    (by norm_num [i2000, i1998, i1999, RationalInterval.add]) (by norm_num [i2000, i1998, i1999, RationalInterval.add])

def n2001 (b : ℝ) : ℝ := (n56 b) * (n1393 b)
def i2001 : RationalInterval := ⟨(8702462121367543808816299109837 / 1000000000000000000000000000000 : ℚ), (8702464056427119235029952070249 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2001 (b : ℝ) (hb : rootInterval.Contains b) : i2001.Contains (n2001 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b56 b hb) (b1393 b hb))
    (by norm_num [i2001, i56, i1393, RationalInterval.mul]) (by norm_num [i2001, i56, i1393, RationalInterval.mul])

def n2002 (b : ℝ) : ℝ := (n2000 b) + (n2001 b)
def i2002 : RationalInterval := ⟨(-2878647295087120366983999249399 / 500000000000000000000000000000 : ℚ), (-575729248127190459278264218907 / 100000000000000000000000000000 : ℚ)⟩
theorem b2002 (b : ℝ) (hb : rootInterval.Contains b) : i2002.Contains (n2002 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2000 b hb) (b2001 b hb))
    (by norm_num [i2002, i2000, i2001, RationalInterval.add]) (by norm_num [i2002, i2000, i2001, RationalInterval.add])

def n2003 (b : ℝ) : ℝ := (n324 b) * (n1430 b)
def i2003 : RationalInterval := ⟨(-120856715034400878693119940037 / 250000000000000000000000000000 : ℚ), (-30214172515208375419978749559 / 62500000000000000000000000000 : ℚ)⟩
theorem b2003 (b : ℝ) (hb : rootInterval.Contains b) : i2003.Contains (n2003 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b324 b hb) (b1430 b hb))
    (by norm_num [i2003, i324, i1430, RationalInterval.mul]) (by norm_num [i2003, i324, i1430, RationalInterval.mul])

def n2004 (b : ℝ) : ℝ := (n2002 b) + (n2003 b)
def i2004 : RationalInterval := ⟨(-3120360725155922124370239129473 / 500000000000000000000000000000 : ℚ), (-3120359620757619299751151091007 / 500000000000000000000000000000 : ℚ)⟩
theorem b2004 (b : ℝ) (hb : rootInterval.Contains b) : i2004.Contains (n2004 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2002 b hb) (b2003 b hb))
    (by norm_num [i2004, i2002, i2003, RationalInterval.add]) (by norm_num [i2004, i2002, i2003, RationalInterval.add])

def n2005 (b : ℝ) : ℝ := (n1481 b) * (n1345 b)
def i2005 : RationalInterval := ⟨(-1837289095414165217933098113733 / 250000000000000000000000000000 : ℚ), (-918644542003043787189477330571 / 125000000000000000000000000000 : ℚ)⟩
theorem b2005 (b : ℝ) (hb : rootInterval.Contains b) : i2005.Contains (n2005 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1481 b hb) (b1345 b hb))
    (by norm_num [i2005, i1481, i1345, RationalInterval.mul]) (by norm_num [i2005, i1481, i1345, RationalInterval.mul])

def n2006 (b : ℝ) : ℝ := (n1624 b) * (n1345 b)
def i2006 : RationalInterval := ⟨(-295862354500740236678169837221 / 25000000000000000000000000000 : ℚ), (-2958623514883275966853833901707 / 250000000000000000000000000000 : ℚ)⟩
theorem b2006 (b : ℝ) (hb : rootInterval.Contains b) : i2006.Contains (n2006 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1624 b hb) (b1345 b hb))
    (by norm_num [i2006, i1624, i1345, RationalInterval.mul]) (by norm_num [i2006, i1624, i1345, RationalInterval.mul])

def n2007 (b : ℝ) : ℝ := (n2005 b) + (n2006 b)
def i2007 : RationalInterval := ⟨(-4795912640421567584714796485943 / 250000000000000000000000000000 : ℚ), (-4795912598889363541232788562849 / 250000000000000000000000000000 : ℚ)⟩
theorem b2007 (b : ℝ) (hb : rootInterval.Contains b) : i2007.Contains (n2007 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2005 b hb) (b2006 b hb))
    (by norm_num [i2007, i2005, i2006, RationalInterval.add]) (by norm_num [i2007, i2005, i2006, RationalInterval.add])

def n2008 (b : ℝ) : ℝ := (n56 b) * (n1398 b)
def i2008 : RationalInterval := ⟨(5812164874352542214278207349311 / 500000000000000000000000000000 : ℚ), (5812166073650734564661064807689 / 500000000000000000000000000000 : ℚ)⟩
theorem b2008 (b : ℝ) (hb : rootInterval.Contains b) : i2008.Contains (n2008 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b56 b hb) (b1398 b hb))
    (by norm_num [i2008, i56, i1398, RationalInterval.mul]) (by norm_num [i2008, i56, i1398, RationalInterval.mul])

def n2009 (b : ℝ) : ℝ := (n2007 b) + (n2008 b)
def i2009 : RationalInterval := ⟨(-151186416259623718206055424903 / 20000000000000000000000000000 : ℚ), (-3779659124127992517804512318009 / 500000000000000000000000000000 : ℚ)⟩
theorem b2009 (b : ℝ) (hb : rootInterval.Contains b) : i2009.Contains (n2009 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2007 b hb) (b2008 b hb))
    (by norm_num [i2009, i2007, i2008, RationalInterval.add]) (by norm_num [i2009, i2007, i2008, RationalInterval.add])

def n2010 (b : ℝ) : ℝ := (n324 b) * (n1435 b)
def i2010 : RationalInterval := ⟨(-26761686779989839743528637053 / 40000000000000000000000000000 : ℚ), (-669042045334842973973282905669 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2010 (b : ℝ) (hb : rootInterval.Contains b) : i2010.Contains (n2010 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b324 b hb) (b1435 b hb))
    (by norm_num [i2010, i324, i1435, RationalInterval.mul]) (by norm_num [i2010, i324, i1435, RationalInterval.mul])

def n2011 (b : ℝ) : ℝ := (n2009 b) + (n2010 b)
def i2011 : RationalInterval := ⟨(-329134519299237276155639486859 / 40000000000000000000000000000 : ℚ), (-8228360293590828009582307541687 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2011 (b : ℝ) (hb : rootInterval.Contains b) : i2011.Contains (n2011 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2009 b hb) (b2010 b hb))
    (by norm_num [i2011, i2009, i2010, RationalInterval.add]) (by norm_num [i2011, i2009, i2010, RationalInterval.add])

def n2012 (b : ℝ) : ℝ := (n1480 b) * (n1333 b)
def i2012 : RationalInterval := ⟨(-31421415159055796210338895987 / 125000000000000000000000000000 : ℚ), (-25137126837747510757564499519 / 100000000000000000000000000000 : ℚ)⟩
theorem b2012 (b : ℝ) (hb : rootInterval.Contains b) : i2012.Contains (n2012 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1480 b hb) (b1333 b hb))
    (by norm_num [i2012, i1480, i1333, RationalInterval.mul]) (by norm_num [i2012, i1480, i1333, RationalInterval.mul])

def n2013 (b : ℝ) : ℝ := (n1626 b) * (n1350 b)
def i2013 : RationalInterval := ⟨(-1649951224042752769868123225871 / 1000000000000000000000000000000 : ℚ), (-51560971296802375561073665991 / 31250000000000000000000000000 : ℚ)⟩
theorem b2013 (b : ℝ) (hb : rootInterval.Contains b) : i2013.Contains (n2013 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1626 b hb) (b1350 b hb))
    (by norm_num [i2013, i1626, i1350, RationalInterval.mul]) (by norm_num [i2013, i1626, i1350, RationalInterval.mul])

def n2014 (b : ℝ) : ℝ := (n2012 b) + (n2013 b)
def i2014 : RationalInterval := ⟨(-1901322545315199139550834393767 / 1000000000000000000000000000000 : ℚ), (-950661174937575562765001153451 / 500000000000000000000000000000 : ℚ)⟩
theorem b2014 (b : ℝ) (hb : rootInterval.Contains b) : i2014.Contains (n2014 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2012 b hb) (b2013 b hb))
    (by norm_num [i2014, i2012, i2013, RationalInterval.add]) (by norm_num [i2014, i2012, i2013, RationalInterval.add])

def n2015 (b : ℝ) : ℝ := (n56 b) * (n1407 b)
def i2015 : RationalInterval := ⟨(182141757037591637842837185067 / 200000000000000000000000000000 : ℚ), (910709450232192277616610948731 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2015 (b : ℝ) (hb : rootInterval.Contains b) : i2015.Contains (n2015 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b56 b hb) (b1407 b hb))
    (by norm_num [i2015, i56, i1407, RationalInterval.mul]) (by norm_num [i2015, i56, i1407, RationalInterval.mul])

def n2016 (b : ℝ) : ℝ := (n2014 b) + (n2015 b)
def i2016 : RationalInterval := ⟨(-61913360007952559396040529277 / 62500000000000000000000000000 : ℚ), (-990612899642958847913391358171 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2016 (b : ℝ) (hb : rootInterval.Contains b) : i2016.Contains (n2016 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2014 b hb) (b2015 b hb))
    (by norm_num [i2016, i2014, i2015, RationalInterval.add]) (by norm_num [i2016, i2014, i2015, RationalInterval.add])

def n2017 (b : ℝ) : ℝ := (n324 b) * (n1444 b)
def i2017 : RationalInterval := ⟨(-44872757690075029238037234513 / 1000000000000000000000000000000 : ℚ), (-22436360239128500786565625283 / 500000000000000000000000000000 : ℚ)⟩
theorem b2017 (b : ℝ) (hb : rootInterval.Contains b) : i2017.Contains (n2017 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b324 b hb) (b1444 b hb))
    (by norm_num [i2017, i324, i1444, RationalInterval.mul]) (by norm_num [i2017, i324, i1444, RationalInterval.mul])

def n2018 (b : ℝ) : ℝ := (n2016 b) + (n2017 b)
def i2018 : RationalInterval := ⟨(-207097303563463195914937140589 / 200000000000000000000000000000 : ℚ), (-1035485620121215849486522608737 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2018 (b : ℝ) (hb : rootInterval.Contains b) : i2018.Contains (n2018 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2016 b hb) (b2017 b hb))
    (by norm_num [i2018, i2016, i2017, RationalInterval.add]) (by norm_num [i2018, i2016, i2017, RationalInterval.add])

def n2019 (b : ℝ) : ℝ := (n1480 b) * (n1338 b)
def i2019 : RationalInterval := ⟨(-365393605794450980642953858993 / 250000000000000000000000000000 : ℚ), (-91348396280464313344731099711 / 62500000000000000000000000000 : ℚ)⟩
theorem b2019 (b : ℝ) (hb : rootInterval.Contains b) : i2019.Contains (n2019 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1480 b hb) (b1338 b hb))
    (by norm_num [i2019, i1480, i1338, RationalInterval.mul]) (by norm_num [i2019, i1480, i1338, RationalInterval.mul])

def n2020 (b : ℝ) : ℝ := (n1626 b) * (n1355 b)
def i2020 : RationalInterval := ⟨(-93583242747614280592231450401 / 50000000000000000000000000000 : ℚ), (-1871664674952731538619714105889 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2020 (b : ℝ) (hb : rootInterval.Contains b) : i2020.Contains (n2020 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1626 b hb) (b1355 b hb))
    (by norm_num [i2020, i1626, i1355, RationalInterval.mul]) (by norm_num [i2020, i1626, i1355, RationalInterval.mul])

def n2021 (b : ℝ) : ℝ := (n2019 b) + (n2020 b)
def i2021 : RationalInterval := ⟨(-416654909766261191802055555499 / 125000000000000000000000000000 : ℚ), (-666647803088032110427082340253 / 200000000000000000000000000000 : ℚ)⟩
theorem b2021 (b : ℝ) (hb : rootInterval.Contains b) : i2021.Contains (n2021 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2019 b hb) (b2020 b hb))
    (by norm_num [i2021, i2019, i2020, RationalInterval.add]) (by norm_num [i2021, i2019, i2020, RationalInterval.add])

def n2022 (b : ℝ) : ℝ := (n56 b) * (n1416 b)
def i2022 : RationalInterval := ⟨(695290794675514059573707597317 / 250000000000000000000000000000 : ℚ), (1390582592227624521747156110889 / 500000000000000000000000000000 : ℚ)⟩
theorem b2022 (b : ℝ) (hb : rootInterval.Contains b) : i2022.Contains (n2022 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b56 b hb) (b1416 b hb))
    (by norm_num [i2022, i56, i1416, RationalInterval.mul]) (by norm_num [i2022, i56, i1416, RationalInterval.mul])

def n2023 (b : ℝ) : ℝ := (n2021 b) + (n2022 b)
def i2023 : RationalInterval := ⟨(-138019024857008324030403513681 / 250000000000000000000000000000 : ℚ), (-552073830984911508641099479487 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2023 (b : ℝ) (hb : rootInterval.Contains b) : i2023.Contains (n2023 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2021 b hb) (b2022 b hb))
    (by norm_num [i2023, i2021, i2022, RationalInterval.add]) (by norm_num [i2023, i2021, i2022, RationalInterval.add])

def n2024 (b : ℝ) : ℝ := (n324 b) * (n1453 b)
def i2024 : RationalInterval := ⟨(-141846356687095876468130292923 / 1000000000000000000000000000000 : ℚ), (-2836925024307741202341574663 / 20000000000000000000000000000 : ℚ)⟩
theorem b2024 (b : ℝ) (hb : rootInterval.Contains b) : i2024.Contains (n2024 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b324 b hb) (b1453 b hb))
    (by norm_num [i2024, i324, i1453, RationalInterval.mul]) (by norm_num [i2024, i324, i1453, RationalInterval.mul])

def n2025 (b : ℝ) : ℝ := (n2023 b) + (n2024 b)
def i2025 : RationalInterval := ⟨(-693922456115129172589744347647 / 1000000000000000000000000000000 : ℚ), (-693920082200298568758178212637 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2025 (b : ℝ) (hb : rootInterval.Contains b) : i2025.Contains (n2025 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2023 b hb) (b2024 b hb))
    (by norm_num [i2025, i2023, i2024, RationalInterval.add]) (by norm_num [i2025, i2023, i2024, RationalInterval.add])

def n2026 (b : ℝ) : ℝ := (n1480 b) * (n1341 b)
def i2026 : RationalInterval := ⟨(4083177591190347444701626430561 / 1000000000000000000000000000000 : ℚ), (102079441532756377487788755277 / 25000000000000000000000000000 : ℚ)⟩
theorem b2026 (b : ℝ) (hb : rootInterval.Contains b) : i2026.Contains (n2026 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1480 b hb) (b1341 b hb))
    (by norm_num [i2026, i1480, i1341, RationalInterval.mul]) (by norm_num [i2026, i1480, i1341, RationalInterval.mul])

def n2027 (b : ℝ) : ℝ := (n1626 b) * (n1358 b)
def i2027 : RationalInterval := ⟨(7467634024028907500548436920959 / 500000000000000000000000000000 : ℚ), (2987053637888337123506514339431 / 200000000000000000000000000000 : ℚ)⟩
theorem b2027 (b : ℝ) (hb : rootInterval.Contains b) : i2027.Contains (n2027 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1626 b hb) (b1358 b hb))
    (by norm_num [i2027, i1626, i1358, RationalInterval.mul]) (by norm_num [i2027, i1626, i1358, RationalInterval.mul])

def n2028 (b : ℝ) : ℝ := (n2026 b) + (n2027 b)
def i2028 : RationalInterval := ⟨(19018445639248162445798500272479 / 1000000000000000000000000000000 : ℚ), (3803689170150388143408824381647 / 200000000000000000000000000000 : ℚ)⟩
theorem b2028 (b : ℝ) (hb : rootInterval.Contains b) : i2028.Contains (n2028 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2026 b hb) (b2027 b hb))
    (by norm_num [i2028, i2026, i2027, RationalInterval.add]) (by norm_num [i2028, i2026, i2027, RationalInterval.add])

def n2029 (b : ℝ) : ℝ := (n56 b) * (n1423 b)
def i2029 : RationalInterval := ⟨(-5803917348827697982212264848333 / 500000000000000000000000000000 : ℚ), (-11607832430706509937246188568597 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2029 (b : ℝ) (hb : rootInterval.Contains b) : i2029.Contains (n2029 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b56 b hb) (b1423 b hb))
    (by norm_num [i2029, i56, i1423, RationalInterval.mul]) (by norm_num [i2029, i56, i1423, RationalInterval.mul])

def n2030 (b : ℝ) : ℝ := (n2028 b) + (n2029 b)
def i2030 : RationalInterval := ⟨(7410610941592766481373970575813 / 1000000000000000000000000000000 : ℚ), (3705306710022715389898966669819 / 500000000000000000000000000000 : ℚ)⟩
theorem b2030 (b : ℝ) (hb : rootInterval.Contains b) : i2030.Contains (n2030 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2028 b hb) (b2029 b hb))
    (by norm_num [i2030, i2028, i2029, RationalInterval.add]) (by norm_num [i2030, i2028, i2029, RationalInterval.add])

def n2031 (b : ℝ) : ℝ := (n324 b) * (n1460 b)
def i2031 : RationalInterval := ⟨(599906874590886436674856431339 / 1000000000000000000000000000000 : ℚ), (599906992402469710512164094937 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2031 (b : ℝ) (hb : rootInterval.Contains b) : i2031.Contains (n2031 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b324 b hb) (b1460 b hb))
    (by norm_num [i2031, i324, i1460, RationalInterval.mul]) (by norm_num [i2031, i324, i1460, RationalInterval.mul])

def n2032 (b : ℝ) : ℝ := (n2030 b) + (n2031 b)
def i2032 : RationalInterval := ⟨(500657363511478307378051687947 / 62500000000000000000000000000 : ℚ), (320420816497916019612403897383 / 40000000000000000000000000000 : ℚ)⟩
theorem b2032 (b : ℝ) (hb : rootInterval.Contains b) : i2032.Contains (n2032 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2030 b hb) (b2031 b hb))
    (by norm_num [i2032, i2030, i2031, RationalInterval.add]) (by norm_num [i2032, i2030, i2031, RationalInterval.add])

def n2033 (b : ℝ) : ℝ := (n1480 b) * (n1344 b)
def i2033 : RationalInterval := ⟨(-414551341937781287982957325447 / 200000000000000000000000000000 : ℚ), (-129547292047459493375177193251 / 62500000000000000000000000000 : ℚ)⟩
theorem b2033 (b : ℝ) (hb : rootInterval.Contains b) : i2033.Contains (n2033 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1480 b hb) (b1344 b hb))
    (by norm_num [i2033, i1480, i1344, RationalInterval.mul]) (by norm_num [i2033, i1480, i1344, RationalInterval.mul])

def n2034 (b : ℝ) : ℝ := (n1626 b) * (n1361 b)
def i2034 : RationalInterval := ⟨(-4184073721331038500236846432717 / 500000000000000000000000000000 : ℚ), (-8368147362131999936029825671959 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2034 (b : ℝ) (hb : rootInterval.Contains b) : i2034.Contains (n2034 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1626 b hb) (b1361 b hb))
    (by norm_num [i2034, i1626, i1361, RationalInterval.mul]) (by norm_num [i2034, i1626, i1361, RationalInterval.mul])

def n2035 (b : ℝ) : ℝ := (n2033 b) + (n2034 b)
def i2035 : RationalInterval := ⟨(-10440904152350983440388479492669 / 1000000000000000000000000000000 : ℚ), (-417636161395654073201306430559 / 40000000000000000000000000000 : ℚ)⟩
theorem b2035 (b : ℝ) (hb : rootInterval.Contains b) : i2035.Contains (n2035 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2033 b hb) (b2034 b hb))
    (by norm_num [i2035, i2033, i2034, RationalInterval.add]) (by norm_num [i2035, i2033, i2034, RationalInterval.add])

def n2036 (b : ℝ) : ℝ := (n56 b) * (n1430 b)
def i2036 : RationalInterval := ⟨(6060956312473806507830973823 / 976562500000000000000000000 : ℚ), (1551605126453711848318747387271 / 250000000000000000000000000000 : ℚ)⟩
theorem b2036 (b : ℝ) (hb : rootInterval.Contains b) : i2036.Contains (n2036 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b56 b hb) (b1430 b hb))
    (by norm_num [i2036, i56, i1430, RationalInterval.mul]) (by norm_num [i2036, i56, i1430, RationalInterval.mul])

def n2037 (b : ℝ) : ℝ := (n2035 b) + (n2036 b)
def i2037 : RationalInterval := ⟨(-4234484888377805576369562297917 / 1000000000000000000000000000000 : ℚ), (-4234483529076504436757671214891 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2037 (b : ℝ) (hb : rootInterval.Contains b) : i2037.Contains (n2037 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2035 b hb) (b2036 b hb))
    (by norm_num [i2037, i2035, i2036, RationalInterval.add]) (by norm_num [i2037, i2035, i2036, RationalInterval.add])

def n2038 (b : ℝ) : ℝ := (n324 b) * (n1467 b)
def i2038 : RationalInterval := ⟨(-271742093620608736474259219509 / 1000000000000000000000000000000 : ℚ), (-135871014754833563030727368469 / 500000000000000000000000000000 : ℚ)⟩
theorem b2038 (b : ℝ) (hb : rootInterval.Contains b) : i2038.Contains (n2038 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b324 b hb) (b1467 b hb))
    (by norm_num [i2038, i324, i1467, RationalInterval.mul]) (by norm_num [i2038, i324, i1467, RationalInterval.mul])

def n2039 (b : ℝ) : ℝ := (n2037 b) + (n2038 b)
def i2039 : RationalInterval := ⟨(-2253113490999207156421910758713 / 500000000000000000000000000000 : ℚ), (-4506225558586171562819125951829 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2039 (b : ℝ) (hb : rootInterval.Contains b) : i2039.Contains (n2039 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2037 b hb) (b2038 b hb))
    (by norm_num [i2039, i2037, i2038, RationalInterval.add]) (by norm_num [i2039, i2037, i2038, RationalInterval.add])

def n2040 (b : ℝ) : ℝ := (n1480 b) * (n1345 b)
def i2040 : RationalInterval := ⟨(-295516189081270530556346008227 / 125000000000000000000000000000 : ℚ), (-11820647405436118287360731577 / 5000000000000000000000000000 : ℚ)⟩
theorem b2040 (b : ℝ) (hb : rootInterval.Contains b) : i2040.Contains (n2040 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1480 b hb) (b1345 b hb))
    (by norm_num [i2040, i1480, i1345, RationalInterval.mul]) (by norm_num [i2040, i1480, i1345, RationalInterval.mul])

def n2041 (b : ℝ) : ℝ := (n1626 b) * (n1345 b)
def i2041 : RationalInterval := ⟨(-617691408969908199211955310233 / 50000000000000000000000000000 : ℚ), (-3088457024158039304278656548997 / 250000000000000000000000000000 : ℚ)⟩
theorem b2041 (b : ℝ) (hb : rootInterval.Contains b) : i2041.Contains (n2041 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1626 b hb) (b1345 b hb))
    (by norm_num [i2041, i1626, i1345, RationalInterval.mul]) (by norm_num [i2041, i1626, i1345, RationalInterval.mul])

def n2042 (b : ℝ) : ℝ := (n2040 b) + (n2041 b)
def i2042 : RationalInterval := ⟨(-3679489423012082057172468567619 / 250000000000000000000000000000 : ℚ), (-3679489394429845218646693127847 / 250000000000000000000000000000 : ℚ)⟩
theorem b2042 (b : ℝ) (hb : rootInterval.Contains b) : i2042.Contains (n2042 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2040 b hb) (b2041 b hb))
    (by norm_num [i2042, i2040, i2041, RationalInterval.add]) (by norm_num [i2042, i2040, i2041, RationalInterval.add])

def n2043 (b : ℝ) : ℝ := (n56 b) * (n1435 b)
def i2043 : RationalInterval := ⟨(8589419908165794681523637457349 / 1000000000000000000000000000000 : ℚ), (8589421445999384092712148600207 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2043 (b : ℝ) (hb : rootInterval.Contains b) : i2043.Contains (n2043 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b56 b hb) (b1435 b hb))
    (by norm_num [i2043, i56, i1435, RationalInterval.mul]) (by norm_num [i2043, i56, i1435, RationalInterval.mul])

def n2044 (b : ℝ) : ℝ := (n2042 b) + (n2043 b)
def i2044 : RationalInterval := ⟨(-6128537783882533547166236813127 / 1000000000000000000000000000000 : ℚ), (-6128536131719996781874623911181 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2044 (b : ℝ) (hb : rootInterval.Contains b) : i2044.Contains (n2044 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2042 b hb) (b2043 b hb))
    (by norm_num [i2044, i2042, i2043, RationalInterval.add]) (by norm_num [i2044, i2042, i2043, RationalInterval.add])

def n2045 (b : ℝ) : ℝ := (n324 b) * (n1472 b)
def i2045 : RationalInterval := ⟨(-542409878192733424726437458581 / 1000000000000000000000000000000 : ℚ), (-135602449428838010509473668221 / 250000000000000000000000000000 : ℚ)⟩
theorem b2045 (b : ℝ) (hb : rootInterval.Contains b) : i2045.Contains (n2045 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b324 b hb) (b1472 b hb))
    (by norm_num [i2045, i324, i1472, RationalInterval.mul]) (by norm_num [i2045, i324, i1472, RationalInterval.mul])

def n2046 (b : ℝ) : ℝ := (n2044 b) + (n2045 b)
def i2046 : RationalInterval := ⟨(-1667736915518816742973168567927 / 250000000000000000000000000000 : ℚ), (-1334189185887069764782503716813 / 200000000000000000000000000000 : ℚ)⟩
theorem b2046 (b : ℝ) (hb : rootInterval.Contains b) : i2046.Contains (n2046 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2044 b hb) (b2045 b hb))
    (by norm_num [i2046, i2044, i2045, RationalInterval.add]) (by norm_num [i2046, i2044, i2045, RationalInterval.add])

def n2047 (b : ℝ) : ℝ := (n1614 b) * (n1333 b)
def i2047 : RationalInterval := ⟨(407593164966735220092495894121 / 200000000000000000000000000000 : ℚ), (1018983520024107939159481142177 / 500000000000000000000000000000 : ℚ)⟩
theorem b2047 (b : ℝ) (hb : rootInterval.Contains b) : i2047.Contains (n2047 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1614 b hb) (b1333 b hb))
    (by norm_num [i2047, i1614, i1333, RationalInterval.mul]) (by norm_num [i2047, i1614, i1333, RationalInterval.mul])

def n2048 (b : ℝ) : ℝ := (n1725 b) * (n1350 b)
def i2048 : RationalInterval := ⟨(3612865332221674602591803038937 / 500000000000000000000000000000 : ℚ), (722573423727337500765346511949 / 100000000000000000000000000000 : ℚ)⟩
theorem b2048 (b : ℝ) (hb : rootInterval.Contains b) : i2048.Contains (n2048 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1725 b hb) (b1350 b hb))
    (by norm_num [i2048, i1725, i1350, RationalInterval.mul]) (by norm_num [i2048, i1725, i1350, RationalInterval.mul])

def n2049 (b : ℝ) : ℝ := (n2047 b) + (n2048 b)
def i2049 : RationalInterval := ⟨(9263696489277025305646085548479 / 1000000000000000000000000000000 : ℚ), (2315925319330397721493106850961 / 250000000000000000000000000000 : ℚ)⟩
theorem b2049 (b : ℝ) (hb : rootInterval.Contains b) : i2049.Contains (n2049 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2047 b hb) (b2048 b hb))
    (by norm_num [i2049, i2047, i2048, RationalInterval.add]) (by norm_num [i2049, i2047, i2048, RationalInterval.add])

def n2050 (b : ℝ) : ℝ := (n1805 b) * (n1370 b)
def i2050 : RationalInterval := ⟨(958686768326964553197302373661 / 125000000000000000000000000000 : ℚ), (76694997022766245549281023867 / 10000000000000000000000000000 : ℚ)⟩
theorem b2050 (b : ℝ) (hb : rootInterval.Contains b) : i2050.Contains (n2050 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1805 b hb) (b1370 b hb))
    (by norm_num [i2050, i1805, i1370, RationalInterval.mul]) (by norm_num [i2050, i1805, i1370, RationalInterval.mul])

def n2051 (b : ℝ) : ℝ := (n2049 b) + (n2050 b)
def i2051 : RationalInterval := ⟨(16933190635892741731224504537767 / 1000000000000000000000000000000 : ℚ), (1058325061224888465056283111909 / 62500000000000000000000000000 : ℚ)⟩
theorem b2051 (b : ℝ) (hb : rootInterval.Contains b) : i2051.Contains (n2051 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2049 b hb) (b2050 b hb))
    (by norm_num [i2051, i2049, i2050, RationalInterval.add]) (by norm_num [i2051, i2049, i2050, RationalInterval.add])

def n2052 (b : ℝ) : ℝ := (n1902 b) * (n1407 b)
def i2052 : RationalInterval := ⟨(-4620968812326275578684712658317 / 500000000000000000000000000000 : ℚ), (-4620965167623572946035325672961 / 500000000000000000000000000000 : ℚ)⟩
theorem b2052 (b : ℝ) (hb : rootInterval.Contains b) : i2052.Contains (n2052 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1902 b hb) (b1407 b hb))
    (by norm_num [i2052, i1902, i1407, RationalInterval.mul]) (by norm_num [i2052, i1902, i1407, RationalInterval.mul])

def n2053 (b : ℝ) : ℝ := (n2051 b) + (n2052 b)
def i2053 : RationalInterval := ⟨(7691253011240190573855079221133 / 1000000000000000000000000000000 : ℚ), (3845635322175534774414939222311 / 500000000000000000000000000000 : ℚ)⟩
theorem b2053 (b : ℝ) (hb : rootInterval.Contains b) : i2053.Contains (n2053 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2051 b hb) (b2052 b hb))
    (by norm_num [i2053, i2051, i2052, RationalInterval.add]) (by norm_num [i2053, i2051, i2052, RationalInterval.add])

def n2054 (b : ℝ) : ℝ := (n1967 b) * (n1444 b)
def i2054 : RationalInterval := ⟨(36153346476233315656859387183 / 15625000000000000000000000000 : ℚ), (144613508781641799946254791239 / 62500000000000000000000000000 : ℚ)⟩
theorem b2054 (b : ℝ) (hb : rootInterval.Contains b) : i2054.Contains (n2054 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1967 b hb) (b1444 b hb))
    (by norm_num [i2054, i1967, i1444, RationalInterval.mul]) (by norm_num [i2054, i1967, i1444, RationalInterval.mul])

def n2055 (b : ℝ) : ℝ := (n2053 b) + (n2054 b)
def i2055 : RationalInterval := ⟨(2001013437143824555178816000169 / 200000000000000000000000000000 : ℚ), (5002543392428669173984977552223 / 500000000000000000000000000000 : ℚ)⟩
theorem b2055 (b : ℝ) (hb : rootInterval.Contains b) : i2055.Contains (n2055 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2053 b hb) (b2054 b hb))
    (by norm_num [i2055, i2053, i2054, RationalInterval.add]) (by norm_num [i2055, i2053, i2054, RationalInterval.add])

def n2056 (b : ℝ) : ℝ := (n1614 b) * (n1338 b)
def i2056 : RationalInterval := ⟨(11849558525894399548474712838849 / 1000000000000000000000000000000 : ℚ), (370298867768595422482659165929 / 31250000000000000000000000000 : ℚ)⟩
theorem b2056 (b : ℝ) (hb : rootInterval.Contains b) : i2056.Contains (n2056 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1614 b hb) (b1338 b hb))
    (by norm_num [i2056, i1614, i1338, RationalInterval.mul]) (by norm_num [i2056, i1614, i1338, RationalInterval.mul])

def n2057 (b : ℝ) : ℝ := (n1725 b) * (n1355 b)
def i2057 : RationalInterval := ⟨(8196694427501058640239465992999 / 1000000000000000000000000000000 : ℚ), (2049174640143726450806417211217 / 250000000000000000000000000000 : ℚ)⟩
theorem b2057 (b : ℝ) (hb : rootInterval.Contains b) : i2057.Contains (n2057 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1725 b hb) (b1355 b hb))
    (by norm_num [i2057, i1725, i1355, RationalInterval.mul]) (by norm_num [i2057, i1725, i1355, RationalInterval.mul])

def n2058 (b : ℝ) : ℝ := (n2056 b) + (n2057 b)
def i2058 : RationalInterval := ⟨(2505781619174432273589272353981 / 125000000000000000000000000000 : ℚ), (5011565582292489830667690538649 / 250000000000000000000000000000 : ℚ)⟩
theorem b2058 (b : ℝ) (hb : rootInterval.Contains b) : i2058.Contains (n2058 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2056 b hb) (b2057 b hb))
    (by norm_num [i2058, i2056, i2057, RationalInterval.add]) (by norm_num [i2058, i2056, i2057, RationalInterval.add])

def n2059 (b : ℝ) : ℝ := (n1805 b) * (n1379 b)
def i2059 : RationalInterval := ⟨(22141776985768762824341610489689 / 1000000000000000000000000000000 : ℚ), (22141794442626841172086393555861 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2059 (b : ℝ) (hb : rootInterval.Contains b) : i2059.Contains (n2059 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1805 b hb) (b1379 b hb))
    (by norm_num [i2059, i1805, i1379, RationalInterval.mul]) (by norm_num [i2059, i1805, i1379, RationalInterval.mul])

def n2060 (b : ℝ) : ℝ := (n2058 b) + (n2059 b)
def i2060 : RationalInterval := ⟨(42188029939164221013055789321537 / 1000000000000000000000000000000 : ℚ), (42188056771796800494757155710457 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2060 (b : ℝ) (hb : rootInterval.Contains b) : i2060.Contains (n2060 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2058 b hb) (b2059 b hb))
    (by norm_num [i2060, i2058, i2059, RationalInterval.add]) (by norm_num [i2060, i2058, i2059, RationalInterval.add])

def n2061 (b : ℝ) : ℝ := (n1902 b) * (n1416 b)
def i2061 : RationalInterval := ⟨(-14111720896295439455092071041769 / 500000000000000000000000000000 : ℚ), (-28223419787494516870920550238793 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2061 (b : ℝ) (hb : rootInterval.Contains b) : i2061.Contains (n2061 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1902 b hb) (b1416 b hb))
    (by norm_num [i2061, i1902, i1416, RationalInterval.mul]) (by norm_num [i2061, i1902, i1416, RationalInterval.mul])

def n2062 (b : ℝ) : ℝ := (n2060 b) + (n2061 b)
def i2062 : RationalInterval := ⟨(13964588146573342102871647237999 / 1000000000000000000000000000000 : ℚ), (872789811518892726489787841979 / 62500000000000000000000000000 : ℚ)⟩
theorem b2062 (b : ℝ) (hb : rootInterval.Contains b) : i2062.Contains (n2062 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2060 b hb) (b2061 b hb))
    (by norm_num [i2062, i2060, i2061, RationalInterval.add]) (by norm_num [i2062, i2060, i2061, RationalInterval.add])

def n2063 (b : ℝ) : ℝ := (n1967 b) * (n1453 b)
def i2063 : RationalInterval := ⟨(7314151296396072624392570959909 / 1000000000000000000000000000000 : ℚ), (7314156884260415013148843699299 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2063 (b : ℝ) (hb : rootInterval.Contains b) : i2063.Contains (n2063 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1967 b hb) (b1453 b hb))
    (by norm_num [i2063, i1967, i1453, RationalInterval.mul]) (by norm_num [i2063, i1967, i1453, RationalInterval.mul])

def n2064 (b : ℝ) : ℝ := (n2062 b) + (n2063 b)
def i2064 : RationalInterval := ⟨(5319684860742353681816054549477 / 250000000000000000000000000000 : ℚ), (21278793868562698636985449170963 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2064 (b : ℝ) (hb : rootInterval.Contains b) : i2064.Contains (n2064 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2062 b hb) (b2063 b hb))
    (by norm_num [i2064, i2062, i2063, RationalInterval.add]) (by norm_num [i2064, i2062, i2063, RationalInterval.add])

def n2065 (b : ℝ) : ℝ := (n1614 b) * (n1341 b)
def i2065 : RationalInterval := ⟨(-8275985353349446379167011819571 / 250000000000000000000000000000 : ℚ), (-33103928071352650903589894445723 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2065 (b : ℝ) (hb : rootInterval.Contains b) : i2065.Contains (n2065 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1614 b hb) (b1341 b hb))
    (by norm_num [i2065, i1614, i1341, RationalInterval.mul]) (by norm_num [i2065, i1614, i1341, RationalInterval.mul])

def n2066 (b : ℝ) : ℝ := (n1725 b) * (n1358 b)
def i2066 : RationalInterval := ⟨(-65406950900575464779656315280059 / 1000000000000000000000000000000 : ℚ), (-65406923591076371698273164646511 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2066 (b : ℝ) (hb : rootInterval.Contains b) : i2066.Contains (n2066 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1725 b hb) (b1358 b hb))
    (by norm_num [i2066, i1725, i1358, RationalInterval.mul]) (by norm_num [i2066, i1725, i1358, RationalInterval.mul])

def n2067 (b : ℝ) : ℝ := (n2065 b) + (n2066 b)
def i2067 : RationalInterval := ⟨(-98510892313973250296324362558343 / 1000000000000000000000000000000 : ℚ), (-49255425831214511300931529546117 / 500000000000000000000000000000 : ℚ)⟩
theorem b2067 (b : ℝ) (hb : rootInterval.Contains b) : i2067.Contains (n2067 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2065 b hb) (b2066 b hb))
    (by norm_num [i2067, i2065, i2066, RationalInterval.add]) (by norm_num [i2067, i2065, i2066, RationalInterval.add])

def n2068 (b : ℝ) : ℝ := (n1805 b) * (n1386 b)
def i2068 : RationalInterval := ⟨(-22107580467142944875521932701141 / 250000000000000000000000000000 : ℚ), (-88430297957792064145508995732033 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2068 (b : ℝ) (hb : rootInterval.Contains b) : i2068.Contains (n2068 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1805 b hb) (b1386 b hb))
    (by norm_num [i2068, i1805, i1386, RationalInterval.mul]) (by norm_num [i2068, i1805, i1386, RationalInterval.mul])

def n2069 (b : ℝ) : ℝ := (n2067 b) + (n2068 b)
def i2069 : RationalInterval := ⟨(-186941214182545029798412093362907 / 1000000000000000000000000000000 : ℚ), (-186941149620221086747372054824267 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2069 (b : ℝ) (hb : rootInterval.Contains b) : i2069.Contains (n2069 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2067 b hb) (b2068 b hb))
    (by norm_num [i2069, i2067, i2068, RationalInterval.add]) (by norm_num [i2069, i2067, i2068, RationalInterval.add])

