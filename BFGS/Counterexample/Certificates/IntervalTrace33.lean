import BFGS.Counterexample.Certificates.IntervalTrace32

/-! Generated arithmetic proofs. Each bound is checked by the Lean kernel. -/
namespace BFGS.Counterexample.Trace
noncomputable section
open BFGS RationalInterval
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false

def n2970 (b : ℝ) : ℝ := (n2967 b) + (n2969 b)
def i2970 : RationalInterval := ⟨(130119164990518154935744672395323 / 500000000000000000000000000000 : ℚ), (260599024008240983665392140766749 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2970 (b : ℝ) (hb : rootInterval.Contains b) : i2970.Contains (n2970 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2967 b hb) (b2969 b hb))
    (by norm_num [i2970, i2967, i2969, RationalInterval.add]) (by norm_num [i2970, i2967, i2969, RationalInterval.add])

def n2971 (b : ℝ) : ℝ := (n2917 b) * (n2960 b)
def i2971 : RationalInterval := ⟨(24824221051181142210941657492277 / 12500000000000000000000000000 : ℚ), (31031827693147174556392170023843 / 15625000000000000000000000000 : ℚ)⟩
theorem b2971 (b : ℝ) (hb : rootInterval.Contains b) : i2971.Contains (n2971 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2917 b hb) (b2960 b hb))
    (by norm_num [i2971, i2917, i2960, RationalInterval.mul]) (by norm_num [i2971, i2917, i2960, RationalInterval.mul])

def n2972 (b : ℝ) : ℝ := (n2929 b) * (n2962 b)
def i2972 : RationalInterval := ⟨(-4582621743502831578500290174216257 / 1000000000000000000000000000000 : ℚ), (-458242128624907646541032968774407 / 100000000000000000000000000000 : ℚ)⟩
theorem b2972 (b : ℝ) (hb : rootInterval.Contains b) : i2972.Contains (n2972 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2929 b hb) (b2962 b hb))
    (by norm_num [i2972, i2929, i2962, RationalInterval.mul]) (by norm_num [i2972, i2929, i2962, RationalInterval.mul])

def n2973 (b : ℝ) : ℝ := (n2971 b) + (n2972 b)
def i2973 : RationalInterval := ⟨(-2596684059408340201624957574834097 / 1000000000000000000000000000000 : ℚ), (-1298192156943828646900615403109059 / 500000000000000000000000000000 : ℚ)⟩
theorem b2973 (b : ℝ) (hb : rootInterval.Contains b) : i2973.Contains (n2973 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2971 b hb) (b2972 b hb))
    (by norm_num [i2973, i2971, i2972, RationalInterval.add]) (by norm_num [i2973, i2971, i2972, RationalInterval.add])

def n2974 (b : ℝ) : ℝ := (n2941 b) * (n2965 b)
def i2974 : RationalInterval := ⟨(2800269259448113385832095652351441 / 1000000000000000000000000000000 : ℚ), (1400329752752129778272513425991259 / 500000000000000000000000000000 : ℚ)⟩
theorem b2974 (b : ℝ) (hb : rootInterval.Contains b) : i2974.Contains (n2974 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2941 b hb) (b2965 b hb))
    (by norm_num [i2974, i2941, i2965, RationalInterval.mul]) (by norm_num [i2974, i2941, i2965, RationalInterval.mul])

def n2975 (b : ℝ) : ℝ := (n2973 b) + (n2974 b)
def i2975 : RationalInterval := ⟨(6362037501242912006473064922417 / 31250000000000000000000000000 : ℚ), (510687979041505656859490114411 / 2500000000000000000000000000 : ℚ)⟩
theorem b2975 (b : ℝ) (hb : rootInterval.Contains b) : i2975.Contains (n2975 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2973 b hb) (b2974 b hb))
    (by norm_num [i2975, i2973, i2974, RationalInterval.add]) (by norm_num [i2975, i2973, i2974, RationalInterval.add])

def n2976 (b : ℝ) : ℝ := (n2953 b) * (n2968 b)
def i2976 : RationalInterval := ⟨(42573537401146348807786181421781 / 125000000000000000000000000000 : ℚ), (85182330428021950621539631517389 / 250000000000000000000000000000 : ℚ)⟩
theorem b2976 (b : ℝ) (hb : rootInterval.Contains b) : i2976.Contains (n2976 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2953 b hb) (b2968 b hb))
    (by norm_num [i2976, i2953, i2968, RationalInterval.mul]) (by norm_num [i2976, i2953, i2968, RationalInterval.mul])

def n2977 (b : ℝ) : ℝ := (n2975 b) + (n2976 b)
def i2977 : RationalInterval := ⟨(68021687406117996833678441111449 / 125000000000000000000000000000 : ℚ), (136251128332172516307488642958489 / 250000000000000000000000000000 : ℚ)⟩
theorem b2977 (b : ℝ) (hb : rootInterval.Contains b) : i2977.Contains (n2977 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2975 b hb) (b2976 b hb))
    (by norm_num [i2977, i2975, i2976, RationalInterval.add]) (by norm_num [i2977, i2975, i2976, RationalInterval.add])

def n2978 (b : ℝ) : ℝ := (n2920 b) * (n2960 b)
def i2978 : RationalInterval := ⟨(260833136670678255603326136117793 / 62500000000000000000000000000 : ℚ), (260843879243709800357963385887811 / 62500000000000000000000000000 : ℚ)⟩
theorem b2978 (b : ℝ) (hb : rootInterval.Contains b) : i2978.Contains (n2978 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2920 b hb) (b2960 b hb))
    (by norm_num [i2978, i2920, i2960, RationalInterval.mul]) (by norm_num [i2978, i2920, i2960, RationalInterval.mul])

def n2979 (b : ℝ) : ℝ := (n2932 b) * (n2962 b)
def i2979 : RationalInterval := ⟨(-12602873631842819808600760237128831 / 1000000000000000000000000000000 : ℚ), (-12602449037748661856737553547084159 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2979 (b : ℝ) (hb : rootInterval.Contains b) : i2979.Contains (n2979 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2932 b hb) (b2962 b hb))
    (by norm_num [i2979, i2932, i2962, RationalInterval.mul]) (by norm_num [i2979, i2932, i2962, RationalInterval.mul])

def n2980 (b : ℝ) : ℝ := (n2978 b) + (n2979 b)
def i2980 : RationalInterval := ⟨(-8429543445111967718947542059244143 / 1000000000000000000000000000000 : ℚ), (-8428946969849305051010139372879183 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2980 (b : ℝ) (hb : rootInterval.Contains b) : i2980.Contains (n2980 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2978 b hb) (b2979 b hb))
    (by norm_num [i2980, i2978, i2979, RationalInterval.add]) (by norm_num [i2980, i2978, i2979, RationalInterval.add])

def n2981 (b : ℝ) : ℝ := (n2944 b) * (n2965 b)
def i2981 : RationalInterval := ⟨(4702872399991424869370951071630517 / 500000000000000000000000000000 : ℚ), (9406605154925195401122582475044367 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2981 (b : ℝ) (hb : rootInterval.Contains b) : i2981.Contains (n2981 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2944 b hb) (b2965 b hb))
    (by norm_num [i2981, i2944, i2965, RationalInterval.mul]) (by norm_num [i2981, i2944, i2965, RationalInterval.mul])

def n2982 (b : ℝ) : ℝ := (n2980 b) + (n2981 b)
def i2982 : RationalInterval := ⟨(976201354870882019794360084016891 / 1000000000000000000000000000000 : ℚ), (15275909141810786720506923471331 / 15625000000000000000000000000 : ℚ)⟩
theorem b2982 (b : ℝ) (hb : rootInterval.Contains b) : i2982.Contains (n2982 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2980 b hb) (b2981 b hb))
    (by norm_num [i2982, i2980, i2981, RationalInterval.add]) (by norm_num [i2982, i2980, i2981, RationalInterval.add])

def n2983 (b : ℝ) : ℝ := (n2956 b) * (n2968 b)
def i2983 : RationalInterval := ⟨(64534782372568242658966198212147 / 62500000000000000000000000000 : ℚ), (51641485629834357333853078019417 / 50000000000000000000000000000 : ℚ)⟩
theorem b2983 (b : ℝ) (hb : rootInterval.Contains b) : i2983.Contains (n2983 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2956 b hb) (b2968 b hb))
    (by norm_num [i2983, i2956, i2968, RationalInterval.mul]) (by norm_num [i2983, i2956, i2968, RationalInterval.mul])

def n2984 (b : ℝ) : ℝ := (n2982 b) + (n2983 b)
def i2984 : RationalInterval := ⟨(2008757872831973902337819255411243 / 1000000000000000000000000000000 : ℚ), (502621974418144374197376165638381 / 250000000000000000000000000000 : ℚ)⟩
theorem b2984 (b : ℝ) (hb : rootInterval.Contains b) : i2984.Contains (n2984 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2982 b hb) (b2983 b hb))
    (by norm_num [i2984, i2982, i2983, RationalInterval.add]) (by norm_num [i2984, i2982, i2983, RationalInterval.add])

def n2985 (b : ℝ) : ℝ := (n2923 b) * (n2960 b)
def i2985 : RationalInterval := ⟨(593838384262827437402897184373637 / 62500000000000000000000000000 : ℚ), (593853360440330981458235150920727 / 62500000000000000000000000000 : ℚ)⟩
theorem b2985 (b : ℝ) (hb : rootInterval.Contains b) : i2985.Contains (n2985 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2923 b hb) (b2960 b hb))
    (by norm_num [i2985, i2923, i2960, RationalInterval.mul]) (by norm_num [i2985, i2923, i2960, RationalInterval.mul])

def n2986 (b : ℝ) : ℝ := (n2935 b) * (n2962 b)
def i2986 : RationalInterval := ⟨(-18724741292797946932676665266119349 / 1000000000000000000000000000000 : ℚ), (-2340517536401895230219490154403229 / 125000000000000000000000000000 : ℚ)⟩
theorem b2986 (b : ℝ) (hb : rootInterval.Contains b) : i2986.Contains (n2986 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2935 b hb) (b2962 b hb))
    (by norm_num [i2986, i2935, i2962, RationalInterval.mul]) (by norm_num [i2986, i2935, i2962, RationalInterval.mul])

def n2987 (b : ℝ) : ℝ := (n2985 b) + (n2986 b)
def i2987 : RationalInterval := ⟨(-9223327144592707934230310316141157 / 1000000000000000000000000000000 : ℚ), (-46112432620849330692120794102471 / 5000000000000000000000000000 : ℚ)⟩
theorem b2987 (b : ℝ) (hb : rootInterval.Contains b) : i2987.Contains (n2987 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2985 b hb) (b2986 b hb))
    (by norm_num [i2987, i2985, i2986, RationalInterval.add]) (by norm_num [i2987, i2985, i2986, RationalInterval.add])

def n2988 (b : ℝ) : ℝ := (n2947 b) * (n2965 b)
def i2988 : RationalInterval := ⟨(1874380363611381189373591164360117 / 200000000000000000000000000000 : ℚ), (4686562200073411491992337305599053 / 500000000000000000000000000000 : ℚ)⟩
theorem b2988 (b : ℝ) (hb : rootInterval.Contains b) : i2988.Contains (n2988 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2947 b hb) (b2965 b hb))
    (by norm_num [i2988, i2947, i2965, RationalInterval.mul]) (by norm_num [i2988, i2947, i2965, RationalInterval.mul])

def n2989 (b : ℝ) : ℝ := (n2987 b) + (n2988 b)
def i2989 : RationalInterval := ⟨(37143668366049503159411376414857 / 250000000000000000000000000000 : ℚ), (75318937988478422780257895351953 / 500000000000000000000000000000 : ℚ)⟩
theorem b2989 (b : ℝ) (hb : rootInterval.Contains b) : i2989.Contains (n2989 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2987 b hb) (b2988 b hb))
    (by norm_num [i2989, i2987, i2988, RationalInterval.add]) (by norm_num [i2989, i2987, i2988, RationalInterval.add])

def n2990 (b : ℝ) : ℝ := (n2959 b) * (n2968 b)
def i2990 : RationalInterval := ⟨(-10918918280859158174909558847523 / 50000000000000000000000000000 : ℚ), (-54499072407570790735159189047807 / 250000000000000000000000000000 : ℚ)⟩
theorem b2990 (b : ℝ) (hb : rootInterval.Contains b) : i2990.Contains (n2990 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2959 b hb) (b2968 b hb))
    (by norm_num [i2990, i2959, i2968, RationalInterval.mul]) (by norm_num [i2990, i2959, i2968, RationalInterval.mul])

def n2991 (b : ℝ) : ℝ := (n2989 b) + (n2990 b)
def i2991 : RationalInterval := ⟨(-8725461519123143857568208911379 / 125000000000000000000000000000 : ℚ), (-33679206826663158690060482743661 / 500000000000000000000000000000 : ℚ)⟩
theorem b2991 (b : ℝ) (hb : rootInterval.Contains b) : i2991.Contains (n2991 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2989 b hb) (b2990 b hb))
    (by norm_num [i2991, i2989, i2990, RationalInterval.add]) (by norm_num [i2991, i2989, i2990, RationalInterval.add])

def n2992 (b : ℝ) : ℝ := ((1366 : ℚ) : ℝ)
def i2992 : RationalInterval := ⟨(1366 : ℚ), (1366 : ℚ)⟩
theorem b2992 (b : ℝ) (hb : rootInterval.Contains b) : i2992.Contains (n2992 b) := by
  exact RationalInterval.contains_point (1366 : ℚ)

def n2993 (b : ℝ) : ℝ := (n2914 b) * (n2992 b)
def i2993 : RationalInterval := ⟨(2166949174190214411906558607404367 / 500000000000000000000000000000 : ℚ), (541752293354636393688836799789739 / 125000000000000000000000000000 : ℚ)⟩
theorem b2993 (b : ℝ) (hb : rootInterval.Contains b) : i2993.Contains (n2993 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2914 b hb) (b2992 b hb))
    (by norm_num [i2993, i2914, i2992, RationalInterval.mul]) (by norm_num [i2993, i2914, i2992, RationalInterval.mul])

def n2994 (b : ℝ) : ℝ := ((2793 : ℚ) : ℝ)
def i2994 : RationalInterval := ⟨(2793 : ℚ), (2793 : ℚ)⟩
theorem b2994 (b : ℝ) (hb : rootInterval.Contains b) : i2994.Contains (n2994 b) := by
  exact RationalInterval.contains_point (2793 : ℚ)

def n2995 (b : ℝ) : ℝ := (n2926 b) * (n2994 b)
def i2995 : RationalInterval := ⟨(-6233174656267351033883725132121247 / 1000000000000000000000000000000 : ℚ), (-623294722810657313526148249532643 / 100000000000000000000000000000 : ℚ)⟩
theorem b2995 (b : ℝ) (hb : rootInterval.Contains b) : i2995.Contains (n2995 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2926 b hb) (b2994 b hb))
    (by norm_num [i2995, i2926, i2994, RationalInterval.mul]) (by norm_num [i2995, i2926, i2994, RationalInterval.mul])

def n2996 (b : ℝ) : ℝ := (n2993 b) + (n2995 b)
def i2996 : RationalInterval := ⟨(-1899276307886922210070607917312513 / 1000000000000000000000000000000 : ℚ), (-949464440634740992875394048504259 / 500000000000000000000000000000 : ℚ)⟩
theorem b2996 (b : ℝ) (hb : rootInterval.Contains b) : i2996.Contains (n2996 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2993 b hb) (b2995 b hb))
    (by norm_num [i2996, i2993, i2995, RationalInterval.add]) (by norm_num [i2996, i2993, i2995, RationalInterval.add])

def n2997 (b : ℝ) : ℝ := ((10000 : ℚ) : ℝ)
def i2997 : RationalInterval := ⟨(10000 : ℚ), (10000 : ℚ)⟩
theorem b2997 (b : ℝ) (hb : rootInterval.Contains b) : i2997.Contains (n2997 b) := by
  exact RationalInterval.contains_point (10000 : ℚ)

def n2998 (b : ℝ) : ℝ := (n2938 b) * (n2997 b)
def i2998 : RationalInterval := ⟨(203413378925366471388602214841 / 100000000000000000000000000 : ℚ), (203451739552764802503227509047 / 100000000000000000000000000 : ℚ)⟩
theorem b2998 (b : ℝ) (hb : rootInterval.Contains b) : i2998.Contains (n2998 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2938 b hb) (b2997 b hb))
    (by norm_num [i2998, i2938, i2997, RationalInterval.mul]) (by norm_num [i2998, i2938, i2997, RationalInterval.mul])

def n2999 (b : ℝ) : ℝ := (n2996 b) + (n2998 b)
def i2999 : RationalInterval := ⟨(134857481366742503815414231097487 / 1000000000000000000000000000000 : ℚ), (67794257129083019640743496730741 / 500000000000000000000000000000 : ℚ)⟩
theorem b2999 (b : ℝ) (hb : rootInterval.Contains b) : i2999.Contains (n2999 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2996 b hb) (b2998 b hb))
    (by norm_num [i2999, i2996, i2998, RationalInterval.add]) (by norm_num [i2999, i2996, i2998, RationalInterval.add])

def n3000 (b : ℝ) : ℝ := ((552 : ℚ) : ℝ)
def i3000 : RationalInterval := ⟨(552 : ℚ), (552 : ℚ)⟩
theorem b3000 (b : ℝ) (hb : rootInterval.Contains b) : i3000.Contains (n3000 b) := by
  exact RationalInterval.contains_point (552 : ℚ)

def n3001 (b : ℝ) : ℝ := (n2950 b) * (n3000 b)
def i3001 : RationalInterval := ⟨(-1394542458591367009230491361429 / 15625000000000000000000000000 : ℚ), (-11153932984349477332049216838261 / 125000000000000000000000000000 : ℚ)⟩
theorem b3001 (b : ℝ) (hb : rootInterval.Contains b) : i3001.Contains (n3001 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2950 b hb) (b3000 b hb))
    (by norm_num [i3001, i2950, i3000, RationalInterval.mul]) (by norm_num [i3001, i2950, i3000, RationalInterval.mul])

def n3002 (b : ℝ) : ℝ := (n2999 b) + (n3001 b)
def i3002 : RationalInterval := ⟨(45606764016895015224662783966031 / 1000000000000000000000000000000 : ℚ), (23178525191685110312546629377697 / 500000000000000000000000000000 : ℚ)⟩
theorem b3002 (b : ℝ) (hb : rootInterval.Contains b) : i3002.Contains (n3002 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2999 b hb) (b3001 b hb))
    (by norm_num [i3002, i2999, i3001, RationalInterval.add]) (by norm_num [i3002, i2999, i3001, RationalInterval.add])

def n3003 (b : ℝ) : ℝ := (n2917 b) * (n2992 b)
def i3003 : RationalInterval := ⟨(584653206136438625174936278180179 / 100000000000000000000000000000 : ℚ), (730853045324811042138477659527061 / 125000000000000000000000000000 : ℚ)⟩
theorem b3003 (b : ℝ) (hb : rootInterval.Contains b) : i3003.Contains (n3003 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2917 b hb) (b2992 b hb))
    (by norm_num [i3003, i2917, i2992, RationalInterval.mul]) (by norm_num [i3003, i2917, i2992, RationalInterval.mul])

def n3004 (b : ℝ) : ℝ := (n2929 b) * (n2994 b)
def i3004 : RationalInterval := ⟨(-11884180621730184399954791510293413 / 1000000000000000000000000000000 : ℚ), (-1188366077297462448272149565261763 / 100000000000000000000000000000 : ℚ)⟩
theorem b3004 (b : ℝ) (hb : rootInterval.Contains b) : i3004.Contains (n3004 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2929 b hb) (b2994 b hb))
    (by norm_num [i3004, i2929, i2994, RationalInterval.mul]) (by norm_num [i3004, i2929, i2994, RationalInterval.mul])

def n3005 (b : ℝ) : ℝ := (n3003 b) + (n3004 b)
def i3005 : RationalInterval := ⟨(-6037648560365798148205428728491623 / 1000000000000000000000000000000 : ℚ), (-3018418205188068072806837188200571 / 500000000000000000000000000000 : ℚ)⟩
theorem b3005 (b : ℝ) (hb : rootInterval.Contains b) : i3005.Contains (n3005 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3003 b hb) (b3004 b hb))
    (by norm_num [i3005, i3003, i3004, RationalInterval.add]) (by norm_num [i3005, i3003, i3004, RationalInterval.add])

def n3006 (b : ℝ) : ℝ := (n2941 b) * (n2997 b)
def i3006 : RationalInterval := ⟨(622143803476585955528126116941 / 100000000000000000000000000 : ℚ), (311115252777633809880585075759 / 50000000000000000000000000 : ℚ)⟩
theorem b3006 (b : ℝ) (hb : rootInterval.Contains b) : i3006.Contains (n3006 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2941 b hb) (b2997 b hb))
    (by norm_num [i3006, i2941, i2997, RationalInterval.mul]) (by norm_num [i3006, i2941, i2997, RationalInterval.mul])

def n3007 (b : ℝ) : ℝ := (n3005 b) + (n3006 b)
def i3007 : RationalInterval := ⟨(183789474400061407075832440918377 / 1000000000000000000000000000000 : ℚ), (92734322588270025999013569389429 / 500000000000000000000000000000 : ℚ)⟩
theorem b3007 (b : ℝ) (hb : rootInterval.Contains b) : i3007.Contains (n3007 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3005 b hb) (b3006 b hb))
    (by norm_num [i3007, i3005, i3006, RationalInterval.add]) (by norm_num [i3007, i3005, i3006, RationalInterval.add])

def n3008 (b : ℝ) : ℝ := (n2953 b) * (n3000 b)
def i3008 : RationalInterval := ⟨(-13764826228415725041888137177283 / 125000000000000000000000000000 : ℚ), (-6879564591754328027487696763707 / 62500000000000000000000000000 : ℚ)⟩
theorem b3008 (b : ℝ) (hb : rootInterval.Contains b) : i3008.Contains (n3008 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2953 b hb) (b3000 b hb))
    (by norm_num [i3008, i2953, i3000, RationalInterval.mul]) (by norm_num [i3008, i2953, i3000, RationalInterval.mul])

def n3009 (b : ℝ) : ℝ := (n3007 b) + (n3008 b)
def i3009 : RationalInterval := ⟨(73670864572735606740727343500113 / 1000000000000000000000000000000 : ℚ), (37697805854235401779111995279773 / 500000000000000000000000000000 : ℚ)⟩
theorem b3009 (b : ℝ) (hb : rootInterval.Contains b) : i3009.Contains (n3009 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3007 b hb) (b3008 b hb))
    (by norm_num [i3009, i3007, i3008, RationalInterval.add]) (by norm_num [i3009, i3007, i3008, RationalInterval.add])

def n3010 (b : ℝ) : ℝ := (n2920 b) * (n2992 b)
def i3010 : RationalInterval := ⟨(6143070080899077537140405205808711 / 500000000000000000000000000000 : ℚ), (6143323087015648056706516984874997 / 500000000000000000000000000000 : ℚ)⟩
theorem b3010 (b : ℝ) (hb : rootInterval.Contains b) : i3010.Contains (n3010 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2920 b hb) (b2992 b hb))
    (by norm_num [i3010, i2920, i2992, RationalInterval.mul]) (by norm_num [i3010, i2920, i2992, RationalInterval.mul])

def n3011 (b : ℝ) : ℝ := (n2932 b) * (n2994 b)
def i3011 : RationalInterval := ⟨(-32683218248595167804477180447818779 / 1000000000000000000000000000000 : ℚ), (-32682117142462407210648084546895131 / 1000000000000000000000000000000 : ℚ)⟩
theorem b3011 (b : ℝ) (hb : rootInterval.Contains b) : i3011.Contains (n3011 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2932 b hb) (b2994 b hb))
    (by norm_num [i3011, i2932, i2994, RationalInterval.mul]) (by norm_num [i3011, i2932, i2994, RationalInterval.mul])

def n3012 (b : ℝ) : ℝ := (n3010 b) + (n3011 b)
def i3012 : RationalInterval := ⟨(-20397078086797012730196370036201357 / 1000000000000000000000000000000 : ℚ), (-20395470968431111097235050577145137 / 1000000000000000000000000000000 : ℚ)⟩
theorem b3012 (b : ℝ) (hb : rootInterval.Contains b) : i3012.Contains (n3012 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3010 b hb) (b3011 b hb))
    (by norm_num [i3012, i3010, i3011, RationalInterval.add]) (by norm_num [i3012, i3010, i3011, RationalInterval.add])

def n3013 (b : ℝ) : ℝ := (n2944 b) * (n2997 b)
def i3013 : RationalInterval := ⟨(1044850566538863556847578554017 / 50000000000000000000000000 : ℚ), (2089892280587690602337832142867 / 100000000000000000000000000 : ℚ)⟩
theorem b3013 (b : ℝ) (hb : rootInterval.Contains b) : i3013.Contains (n3013 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2944 b hb) (b2997 b hb))
    (by norm_num [i3013, i2944, i2997, RationalInterval.mul]) (by norm_num [i3013, i2944, i2997, RationalInterval.mul])

def n3014 (b : ℝ) : ℝ := (n3012 b) + (n3013 b)
def i3014 : RationalInterval := ⟨(499933243980258406755201044138643 / 1000000000000000000000000000000 : ℚ), (503451837445794926143270851524863 / 1000000000000000000000000000000 : ℚ)⟩
theorem b3014 (b : ℝ) (hb : rootInterval.Contains b) : i3014.Contains (n3014 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3012 b hb) (b3013 b hb))
    (by norm_num [i3014, i3012, i3013, RationalInterval.add]) (by norm_num [i3014, i3012, i3013, RationalInterval.add])

def n3015 (b : ℝ) : ℝ := (n2956 b) * (n3000 b)
def i3015 : RationalInterval := ⟨(-8344877068989626829123799492599 / 25000000000000000000000000000 : ℚ), (-10428337198377538040910228750909 / 31250000000000000000000000000 : ℚ)⟩
theorem b3015 (b : ℝ) (hb : rootInterval.Contains b) : i3015.Contains (n3015 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2956 b hb) (b3000 b hb))
    (by norm_num [i3015, i2956, i3000, RationalInterval.mul]) (by norm_num [i3015, i2956, i3000, RationalInterval.mul])

def n3016 (b : ℝ) : ℝ := (n3014 b) + (n3015 b)
def i3016 : RationalInterval := ⟨(166138161220673333590249064434683 / 1000000000000000000000000000000 : ℚ), (6789801883908548353365741259831 / 40000000000000000000000000000 : ℚ)⟩
theorem b3016 (b : ℝ) (hb : rootInterval.Contains b) : i3016.Contains (n3016 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3014 b hb) (b3015 b hb))
    (by norm_num [i3016, i3014, i3015, RationalInterval.add]) (by norm_num [i3016, i3014, i3015, RationalInterval.add])

def n3017 (b : ℝ) : ℝ := (n2923 b) * (n2992 b)
def i3017 : RationalInterval := ⟨(13985917808672797922282026790592899 / 500000000000000000000000000000 : ℚ), (13986270523474002080550848554443329 / 500000000000000000000000000000 : ℚ)⟩
theorem b3017 (b : ℝ) (hb : rootInterval.Contains b) : i3017.Contains (n3017 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2923 b hb) (b2992 b hb))
    (by norm_num [i3017, i2923, i2992, RationalInterval.mul]) (by norm_num [i3017, i2923, i2992, RationalInterval.mul])

def n3018 (b : ℝ) : ℝ := (n2935 b) * (n2994 b)
def i3018 : RationalInterval := ⟨(-48559148032297739817052856163668841 / 1000000000000000000000000000000 : ℚ), (-6069698680752547240485641598187761 / 125000000000000000000000000000 : ℚ)⟩
theorem b3018 (b : ℝ) (hb : rootInterval.Contains b) : i3018.Contains (n3018 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2935 b hb) (b2994 b hb))
    (by norm_num [i3018, i2935, i2994, RationalInterval.mul]) (by norm_num [i3018, i2935, i2994, RationalInterval.mul])

def n3019 (b : ℝ) : ℝ := (n3017 b) + (n3018 b)
def i3019 : RationalInterval := ⟨(-20587312414952143972488802582483043 / 1000000000000000000000000000000 : ℚ), (-2058504839907237376278343567661543 / 100000000000000000000000000000 : ℚ)⟩
theorem b3019 (b : ℝ) (hb : rootInterval.Contains b) : i3019.Contains (n3019 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3017 b hb) (b3018 b hb))
    (by norm_num [i3019, i3017, i3018, RationalInterval.add]) (by norm_num [i3019, i3017, i3018, RationalInterval.add])

def n3020 (b : ℝ) : ℝ := (n2947 b) * (n2997 b)
def i3020 : RationalInterval := ⟨(416436428262915172044788083617 / 20000000000000000000000000 : ℚ), (1041226882931217838700808110553 / 50000000000000000000000000 : ℚ)⟩
theorem b3020 (b : ℝ) (hb : rootInterval.Contains b) : i3020.Contains (n3020 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2947 b hb) (b2997 b hb))
    (by norm_num [i3020, i2947, i2997, RationalInterval.mul]) (by norm_num [i3020, i2947, i2997, RationalInterval.mul])

def n3021 (b : ℝ) : ℝ := (n3019 b) + (n3020 b)
def i3021 : RationalInterval := ⟨(234508998193614629750601598366957 / 1000000000000000000000000000000 : ℚ), (23948925955198301123272653444457 / 100000000000000000000000000000 : ℚ)⟩
theorem b3021 (b : ℝ) (hb : rootInterval.Contains b) : i3021.Contains (n3021 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3019 b hb) (b3020 b hb))
    (by norm_num [i3021, i3019, i3020, RationalInterval.add]) (by norm_num [i3021, i3019, i3020, RationalInterval.add])

def n3022 (b : ℝ) : ℝ := (n2959 b) * (n3000 b)
def i3022 : RationalInterval := ⟨(8806641677101603186711906426929 / 125000000000000000000000000000 : ℚ), (1764415366227826496648148853581 / 25000000000000000000000000000 : ℚ)⟩
theorem b3022 (b : ℝ) (hb : rootInterval.Contains b) : i3022.Contains (n3022 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2959 b hb) (b3000 b hb))
    (by norm_num [i3022, i2959, i3000, RationalInterval.mul]) (by norm_num [i3022, i2959, i3000, RationalInterval.mul])

def n3023 (b : ℝ) : ℝ := (n3021 b) + (n3022 b)
def i3023 : RationalInterval := ⟨(304962131610427455244296849782389 / 1000000000000000000000000000000 : ℚ), (31006587420109607109865248858781 / 100000000000000000000000000000 : ℚ)⟩
theorem b3023 (b : ℝ) (hb : rootInterval.Contains b) : i3023.Contains (n3023 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3021 b hb) (b3022 b hb))
    (by norm_num [i3023, i3021, i3022, RationalInterval.add]) (by norm_num [i3023, i3021, i3022, RationalInterval.add])

def n3024 (b : ℝ) : ℝ := ((-448 : ℚ) : ℝ)
def i3024 : RationalInterval := ⟨(-448 : ℚ), (-448 : ℚ)⟩
theorem b3024 (b : ℝ) (hb : rootInterval.Contains b) : i3024.Contains (n3024 b) := by
  exact RationalInterval.contains_point (-448 : ℚ)

def n3025 (b : ℝ) : ℝ := (n2914 b) * (n3024 b)
def i3025 : RationalInterval := ⟨(-5552366110516039173970508929031 / 3906250000000000000000000000 : ℚ), (-22208849515858712859950088216443 / 15625000000000000000000000000 : ℚ)⟩
theorem b3025 (b : ℝ) (hb : rootInterval.Contains b) : i3025.Contains (n3025 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2914 b hb) (b3024 b hb))
    (by norm_num [i3025, i2914, i3024, RationalInterval.mul]) (by norm_num [i3025, i2914, i3024, RationalInterval.mul])

def n3026 (b : ℝ) : ℝ := ((-1058 : ℚ) : ℝ)
def i3026 : RationalInterval := ⟨(-1058 : ℚ), (-1058 : ℚ)⟩
theorem b3026 (b : ℝ) (hb : rootInterval.Contains b) : i3026.Contains (n3026 b) := by
  exact RationalInterval.contains_point (-1058 : ℚ)

def n3027 (b : ℝ) : ℝ := (n2926 b) * (n3026 b)
def i3027 : RationalInterval := ⟨(118053314846701653725503911207579 / 50000000000000000000000000000 : ℚ), (1180576223832949766174182096273591 / 500000000000000000000000000000 : ℚ)⟩
theorem b3027 (b : ℝ) (hb : rootInterval.Contains b) : i3027.Contains (n3027 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2926 b hb) (b3026 b hb))
    (by norm_num [i3027, i2926, i3026, RationalInterval.mul]) (by norm_num [i3027, i2926, i3026, RationalInterval.mul])

def n3028 (b : ℝ) : ℝ := (n3025 b) + (n3027 b)
def i3028 : RationalInterval := ⟨(234915143160481761493406984579911 / 250000000000000000000000000000 : ℚ), (93978607865094190931155854669483 / 100000000000000000000000000000 : ℚ)⟩
theorem b3028 (b : ℝ) (hb : rootInterval.Contains b) : i3028.Contains (n3028 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3025 b hb) (b3027 b hb))
    (by norm_num [i3028, i3025, i3027, RationalInterval.add]) (by norm_num [i3028, i3025, i3027, RationalInterval.add])

def n3029 (b : ℝ) : ℝ := ((-4343 : ℚ) : ℝ)
def i3029 : RationalInterval := ⟨(-4343 : ℚ), (-4343 : ℚ)⟩
theorem b3029 (b : ℝ) (hb : rootInterval.Contains b) : i3029.Contains (n3029 b) := by
  exact RationalInterval.contains_point (-4343 : ℚ)

def n3030 (b : ℝ) : ℝ := (n2938 b) * (n3029 b)
def i3030 : RationalInterval := ⟨(-883590904877657537271517071791121 / 1000000000000000000000000000000 : ℚ), (-883424304672866585240699419054463 / 1000000000000000000000000000000 : ℚ)⟩
theorem b3030 (b : ℝ) (hb : rootInterval.Contains b) : i3030.Contains (n3030 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2938 b hb) (b3029 b hb))
    (by norm_num [i3030, i2938, i3029, RationalInterval.mul]) (by norm_num [i3030, i2938, i3029, RationalInterval.mul])

def n3031 (b : ℝ) : ℝ := (n3028 b) + (n3030 b)
def i3031 : RationalInterval := ⟨(56069667764269508702110866528523 / 1000000000000000000000000000000 : ℚ), (56361773978075324070859127640367 / 1000000000000000000000000000000 : ℚ)⟩
theorem b3031 (b : ℝ) (hb : rootInterval.Contains b) : i3031.Contains (n3031 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3028 b hb) (b3030 b hb))
    (by norm_num [i3031, i3028, i3030, RationalInterval.add]) (by norm_num [i3031, i3028, i3030, RationalInterval.add])

def n3032 (b : ℝ) : ℝ := ((1648 : ℚ) : ℝ)
def i3032 : RationalInterval := ⟨(1648 : ℚ), (1648 : ℚ)⟩
theorem b3032 (b : ℝ) (hb : rootInterval.Contains b) : i3032.Contains (n3032 b) := by
  exact RationalInterval.contains_point (1648 : ℚ)

def n3033 (b : ℝ) : ℝ := (n2950 b) * (n3032 b)
def i3033 : RationalInterval := ⟨(-2081708307752330463054211742423 / 7812500000000000000000000000 : ℚ), (-16650073875188350220305352671607 / 62500000000000000000000000000 : ℚ)⟩
theorem b3033 (b : ℝ) (hb : rootInterval.Contains b) : i3033.Contains (n3033 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2950 b hb) (b3032 b hb))
    (by norm_num [i3033, i2950, i3032, RationalInterval.mul]) (by norm_num [i3033, i2950, i3032, RationalInterval.mul])

def n3034 (b : ℝ) : ℝ := (n3031 b) + (n3033 b)
def i3034 : RationalInterval := ⟨(-210388995628028790568828236501621 / 1000000000000000000000000000000 : ℚ), (-42007881604987655890805303021069 / 200000000000000000000000000000 : ℚ)⟩
theorem b3034 (b : ℝ) (hb : rootInterval.Contains b) : i3034.Contains (n3034 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3031 b hb) (b3033 b hb))
    (by norm_num [i3034, i3031, i3033, RationalInterval.add]) (by norm_num [i3034, i3031, i3033, RationalInterval.add])

def n3035 (b : ℝ) : ℝ := (n2917 b) * (n3024 b)
def i3035 : RationalInterval := ⟨(-7490441167311386961887765178169 / 3906250000000000000000000000 : ℚ), (-5992053357181655016434193187791 / 3125000000000000000000000000 : ℚ)⟩
theorem b3035 (b : ℝ) (hb : rootInterval.Contains b) : i3035.Contains (n3035 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2917 b hb) (b3024 b hb))
    (by norm_num [i3035, i2917, i3024, RationalInterval.mul]) (by norm_num [i3035, i2917, i3024, RationalInterval.mul])

def n3036 (b : ℝ) : ℝ := (n2929 b) * (n3026 b)
def i3036 : RationalInterval := ⟨(225079002825047488412447948450939 / 50000000000000000000000000000 : ℚ), (2250888488684306318501999537753389 / 500000000000000000000000000000 : ℚ)⟩
theorem b3036 (b : ℝ) (hb : rootInterval.Contains b) : i3036.Contains (n3036 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2929 b hb) (b3026 b hb))
    (by norm_num [i3036, i2929, i3026, RationalInterval.mul]) (by norm_num [i3036, i2929, i3026, RationalInterval.mul])

def n3037 (b : ℝ) : ℝ := (n3035 b) + (n3036 b)
def i3037 : RationalInterval := ⟨(646006779417308676501422770851879 / 250000000000000000000000000000 : ℚ), (1292159951535241515872528627706829 / 500000000000000000000000000000 : ℚ)⟩
theorem b3037 (b : ℝ) (hb : rootInterval.Contains b) : i3037.Contains (n3037 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3035 b hb) (b3036 b hb))
    (by norm_num [i3037, i3035, i3036, RationalInterval.add]) (by norm_num [i3037, i3035, i3036, RationalInterval.add])

def n3038 (b : ℝ) : ℝ := (n2941 b) * (n3029 b)
def i3038 : RationalInterval := ⟨(-1351173542813263636311380984021337 / 500000000000000000000000000000 : ℚ), (-2701970538498812804858651725874763 / 1000000000000000000000000000000 : ℚ)⟩
theorem b3038 (b : ℝ) (hb : rootInterval.Contains b) : i3038.Contains (n3038 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2941 b hb) (b3029 b hb))
    (by norm_num [i3038, i2941, i3029, RationalInterval.mul]) (by norm_num [i3038, i2941, i3029, RationalInterval.mul])

def n3039 (b : ℝ) : ℝ := (n3037 b) + (n3038 b)
def i3039 : RationalInterval := ⟨(-59159983978646283308535442317579 / 500000000000000000000000000000 : ℚ), (-23530127085665954622718894092221 / 200000000000000000000000000000 : ℚ)⟩
theorem b3039 (b : ℝ) (hb : rootInterval.Contains b) : i3039.Contains (n3039 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3037 b hb) (b3038 b hb))
    (by norm_num [i3039, i3037, i3038, RationalInterval.add]) (by norm_num [i3039, i3037, i3038, RationalInterval.add])

def n3040 (b : ℝ) : ℝ := (n2953 b) * (n3032 b)
def i3040 : RationalInterval := ⟨(-20547494225026372163977943902321 / 62500000000000000000000000000 : ℚ), (-10269494970299938939583083574809 / 31250000000000000000000000000 : ℚ)⟩
theorem b3040 (b : ℝ) (hb : rootInterval.Contains b) : i3040.Contains (n3040 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2953 b hb) (b3032 b hb))
    (by norm_num [i3040, i2953, i3032, RationalInterval.mul]) (by norm_num [i3040, i2953, i3032, RationalInterval.mul])

def n3041 (b : ℝ) : ℝ := (n3039 b) + (n3040 b)
def i3041 : RationalInterval := ⟨(-223539937778857260620358993536147 / 500000000000000000000000000000 : ℚ), (-446274474477927819180253144854993 / 1000000000000000000000000000000 : ℚ)⟩
theorem b3041 (b : ℝ) (hb : rootInterval.Contains b) : i3041.Contains (n3041 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3039 b hb) (b3040 b hb))
    (by norm_num [i3041, i3039, i3040, RationalInterval.add]) (by norm_num [i3041, i3039, i3040, RationalInterval.add])

def n3042 (b : ℝ) : ℝ := (n2920 b) * (n3024 b)
def i3042 : RationalInterval := ⟨(-62962315679516158707094610386713 / 15625000000000000000000000000 : ℚ), (-62959722644646475490458032856019 / 15625000000000000000000000000 : ℚ)⟩
theorem b3042 (b : ℝ) (hb : rootInterval.Contains b) : i3042.Contains (n3042 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2920 b hb) (b3024 b hb))
    (by norm_num [i3042, i2920, i3024, RationalInterval.mul]) (by norm_num [i3042, i2920, i3024, RationalInterval.mul])

def n3043 (b : ℝ) : ℝ := (n2932 b) * (n3026 b)
def i3043 : RationalInterval := ⟨(6190060855124458794999225465559443 / 500000000000000000000000000000 : ℚ), (6190269406912582802924607395952787 / 500000000000000000000000000000 : ℚ)⟩
theorem b3043 (b : ℝ) (hb : rootInterval.Contains b) : i3043.Contains (n3043 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2932 b hb) (b3026 b hb))
    (by norm_num [i3043, i2932, i3026, RationalInterval.mul]) (by norm_num [i3043, i2932, i3026, RationalInterval.mul])

def n3044 (b : ℝ) : ℝ := (n3042 b) + (n3043 b)
def i3044 : RationalInterval := ⟨(4175266753379941716372197933184627 / 500000000000000000000000000000 : ℚ), (4175558282283895587229950344560179 / 500000000000000000000000000000 : ℚ)⟩
theorem b3044 (b : ℝ) (hb : rootInterval.Contains b) : i3044.Contains (n3044 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3042 b hb) (b3043 b hb))
    (by norm_num [i3044, i3042, i3043, RationalInterval.add]) (by norm_num [i3044, i3042, i3043, RationalInterval.add])

def n3045 (b : ℝ) : ℝ := (n2944 b) * (n3029 b)
def i3045 : RationalInterval := ⟨(-9076402174592340285953204996471381 / 1000000000000000000000000000000 : ℚ), (-4537786010478284427389033660095831 / 500000000000000000000000000000 : ℚ)⟩
theorem b3045 (b : ℝ) (hb : rootInterval.Contains b) : i3045.Contains (n3045 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2944 b hb) (b3029 b hb))
    (by norm_num [i3045, i2944, i3029, RationalInterval.mul]) (by norm_num [i3045, i2944, i3029, RationalInterval.mul])

def n3046 (b : ℝ) : ℝ := (n3044 b) + (n3045 b)
def i3046 : RationalInterval := ⟨(-725868667832456853208809130102127 / 1000000000000000000000000000000 : ℚ), (-90556932048597210039770828883913 / 125000000000000000000000000000 : ℚ)⟩
theorem b3046 (b : ℝ) (hb : rootInterval.Contains b) : i3046.Contains (n3046 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3044 b hb) (b3045 b hb))
    (by norm_num [i3046, i3044, i3045, RationalInterval.add]) (by norm_num [i3046, i3044, i3045, RationalInterval.add])

def n3047 (b : ℝ) : ℝ := (n2956 b) * (n3032 b)
def i3047 : RationalInterval := ⟨(-12456845479796109614489149967213 / 12500000000000000000000000000 : ℚ), (-15566938136708498814692080599183 / 15625000000000000000000000000 : ℚ)⟩
theorem b3047 (b : ℝ) (hb : rootInterval.Contains b) : i3047.Contains (n3047 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2956 b hb) (b3032 b hb))
    (by norm_num [i3047, i2956, i3032, RationalInterval.mul]) (by norm_num [i3047, i2956, i3032, RationalInterval.mul])

def n3048 (b : ℝ) : ℝ := (n3046 b) + (n3047 b)
def i3048 : RationalInterval := ⟨(-1722416306216145622367941127479167 / 1000000000000000000000000000000 : ℚ), (-215092437142265200557307473677377 / 125000000000000000000000000000 : ℚ)⟩
theorem b3048 (b : ℝ) (hb : rootInterval.Contains b) : i3048.Contains (n3048 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3046 b hb) (b3047 b hb))
    (by norm_num [i3048, i3046, i3047, RationalInterval.add]) (by norm_num [i3048, i3046, i3047, RationalInterval.add])

def n3049 (b : ℝ) : ℝ := (n2923 b) * (n3024 b)
def i3049 : RationalInterval := ⟨(-143343914589045409317505036429141 / 15625000000000000000000000000 : ℚ), (-143340299649648002131733803124671 / 15625000000000000000000000000 : ℚ)⟩
theorem b3049 (b : ℝ) (hb : rootInterval.Contains b) : i3049.Contains (n3049 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2923 b hb) (b3024 b hb))
    (by norm_num [i3049, i2923, i3024, RationalInterval.mul]) (by norm_num [i3049, i2923, i3024, RationalInterval.mul])

def n3050 (b : ℝ) : ℝ := (n2935 b) * (n3026 b)
def i3050 : RationalInterval := ⟨(1149613534592945753747549017343833 / 62500000000000000000000000000 : ℚ), (9197203476221089997572846727741073 / 500000000000000000000000000000 : ℚ)⟩
theorem b3050 (b : ℝ) (hb : rootInterval.Contains b) : i3050.Contains (n3050 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2935 b hb) (b3026 b hb))
    (by norm_num [i3050, i2935, i3026, RationalInterval.mul]) (by norm_num [i3050, i2935, i3026, RationalInterval.mul])

def n3051 (b : ℝ) : ℝ := (n3049 b) + (n3050 b)
def i3051 : RationalInterval := ⟨(576237876236764116477528871627269 / 62500000000000000000000000000 : ℚ), (4610313887432353929357365027751601 / 500000000000000000000000000000 : ℚ)⟩
theorem b3051 (b : ℝ) (hb : rootInterval.Contains b) : i3051.Contains (n3051 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3049 b hb) (b3050 b hb))
    (by norm_num [i3051, i3049, i3050, RationalInterval.add]) (by norm_num [i3051, i3049, i3050, RationalInterval.add])

def n3052 (b : ℝ) : ℝ := (n2947 b) * (n3029 b)
def i3052 : RationalInterval := ⟨(-4522048352570279073477609624131679 / 500000000000000000000000000000 : ℚ), (-1808583407945840592190514647148631 / 200000000000000000000000000000 : ℚ)⟩
theorem b3052 (b : ℝ) (hb : rootInterval.Contains b) : i3052.Contains (n3052 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2947 b hb) (b3029 b hb))
    (by norm_num [i3052, i2947, i3029, RationalInterval.mul]) (by norm_num [i3052, i2947, i3029, RationalInterval.mul])

def n3053 (b : ℝ) : ℝ := (n3051 b) + (n3052 b)
def i3053 : RationalInterval := ⟨(87854657323833858342621348886473 / 500000000000000000000000000000 : ℚ), (177710735135504897762156819760047 / 1000000000000000000000000000000 : ℚ)⟩
theorem b3053 (b : ℝ) (hb : rootInterval.Contains b) : i3053.Contains (n3053 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3051 b hb) (b3052 b hb))
    (by norm_num [i3053, i3051, i3052, RationalInterval.add]) (by norm_num [i3053, i3051, i3052, RationalInterval.add])

def n3054 (b : ℝ) : ℝ := (n2959 b) * (n3032 b)
def i3054 : RationalInterval := ⟨(13146146271615436641033715390923 / 62500000000000000000000000000 : ℚ), (2633837430745885929779120752447 / 12500000000000000000000000000 : ℚ)⟩
theorem b3054 (b : ℝ) (hb : rootInterval.Contains b) : i3054.Contains (n3054 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2959 b hb) (b3032 b hb))
    (by norm_num [i3054, i2959, i3032, RationalInterval.mul]) (by norm_num [i3054, i2959, i3032, RationalInterval.mul])

def n3055 (b : ℝ) : ℝ := (n3053 b) + (n3054 b)
def i3055 : RationalInterval := ⟨(193023827496757351470891072013857 / 500000000000000000000000000000 : ℚ), (388417729595175772144486479955807 / 1000000000000000000000000000000 : ℚ)⟩
theorem b3055 (b : ℝ) (hb : rootInterval.Contains b) : i3055.Contains (n3055 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3053 b hb) (b3054 b hb))
    (by norm_num [i3055, i3053, i3054, RationalInterval.add]) (by norm_num [i3055, i3053, i3054, RationalInterval.add])

def n3056 (b : ℝ) : ℝ := ((16 : ℚ) : ℝ)
def i3056 : RationalInterval := ⟨(16 : ℚ), (16 : ℚ)⟩
theorem b3056 (b : ℝ) (hb : rootInterval.Contains b) : i3056.Contains (n3056 b) := by
  exact RationalInterval.contains_point (16 : ℚ)

def n3057 (b : ℝ) : ℝ := (n2914 b) * (n3056 b)
def i3057 : RationalInterval := ⟨(3172692787979816122850012602349 / 62500000000000000000000000000 : ℚ), (793195158645148453424358418433 / 15625000000000000000000000000 : ℚ)⟩
theorem b3057 (b : ℝ) (hb : rootInterval.Contains b) : i3057.Contains (n3057 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2914 b hb) (b3056 b hb))
    (by norm_num [i3057, i2914, i3056, RationalInterval.mul]) (by norm_num [i3057, i2914, i3056, RationalInterval.mul])

def n3058 (b : ℝ) : ℝ := ((293 : ℚ) : ℝ)
def i3058 : RationalInterval := ⟨(293 : ℚ), (293 : ℚ)⟩
theorem b3058 (b : ℝ) (hb : rootInterval.Contains b) : i3058.Contains (n3058 b) := by
  exact RationalInterval.contains_point (293 : ℚ)

def n3059 (b : ℝ) : ℝ := (n2926 b) * (n3058 b)
def i3059 : RationalInterval := ⟨(-653891934939611118126720896423747 / 1000000000000000000000000000000 : ℚ), (-65386807656112636184447345905143 / 100000000000000000000000000000 : ℚ)⟩
theorem b3059 (b : ℝ) (hb : rootInterval.Contains b) : i3059.Contains (n3059 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2926 b hb) (b3058 b hb))
    (by norm_num [i3059, i2926, i3058, RationalInterval.mul]) (by norm_num [i3059, i2926, i3058, RationalInterval.mul])

