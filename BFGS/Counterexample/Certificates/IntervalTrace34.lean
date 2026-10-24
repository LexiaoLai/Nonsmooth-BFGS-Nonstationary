import BFGS.Counterexample.Certificates.IntervalTrace33

/-! Generated arithmetic proofs. Each bound is checked by the Lean kernel. -/
namespace BFGS.Counterexample.Trace
noncomputable section
open BFGS RationalInterval
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false

def n3060 (b : ℝ) : ℝ := (n3057 b) + (n3059 b)
def i3060 : RationalInterval := ⟨(-603128850331934060161120694786163 / 1000000000000000000000000000000 : ℚ), (-301551793203918430412657260135859 / 500000000000000000000000000000 : ℚ)⟩
theorem b3060 (b : ℝ) (hb : rootInterval.Contains b) : i3060.Contains (n3060 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3057 b hb) (b3059 b hb))
    (by norm_num [i3060, i3057, i3059, RationalInterval.add]) (by norm_num [i3060, i3057, i3059, RationalInterval.add])

def n3061 (b : ℝ) : ℝ := ((1787 : ℚ) : ℝ)
def i3061 : RationalInterval := ⟨(1787 : ℚ), (1787 : ℚ)⟩
theorem b3061 (b : ℝ) (hb : rootInterval.Contains b) : i3061.Contains (n3061 b) := by
  exact RationalInterval.contains_point (1787 : ℚ)

def n3062 (b : ℝ) : ℝ := (n2938 b) * (n3061 b)
def i3062 : RationalInterval := ⟨(363499708139629884371432157920867 / 1000000000000000000000000000000 : ℚ), (363568258580790702073267558666989 / 1000000000000000000000000000000 : ℚ)⟩
theorem b3062 (b : ℝ) (hb : rootInterval.Contains b) : i3062.Contains (n3062 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2938 b hb) (b3061 b hb))
    (by norm_num [i3062, i2938, i3061, RationalInterval.mul]) (by norm_num [i3062, i2938, i3061, RationalInterval.mul])

def n3063 (b : ℝ) : ℝ := (n3060 b) + (n3062 b)
def i3063 : RationalInterval := ⟨(-14976821387019010986855533554081 / 62500000000000000000000000000 : ℚ), (-239535327827046158752046961604729 / 1000000000000000000000000000000 : ℚ)⟩
theorem b3063 (b : ℝ) (hb : rootInterval.Contains b) : i3063.Contains (n3063 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3060 b hb) (b3062 b hb))
    (by norm_num [i3063, i3060, i3062, RationalInterval.add]) (by norm_num [i3063, i3060, i3062, RationalInterval.add])

def n3064 (b : ℝ) : ℝ := ((-2075 : ℚ) : ℝ)
def i3064 : RationalInterval := ⟨(-2075 : ℚ), (-2075 : ℚ)⟩
theorem b3064 (b : ℝ) (hb : rootInterval.Contains b) : i3064.Contains (n3064 b) := by
  exact RationalInterval.contains_point (-2075 : ℚ)

def n3065 (b : ℝ) : ℝ := (n2950 b) * (n3064 b)
def i3065 : RationalInterval := ⟨(13417049821753719109566449240227 / 40000000000000000000000000000 : ℚ), (1677493102363528431393199753603 / 5000000000000000000000000000 : ℚ)⟩
theorem b3065 (b : ℝ) (hb : rootInterval.Contains b) : i3065.Contains (n3065 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2950 b hb) (b3064 b hb))
    (by norm_num [i3065, i2950, i3064, RationalInterval.mul]) (by norm_num [i3065, i2950, i3064, RationalInterval.mul])

def n3066 (b : ℝ) : ℝ := (n3063 b) + (n3065 b)
def i3066 : RationalInterval := ⟨(95797103351538801949472694140379 / 1000000000000000000000000000000 : ℚ), (95963292645659527526592989115871 / 1000000000000000000000000000000 : ℚ)⟩
theorem b3066 (b : ℝ) (hb : rootInterval.Contains b) : i3066.Contains (n3066 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3063 b hb) (b3065 b hb))
    (by norm_num [i3066, i3063, i3065, RationalInterval.add]) (by norm_num [i3066, i3063, i3065, RationalInterval.add])

def n3067 (b : ℝ) : ℝ := (n2917 b) * (n3056 b)
def i3067 : RationalInterval := ⟨(856007622454522145204884741113 / 12500000000000000000000000000 : ℚ), (1070063023901626708841109311167 / 15625000000000000000000000000 : ℚ)⟩
theorem b3067 (b : ℝ) (hb : rootInterval.Contains b) : i3067.Contains (n3067 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2917 b hb) (b3056 b hb))
    (by norm_num [i3067, i2917, i3056, RationalInterval.mul]) (by norm_num [i3067, i2917, i3056, RationalInterval.mul])

def n3068 (b : ℝ) : ℝ := (n2929 b) * (n3058 b)
def i3068 : RationalInterval := ⟨(-1246711393543481571495436416940913 / 1000000000000000000000000000000 : ℚ), (-124665685874742748780429582034263 / 100000000000000000000000000000 : ℚ)⟩
theorem b3068 (b : ℝ) (hb : rootInterval.Contains b) : i3068.Contains (n3068 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2929 b hb) (b3058 b hb))
    (by norm_num [i3068, i2929, i3058, RationalInterval.mul]) (by norm_num [i3068, i2929, i3058, RationalInterval.mul])

def n3069 (b : ℝ) : ℝ := (n3067 b) + (n3068 b)
def i3069 : RationalInterval := ⟨(-1178230783747119799879045637651873 / 1000000000000000000000000000000 : ℚ), (-589086412608861689219232412213971 / 500000000000000000000000000000 : ℚ)⟩
theorem b3069 (b : ℝ) (hb : rootInterval.Contains b) : i3069.Contains (n3069 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3067 b hb) (b3068 b hb))
    (by norm_num [i3069, i3067, i3068, RationalInterval.add]) (by norm_num [i3069, i3067, i3068, RationalInterval.add])

def n3070 (b : ℝ) : ℝ := (n2941 b) * (n3061 b)
def i3070 : RationalInterval := ⟨(1111770976812659102528761370973567 / 1000000000000000000000000000000 : ℚ), (555962956713631618256605530381333 / 500000000000000000000000000000 : ℚ)⟩
theorem b3070 (b : ℝ) (hb : rootInterval.Contains b) : i3070.Contains (n3070 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2941 b hb) (b3061 b hb))
    (by norm_num [i3070, i2941, i3061, RationalInterval.mul]) (by norm_num [i3070, i2941, i3061, RationalInterval.mul])

def n3071 (b : ℝ) : ℝ := (n3069 b) + (n3070 b)
def i3071 : RationalInterval := ⟨(-33229903467230348675142133339153 / 500000000000000000000000000000 : ℚ), (-16561727947615035481313440916319 / 250000000000000000000000000000 : ℚ)⟩
theorem b3071 (b : ℝ) (hb : rootInterval.Contains b) : i3071.Contains (n3071 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3069 b hb) (b3070 b hb))
    (by norm_num [i3071, i3069, i3070, RationalInterval.add]) (by norm_num [i3071, i3069, i3070, RationalInterval.add])

def n3072 (b : ℝ) : ℝ := (n2953 b) * (n3064 b)
def i3072 : RationalInterval := ⟨(8275418277037814873644620744749 / 20000000000000000000000000000 : ℚ), (16557689521137756209807469358181 / 40000000000000000000000000000 : ℚ)⟩
theorem b3072 (b : ℝ) (hb : rootInterval.Contains b) : i3072.Contains (n3072 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2953 b hb) (b3064 b hb))
    (by norm_num [i3072, i2953, i3064, RationalInterval.mul]) (by norm_num [i3072, i2953, i3064, RationalInterval.mul])

def n3073 (b : ℝ) : ℝ := (n3071 b) + (n3072 b)
def i3073 : RationalInterval := ⟨(43413888364678755791493346319893 / 125000000000000000000000000000 : ℚ), (347695326237983763319932970289249 / 1000000000000000000000000000000 : ℚ)⟩
theorem b3073 (b : ℝ) (hb : rootInterval.Contains b) : i3073.Contains (n3073 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3071 b hb) (b3072 b hb))
    (by norm_num [i3073, i3071, i3072, RationalInterval.add]) (by norm_num [i3073, i3071, i3072, RationalInterval.add])

def n3074 (b : ℝ) : ℝ := (n2920 b) * (n3056 b)
def i3074 : RationalInterval := ⟨(8994246092092353641494004693717 / 62500000000000000000000000000 : ℚ), (8994616525645165529584944340959 / 62500000000000000000000000000 : ℚ)⟩
theorem b3074 (b : ℝ) (hb : rootInterval.Contains b) : i3074.Contains (n3074 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2920 b hb) (b3056 b hb))
    (by norm_num [i3074, i2920, i3056, RationalInterval.mul]) (by norm_num [i3074, i2920, i3056, RationalInterval.mul])

def n3075 (b : ℝ) : ℝ := (n2932 b) * (n3058 b)
def i3075 : RationalInterval := ⟨(-3428636930482772705589621865811279 / 1000000000000000000000000000000 : ℚ), (-3428521418811845797608266656727631 / 1000000000000000000000000000000 : ℚ)⟩
theorem b3075 (b : ℝ) (hb : rootInterval.Contains b) : i3075.Contains (n3075 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2932 b hb) (b3058 b hb))
    (by norm_num [i3075, i2932, i3058, RationalInterval.mul]) (by norm_num [i3075, i2932, i3058, RationalInterval.mul])

def n3076 (b : ℝ) : ℝ := (n3074 b) + (n3075 b)
def i3076 : RationalInterval := ⟨(-3284728993009295047325717790711807 / 1000000000000000000000000000000 : ℚ), (-3284607554401523149134907547272287 / 1000000000000000000000000000000 : ℚ)⟩
theorem b3076 (b : ℝ) (hb : rootInterval.Contains b) : i3076.Contains (n3076 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3074 b hb) (b3075 b hb))
    (by norm_num [i3076, i3074, i3075, RationalInterval.add]) (by norm_num [i3076, i3074, i3075, RationalInterval.add])

def n3077 (b : ℝ) : ℝ := (n2944 b) * (n3061 b)
def i3077 : RationalInterval := ⟨(1867147962404949176086622876028379 / 500000000000000000000000000000 : ℚ), (3734637505410203106377706039303329 / 1000000000000000000000000000000 : ℚ)⟩
theorem b3077 (b : ℝ) (hb : rootInterval.Contains b) : i3077.Contains (n3077 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2944 b hb) (b3061 b hb))
    (by norm_num [i3077, i2944, i3061, RationalInterval.mul]) (by norm_num [i3077, i2944, i3061, RationalInterval.mul])

def n3078 (b : ℝ) : ℝ := (n3076 b) + (n3077 b)
def i3078 : RationalInterval := ⟨(449566931800603304847527961344951 / 1000000000000000000000000000000 : ℚ), (225014975504339978621399246015521 / 500000000000000000000000000000 : ℚ)⟩
theorem b3078 (b : ℝ) (hb : rootInterval.Contains b) : i3078.Contains (n3078 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3076 b hb) (b3077 b hb))
    (by norm_num [i3078, i3076, i3077, RationalInterval.add]) (by norm_num [i3078, i3076, i3077, RationalInterval.add])

def n3079 (b : ℝ) : ℝ := (n2956 b) * (n3064 b)
def i3079 : RationalInterval := ⟨(12544231702396168947761579511963 / 10000000000000000000000000000 : ℚ), (10038040532262884446627179099793 / 8000000000000000000000000000 : ℚ)⟩
theorem b3079 (b : ℝ) (hb : rootInterval.Contains b) : i3079.Contains (n3079 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2956 b hb) (b3064 b hb))
    (by norm_num [i3079, i2956, i3064, RationalInterval.mul]) (by norm_num [i3079, i2956, i3064, RationalInterval.mul])

def n3080 (b : ℝ) : ℝ := (n3078 b) + (n3079 b)
def i3080 : RationalInterval := ⟨(1703990102040220199623685912541251 / 1000000000000000000000000000000 : ℚ), (1704785017541540513071195879505167 / 1000000000000000000000000000000 : ℚ)⟩
theorem b3080 (b : ℝ) (hb : rootInterval.Contains b) : i3080.Contains (n3080 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3078 b hb) (b3079 b hb))
    (by norm_num [i3080, i3078, i3079, RationalInterval.add]) (by norm_num [i3080, i3078, i3079, RationalInterval.add])

def n3081 (b : ℝ) : ℝ := (n2923 b) * (n3056 b)
def i3081 : RationalInterval := ⟨(20477185664235428875961971874953 / 62500000000000000000000000000 : ℚ), (20477702084149344188215005204163 / 62500000000000000000000000000 : ℚ)⟩
theorem b3081 (b : ℝ) (hb : rootInterval.Contains b) : i3081.Contains (n3081 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2923 b hb) (b3056 b hb))
    (by norm_num [i3081, i2923, i3056, RationalInterval.mul]) (by norm_num [i3081, i2923, i3056, RationalInterval.mul])

def n3082 (b : ℝ) : ℝ := (n2935 b) * (n3058 b)
def i3082 : RationalInterval := ⟨(-5094103248644195405082881079826341 / 1000000000000000000000000000000 : ℚ), (-636742468120478460960362688245261 / 125000000000000000000000000000 : ℚ)⟩
theorem b3082 (b : ℝ) (hb : rootInterval.Contains b) : i3082.Contains (n3082 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2935 b hb) (b3058 b hb))
    (by norm_num [i3082, i2935, i3058, RationalInterval.mul]) (by norm_num [i3082, i2935, i3058, RationalInterval.mul])

def n3083 (b : ℝ) : ℝ := (n3081 b) + (n3082 b)
def i3083 : RationalInterval := ⟨(-4766468278016428543067489529827093 / 1000000000000000000000000000000 : ℚ), (-119157412790435954516786535567387 / 25000000000000000000000000000 : ℚ)⟩
theorem b3083 (b : ℝ) (hb : rootInterval.Contains b) : i3083.Contains (n3083 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3081 b hb) (b3082 b hb))
    (by norm_num [i3083, i3081, i3082, RationalInterval.add]) (by norm_num [i3083, i3081, i3082, RationalInterval.add])

def n3084 (b : ℝ) : ℝ := (n2947 b) * (n3061 b)
def i3084 : RationalInterval := ⟨(744171897305829412444036305423579 / 200000000000000000000000000000 : ℚ), (1860672439798086277758344093558211 / 500000000000000000000000000000 : ℚ)⟩
theorem b3084 (b : ℝ) (hb : rootInterval.Contains b) : i3084.Contains (n3084 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2947 b hb) (b3061 b hb))
    (by norm_num [i3084, i2947, i3061, RationalInterval.mul]) (by norm_num [i3084, i2947, i3061, RationalInterval.mul])

def n3085 (b : ℝ) : ℝ := (n3083 b) + (n3084 b)
def i3085 : RationalInterval := ⟨(-522804395743640740423654001354599 / 500000000000000000000000000000 : ℚ), (-522475816010632812577386617789529 / 500000000000000000000000000000 : ℚ)⟩
theorem b3085 (b : ℝ) (hb : rootInterval.Contains b) : i3085.Contains (n3085 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3083 b hb) (b3084 b hb))
    (by norm_num [i3085, i3083, i3084, RationalInterval.add]) (by norm_num [i3085, i3083, i3084, RationalInterval.add])

def n3086 (b : ℝ) : ℝ := (n2959 b) * (n3064 b)
def i3086 : RationalInterval := ⟨(-2122412686911733322055019635467 / 8000000000000000000000000000 : ℚ), (-10593496510136711079667945412103 / 40000000000000000000000000000 : ℚ)⟩
theorem b3086 (b : ℝ) (hb : rootInterval.Contains b) : i3086.Contains (n3086 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2959 b hb) (b3064 b hb))
    (by norm_num [i3086, i2959, i3064, RationalInterval.mul]) (by norm_num [i3086, i2959, i3064, RationalInterval.mul])

def n3087 (b : ℝ) : ℝ := (n3085 b) + (n3086 b)
def i3087 : RationalInterval := ⟨(-1310910377351248146104185457142573 / 1000000000000000000000000000000 : ℚ), (-1309789044774683402146471870881633 / 1000000000000000000000000000000 : ℚ)⟩
theorem b3087 (b : ℝ) (hb : rootInterval.Contains b) : i3087.Contains (n3087 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3085 b hb) (b3086 b hb))
    (by norm_num [i3087, i3085, i3086, RationalInterval.add]) (by norm_num [i3087, i3085, i3086, RationalInterval.add])

def n3088 (b : ℝ) : ℝ := ((521647187 / 22230591050 : ℚ) : ℝ)
def i3088 : RationalInterval := ⟨(521647187 / 22230591050 : ℚ), (521647187 / 22230591050 : ℚ)⟩
theorem b3088 (b : ℝ) (hb : rootInterval.Contains b) : i3088.Contains (n3088 b) := by
  exact RationalInterval.contains_point (521647187 / 22230591050 : ℚ)

def n3089 (b : ℝ) : ℝ := (n2970 b) * (n3088 b)
def i3089 : RationalInterval := ⟨(1221313391792930799195487411123 / 200000000000000000000000000000 : ℚ), (6115030747634772128434469108859 / 1000000000000000000000000000000 : ℚ)⟩
theorem b3089 (b : ℝ) (hb : rootInterval.Contains b) : i3089.Contains (n3089 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2970 b hb) (b3088 b hb))
    (by norm_num [i3089, i2970, i3088, RationalInterval.mul]) (by norm_num [i3089, i2970, i3088, RationalInterval.mul])

def n3090 (b : ℝ) : ℝ := ((-574350721 / 11115295525 : ℚ) : ℝ)
def i3090 : RationalInterval := ⟨(-574350721 / 11115295525 : ℚ), (-574350721 / 11115295525 : ℚ)⟩
theorem b3090 (b : ℝ) (hb : rootInterval.Contains b) : i3090.Contains (n3090 b) := by
  exact RationalInterval.contains_point (-574350721 / 11115295525 : ℚ)

def n3091 (b : ℝ) : ℝ := (n2977 b) * (n3090 b)
def i3091 : RationalInterval := ⟨(-7040382652772231374171255764477 / 250000000000000000000000000000 : ℚ), (-28118590364040179700034690519497 / 1000000000000000000000000000000 : ℚ)⟩
theorem b3091 (b : ℝ) (hb : rootInterval.Contains b) : i3091.Contains (n3091 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2977 b hb) (b3090 b hb))
    (by norm_num [i3091, i2977, i3090, RationalInterval.mul]) (by norm_num [i3091, i2977, i3090, RationalInterval.mul])

def n3092 (b : ℝ) : ℝ := (n3089 b) + (n3091 b)
def i3092 : RationalInterval := ⟨(-22054963652124271500707586002293 / 1000000000000000000000000000000 : ℚ), (-11001779808202703785800110705319 / 500000000000000000000000000000 : ℚ)⟩
theorem b3092 (b : ℝ) (hb : rootInterval.Contains b) : i3092.Contains (n3092 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3089 b hb) (b3091 b hb))
    (by norm_num [i3092, i3089, i3091, RationalInterval.add]) (by norm_num [i3092, i3089, i3091, RationalInterval.add])

def n3093 (b : ℝ) : ℝ := ((123292286 / 11115295525 : ℚ) : ℝ)
def i3093 : RationalInterval := ⟨(123292286 / 11115295525 : ℚ), (123292286 / 11115295525 : ℚ)⟩
theorem b3093 (b : ℝ) (hb : rootInterval.Contains b) : i3093.Contains (n3093 b) := by
  exact RationalInterval.contains_point (123292286 / 11115295525 : ℚ)

def n3094 (b : ℝ) : ℝ := (n2984 b) * (n3093 b)
def i3094 : RationalInterval := ⟨(4456280080091732087556358160877 / 200000000000000000000000000000 : ℚ), (22300590058255437980479218131619 / 1000000000000000000000000000000 : ℚ)⟩
theorem b3094 (b : ℝ) (hb : rootInterval.Contains b) : i3094.Contains (n3094 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2984 b hb) (b3093 b hb))
    (by norm_num [i3094, i2984, i3093, RationalInterval.mul]) (by norm_num [i3094, i2984, i3093, RationalInterval.mul])

def n3095 (b : ℝ) : ℝ := (n3092 b) + (n3094 b)
def i3095 : RationalInterval := ⟨(56609187083597234268551200523 / 250000000000000000000000000000 : ℚ), (297030441850030408878996720981 / 1000000000000000000000000000000 : ℚ)⟩
theorem b3095 (b : ℝ) (hb : rootInterval.Contains b) : i3095.Contains (n3095 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3092 b hb) (b3094 b hb))
    (by norm_num [i3095, i3092, i3094, RationalInterval.add]) (by norm_num [i3095, i3092, i3094, RationalInterval.add])

def n3096 (b : ℝ) : ℝ := ((27089991 / 11115295525 : ℚ) : ℝ)
def i3096 : RationalInterval := ⟨(27089991 / 11115295525 : ℚ), (27089991 / 11115295525 : ℚ)⟩
theorem b3096 (b : ℝ) (hb : rootInterval.Contains b) : i3096.Contains (n3096 b) := by
  exact RationalInterval.contains_point (27089991 / 11115295525 : ℚ)

def n3097 (b : ℝ) : ℝ := (n2991 b) * (n3096 b)
def i3097 : RationalInterval := ⟨(-85062128484934653140759588143 / 500000000000000000000000000000 : ℚ), (-16416466980466424061996503093 / 100000000000000000000000000000 : ℚ)⟩
theorem b3097 (b : ℝ) (hb : rootInterval.Contains b) : i3097.Contains (n3097 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2991 b hb) (b3096 b hb))
    (by norm_num [i3097, i2991, i3096, RationalInterval.mul]) (by norm_num [i3097, i2991, i3096, RationalInterval.mul])

def n3098 (b : ℝ) : ℝ := (n3095 b) + (n3097 b)
def i3098 : RationalInterval := ⟨(28156245682259815396342812903 / 500000000000000000000000000000 : ℚ), (132865772045366168259031690051 / 1000000000000000000000000000000 : ℚ)⟩
theorem b3098 (b : ℝ) (hb : rootInterval.Contains b) : i3098.Contains (n3098 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3095 b hb) (b3097 b hb))
    (by norm_num [i3098, i3095, i3097, RationalInterval.add]) (by norm_num [i3098, i3095, i3097, RationalInterval.add])

def n3099 (b : ℝ) : ℝ := ((-118215737 / 22230591050 : ℚ) : ℝ)
def i3099 : RationalInterval := ⟨(-118215737 / 22230591050 : ℚ), (-118215737 / 22230591050 : ℚ)⟩
theorem b3099 (b : ℝ) (hb : rootInterval.Contains b) : i3099.Contains (n3099 b) := by
  exact RationalInterval.contains_point (-118215737 / 22230591050 : ℚ)

def n3100 (b : ℝ) : ℝ := (n2970 b) * (n3099 b)
def i3100 : RationalInterval := ⟨(-1385788871529571948003123080021 / 1000000000000000000000000000000 : ℚ), (-86491925431615445609178056981 / 62500000000000000000000000000 : ℚ)⟩
theorem b3100 (b : ℝ) (hb : rootInterval.Contains b) : i3100.Contains (n3100 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2970 b hb) (b3099 b hb))
    (by norm_num [i3100, i2970, i3099, RationalInterval.mul]) (by norm_num [i3100, i2970, i3099, RationalInterval.mul])

def n3101 (b : ℝ) : ℝ := ((888696 / 11115295525 : ℚ) : ℝ)
def i3101 : RationalInterval := ⟨(888696 / 11115295525 : ℚ), (888696 / 11115295525 : ℚ)⟩
theorem b3101 (b : ℝ) (hb : rootInterval.Contains b) : i3101.Contains (n3101 b) := by
  exact RationalInterval.contains_point (888696 / 11115295525 : ℚ)

def n3102 (b : ℝ) : ℝ := (n2977 b) * (n3101 b)
def i3102 : RationalInterval := ⟨(21754024038354999765641479299 / 500000000000000000000000000000 : ℚ), (10893622438732989652328648009 / 250000000000000000000000000000 : ℚ)⟩
theorem b3102 (b : ℝ) (hb : rootInterval.Contains b) : i3102.Contains (n3102 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2977 b hb) (b3101 b hb))
    (by norm_num [i3102, i2977, i3101, RationalInterval.mul]) (by norm_num [i3102, i2977, i3101, RationalInterval.mul])

def n3103 (b : ℝ) : ℝ := (n3100 b) + (n3102 b)
def i3103 : RationalInterval := ⟨(-1342280823452861948471840121423 / 1000000000000000000000000000000 : ℚ), (-67014815857545758556876715983 / 50000000000000000000000000000 : ℚ)⟩
theorem b3103 (b : ℝ) (hb : rootInterval.Contains b) : i3103.Contains (n3103 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3100 b hb) (b3102 b hb))
    (by norm_num [i3103, i3100, i3102, RationalInterval.add]) (by norm_num [i3103, i3100, i3102, RationalInterval.add])

def n3104 (b : ℝ) : ℝ := ((8549264 / 11115295525 : ℚ) : ℝ)
def i3104 : RationalInterval := ⟨(8549264 / 11115295525 : ℚ), (8549264 / 11115295525 : ℚ)⟩
theorem b3104 (b : ℝ) (hb : rootInterval.Contains b) : i3104.Contains (n3104 b) := by
  exact RationalInterval.contains_point (8549264 / 11115295525 : ℚ)

def n3105 (b : ℝ) : ℝ := (n2984 b) * (n3104 b)
def i3105 : RationalInterval := ⟨(193128033891377041594629959229 / 125000000000000000000000000000 : ℚ), (1546354909534251954179385418491 / 1000000000000000000000000000000 : ℚ)⟩
theorem b3105 (b : ℝ) (hb : rootInterval.Contains b) : i3105.Contains (n3105 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2984 b hb) (b3104 b hb))
    (by norm_num [i3105, i2984, i3104, RationalInterval.mul]) (by norm_num [i3105, i2984, i3104, RationalInterval.mul])

def n3106 (b : ℝ) : ℝ := (n3103 b) + (n3105 b)
def i3106 : RationalInterval := ⟨(202743447678154384285199552409 / 1000000000000000000000000000000 : ℚ), (206058592383336783041851098831 / 1000000000000000000000000000000 : ℚ)⟩
theorem b3106 (b : ℝ) (hb : rootInterval.Contains b) : i3106.Contains (n3106 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3103 b hb) (b3105 b hb))
    (by norm_num [i3106, i3103, i3105, RationalInterval.add]) (by norm_num [i3106, i3103, i3105, RationalInterval.add])

def n3107 (b : ℝ) : ℝ := ((7032384 / 11115295525 : ℚ) : ℝ)
def i3107 : RationalInterval := ⟨(7032384 / 11115295525 : ℚ), (7032384 / 11115295525 : ℚ)⟩
theorem b3107 (b : ℝ) (hb : rootInterval.Contains b) : i3107.Contains (n3107 b) := by
  exact RationalInterval.contains_point (7032384 / 11115295525 : ℚ)

def n3108 (b : ℝ) : ℝ := (n2991 b) * (n3107 b)
def i3108 : RationalInterval := ⟨(-44163141387784048787068808957 / 1000000000000000000000000000000 : ℚ), (-21308035822152985047281709397 / 500000000000000000000000000000 : ℚ)⟩
theorem b3108 (b : ℝ) (hb : rootInterval.Contains b) : i3108.Contains (n3108 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2991 b hb) (b3107 b hb))
    (by norm_num [i3108, i2991, i3107, RationalInterval.mul]) (by norm_num [i3108, i2991, i3107, RationalInterval.mul])

def n3109 (b : ℝ) : ℝ := (n3106 b) + (n3108 b)
def i3109 : RationalInterval := ⟨(39645076572592583874532685863 / 250000000000000000000000000000 : ℚ), (163442520739030812947287680037 / 1000000000000000000000000000000 : ℚ)⟩
theorem b3109 (b : ℝ) (hb : rootInterval.Contains b) : i3109.Contains (n3109 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3106 b hb) (b3108 b hb))
    (by norm_num [i3109, i3106, i3108, RationalInterval.add]) (by norm_num [i3109, i3106, i3108, RationalInterval.add])

def n3110 (b : ℝ) : ℝ := ((23413073 / 4446118210 : ℚ) : ℝ)
def i3110 : RationalInterval := ⟨(23413073 / 4446118210 : ℚ), (23413073 / 4446118210 : ℚ)⟩
theorem b3110 (b : ℝ) (hb : rootInterval.Contains b) : i3110.Contains (n3110 b) := by
  exact RationalInterval.contains_point (23413073 / 4446118210 : ℚ)

def n3111 (b : ℝ) : ℝ := (n2970 b) * (n3110 b)
def i3111 : RationalInterval := ⟨(1370404188431168981148569292831 / 1000000000000000000000000000000 : ℚ), (686151794065063640328810979297 / 500000000000000000000000000000 : ℚ)⟩
theorem b3111 (b : ℝ) (hb : rootInterval.Contains b) : i3111.Contains (n3111 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2970 b hb) (b3110 b hb))
    (by norm_num [i3111, i2970, i3110, RationalInterval.mul]) (by norm_num [i3111, i2970, i3110, RationalInterval.mul])

def n3112 (b : ℝ) : ℝ := ((-118410819 / 2223059105 : ℚ) : ℝ)
def i3112 : RationalInterval := ⟨(-118410819 / 2223059105 : ℚ), (-118410819 / 2223059105 : ℚ)⟩
theorem b3112 (b : ℝ) (hb : rootInterval.Contains b) : i3112.Contains (n3112 b) := by
  exact RationalInterval.contains_point (-118410819 / 2223059105 : ℚ)

def n3113 (b : ℝ) : ℝ := (n2977 b) * (n3112 b)
def i3113 : RationalInterval := ⟨(-29029561398884447033648412233131 / 1000000000000000000000000000000 : ℚ), (-14492648796254866315334015367351 / 500000000000000000000000000000 : ℚ)⟩
theorem b3113 (b : ℝ) (hb : rootInterval.Contains b) : i3113.Contains (n3113 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2977 b hb) (b3112 b hb))
    (by norm_num [i3113, i2977, i3112, RationalInterval.mul]) (by norm_num [i3113, i2977, i3112, RationalInterval.mul])

def n3114 (b : ℝ) : ℝ := (n3111 b) + (n3113 b)
def i3114 : RationalInterval := ⟨(-276591572104532780524998429403 / 10000000000000000000000000000 : ℚ), (-6903248501094901337502602194027 / 250000000000000000000000000000 : ℚ)⟩
theorem b3114 (b : ℝ) (hb : rootInterval.Contains b) : i3114.Contains (n3114 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3111 b hb) (b3113 b hb))
    (by norm_num [i3114, i3111, i3113, RationalInterval.add]) (by norm_num [i3114, i3111, i3113, RationalInterval.add])

def n3115 (b : ℝ) : ℝ := ((30921059 / 2223059105 : ℚ) : ℝ)
def i3115 : RationalInterval := ⟨(30921059 / 2223059105 : ℚ), (30921059 / 2223059105 : ℚ)⟩
theorem b3115 (b : ℝ) (hb : rootInterval.Contains b) : i3115.Contains (n3115 b) := by
  exact RationalInterval.contains_point (30921059 / 2223059105 : ℚ)

def n3116 (b : ℝ) : ℝ := (n2984 b) * (n3115 b)
def i3116 : RationalInterval := ⟨(13970146039493619788540878027601 / 500000000000000000000000000000 : ℚ), (2796435540687962565903104238499 / 100000000000000000000000000000 : ℚ)⟩
theorem b3116 (b : ℝ) (hb : rootInterval.Contains b) : i3116.Contains (n3116 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2984 b hb) (b3115 b hb))
    (by norm_num [i3116, i2984, i3115, RationalInterval.mul]) (by norm_num [i3116, i2984, i3115, RationalInterval.mul])

def n3117 (b : ℝ) : ℝ := (n3114 b) + (n3116 b)
def i3117 : RationalInterval := ⟨(140567434266980762290956557451 / 500000000000000000000000000000 : ℚ), (175680701250010154510316804441 / 500000000000000000000000000000 : ℚ)⟩
theorem b3117 (b : ℝ) (hb : rootInterval.Contains b) : i3117.Contains (n3117 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3114 b hb) (b3116 b hb))
    (by norm_num [i3117, i3114, i3116, RationalInterval.add]) (by norm_num [i3117, i3114, i3116, RationalInterval.add])

def n3118 (b : ℝ) : ℝ := ((9999454 / 2223059105 : ℚ) : ℝ)
def i3118 : RationalInterval := ⟨(9999454 / 2223059105 : ℚ), (9999454 / 2223059105 : ℚ)⟩
theorem b3118 (b : ℝ) (hb : rootInterval.Contains b) : i3118.Contains (n3118 b) := by
  exact RationalInterval.contains_point (9999454 / 2223059105 : ℚ)

def n3119 (b : ℝ) : ℝ := (n2991 b) * (n3118 b)
def i3119 : RationalInterval := ⟨(-313981219457471860026450738463 / 1000000000000000000000000000000 : ℚ), (-75745552302736509746545864873 / 250000000000000000000000000000 : ℚ)⟩
theorem b3119 (b : ℝ) (hb : rootInterval.Contains b) : i3119.Contains (n3119 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2991 b hb) (b3118 b hb))
    (by norm_num [i3119, i2991, i3118, RationalInterval.mul]) (by norm_num [i3119, i2991, i3118, RationalInterval.mul])

def n3120 (b : ℝ) : ℝ := (n3117 b) + (n3119 b)
def i3120 : RationalInterval := ⟨(-32846350923510335444537623561 / 1000000000000000000000000000000 : ℚ), (4837919328907427003445014939 / 100000000000000000000000000000 : ℚ)⟩
theorem b3120 (b : ℝ) (hb : rootInterval.Contains b) : i3120.Contains (n3120 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3117 b hb) (b3119 b hb))
    (by norm_num [i3120, i3117, i3119, RationalInterval.add]) (by norm_num [i3120, i3117, i3119, RationalInterval.add])

def n3121 (b : ℝ) : ℝ := ((-183928858 / 11115295525 : ℚ) : ℝ)
def i3121 : RationalInterval := ⟨(-183928858 / 11115295525 : ℚ), (-183928858 / 11115295525 : ℚ)⟩
theorem b3121 (b : ℝ) (hb : rootInterval.Contains b) : i3121.Contains (n3121 b) := by
  exact RationalInterval.contains_point (-183928858 / 11115295525 : ℚ)

def n3122 (b : ℝ) : ℝ := (n2970 b) * (n3121 b)
def i3122 : RationalInterval := ⟨(-431222730641256132633254756161 / 100000000000000000000000000000 : ℚ), (-4306258770500766342080424528029 / 1000000000000000000000000000000 : ℚ)⟩
theorem b3122 (b : ℝ) (hb : rootInterval.Contains b) : i3122.Contains (n3122 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2970 b hb) (b3121 b hb))
    (by norm_num [i3122, i2970, i3121, RationalInterval.mul]) (by norm_num [i3122, i2970, i3121, RationalInterval.mul])

def n3123 (b : ℝ) : ℝ := ((2783828 / 11115295525 : ℚ) : ℝ)
def i3123 : RationalInterval := ⟨(2783828 / 11115295525 : ℚ), (2783828 / 11115295525 : ℚ)⟩
theorem b3123 (b : ℝ) (hb : rootInterval.Contains b) : i3123.Contains (n3123 b) := by
  exact RationalInterval.contains_point (2783828 / 11115295525 : ℚ)

def n3124 (b : ℝ) : ℝ := (n2977 b) * (n3123 b)
def i3124 : RationalInterval := ⟨(2725767246871628646357638069 / 20000000000000000000000000000 : ℚ), (17062061248375811929986607079 / 125000000000000000000000000000 : ℚ)⟩
theorem b3124 (b : ℝ) (hb : rootInterval.Contains b) : i3124.Contains (n3124 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2977 b hb) (b3123 b hb))
    (by norm_num [i3124, i2977, i3123, RationalInterval.mul]) (by norm_num [i3124, i2977, i3123, RationalInterval.mul])

def n3125 (b : ℝ) : ℝ := (n3122 b) + (n3124 b)
def i3125 : RationalInterval := ⟨(-52199236800862248675183320727 / 12500000000000000000000000000 : ℚ), (-4169762280513759846640531671397 / 1000000000000000000000000000000 : ℚ)⟩
theorem b3125 (b : ℝ) (hb : rootInterval.Contains b) : i3125.Contains (n3125 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3122 b hb) (b3124 b hb))
    (by norm_num [i3125, i3122, i3124, RationalInterval.add]) (by norm_num [i3125, i3122, i3124, RationalInterval.add])

def n3126 (b : ℝ) : ℝ := ((23578552 / 11115295525 : ℚ) : ℝ)
def i3126 : RationalInterval := ⟨(23578552 / 11115295525 : ℚ), (23578552 / 11115295525 : ℚ)⟩
theorem b3126 (b : ℝ) (hb : rootInterval.Contains b) : i3126.Contains (n3126 b) := by
  exact RationalInterval.contains_point (23578552 / 11115295525 : ℚ)

def n3127 (b : ℝ) : ℝ := (n2984 b) * (n3126 b)
def i3127 : RationalInterval := ⟨(4261119450531036053484974065079 / 1000000000000000000000000000000 : ℚ), (1066197325433764107726707714779 / 250000000000000000000000000000 : ℚ)⟩
theorem b3127 (b : ℝ) (hb : rootInterval.Contains b) : i3127.Contains (n3127 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2984 b hb) (b3126 b hb))
    (by norm_num [i3127, i2984, i3126, RationalInterval.mul]) (by norm_num [i3127, i2984, i3126, RationalInterval.mul])

def n3128 (b : ℝ) : ℝ := (n3125 b) + (n3127 b)
def i3128 : RationalInterval := ⟨(85180506462056159470308406919 / 1000000000000000000000000000000 : ℚ), (95027021221296584266299187719 / 1000000000000000000000000000000 : ℚ)⟩
theorem b3128 (b : ℝ) (hb : rootInterval.Contains b) : i3128.Contains (n3128 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3125 b hb) (b3127 b hb))
    (by norm_num [i3128, i3125, i3127, RationalInterval.add]) (by norm_num [i3128, i3125, i3127, RationalInterval.add])

def n3129 (b : ℝ) : ℝ := ((13924037 / 11115295525 : ℚ) : ℝ)
def i3129 : RationalInterval := ⟨(13924037 / 11115295525 : ℚ), (13924037 / 11115295525 : ℚ)⟩
theorem b3129 (b : ℝ) (hb : rootInterval.Contains b) : i3129.Contains (n3129 b) := by
  exact RationalInterval.contains_point (13924037 / 11115295525 : ℚ)

def n3130 (b : ℝ) : ℝ := (n2991 b) * (n3129 b)
def i3130 : RationalInterval := ⟨(-8744249670093903338056500007 / 100000000000000000000000000000 : ℚ), (-16875863387720783362159817841 / 200000000000000000000000000000 : ℚ)⟩
theorem b3130 (b : ℝ) (hb : rootInterval.Contains b) : i3130.Contains (n3130 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2991 b hb) (b3129 b hb))
    (by norm_num [i3130, i2991, i3129, RationalInterval.mul]) (by norm_num [i3130, i2991, i3129, RationalInterval.mul])

def n3131 (b : ℝ) : ℝ := (n3128 b) + (n3130 b)
def i3131 : RationalInterval := ⟨(-2261990238882873910256593151 / 1000000000000000000000000000000 : ℚ), (5323852141346333727750049257 / 500000000000000000000000000000 : ℚ)⟩
theorem b3131 (b : ℝ) (hb : rootInterval.Contains b) : i3131.Contains (n3131 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3128 b hb) (b3130 b hb))
    (by norm_num [i3131, i3128, i3130, RationalInterval.add]) (by norm_num [i3131, i3128, i3130, RationalInterval.add])

def n3132 (b : ℝ) : ℝ := (n3002 b) * (n3088 b)
def i3132 : RationalInterval := ⟨(267543945458729775498563659191 / 250000000000000000000000000000 : ℚ), (543890733172889417365474860877 / 500000000000000000000000000000 : ℚ)⟩
theorem b3132 (b : ℝ) (hb : rootInterval.Contains b) : i3132.Contains (n3132 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b3002 b hb) (b3088 b hb))
    (by norm_num [i3132, i3002, i3088, RationalInterval.mul]) (by norm_num [i3132, i3002, i3088, RationalInterval.mul])

def n3133 (b : ℝ) : ℝ := (n3009 b) * (n3090 b)
def i3133 : RationalInterval := ⟨(-3895849988657521351067749901987 / 1000000000000000000000000000000 : ℚ), (-3806728673014211439412827469893 / 1000000000000000000000000000000 : ℚ)⟩
theorem b3133 (b : ℝ) (hb : rootInterval.Contains b) : i3133.Contains (n3133 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b3009 b hb) (b3090 b hb))
    (by norm_num [i3133, i3009, i3090, RationalInterval.mul]) (by norm_num [i3133, i3009, i3090, RationalInterval.mul])

def n3134 (b : ℝ) : ℝ := (n3132 b) + (n3133 b)
def i3134 : RationalInterval := ⟨(-2825674206822602249073495265223 / 1000000000000000000000000000000 : ℚ), (-2718947206668432604681877748139 / 1000000000000000000000000000000 : ℚ)⟩
theorem b3134 (b : ℝ) (hb : rootInterval.Contains b) : i3134.Contains (n3134 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3132 b hb) (b3133 b hb))
    (by norm_num [i3134, i3132, i3133, RationalInterval.add]) (by norm_num [i3134, i3132, i3133, RationalInterval.add])

def n3135 (b : ℝ) : ℝ := (n3016 b) * (n3093 b)
def i3135 : RationalInterval := ⟨(921412914423315153268603466281 / 500000000000000000000000000000 : ℚ), (1882833870389135563329968309613 / 1000000000000000000000000000000 : ℚ)⟩
theorem b3135 (b : ℝ) (hb : rootInterval.Contains b) : i3135.Contains (n3135 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b3016 b hb) (b3093 b hb))
    (by norm_num [i3135, i3016, i3093, RationalInterval.mul]) (by norm_num [i3135, i3016, i3093, RationalInterval.mul])

def n3136 (b : ℝ) : ℝ := (n3134 b) + (n3135 b)
def i3136 : RationalInterval := ⟨(-982848377975971942536288332661 / 1000000000000000000000000000000 : ℚ), (-418056668139648520675954719263 / 500000000000000000000000000000 : ℚ)⟩
theorem b3136 (b : ℝ) (hb : rootInterval.Contains b) : i3136.Contains (n3136 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3134 b hb) (b3135 b hb))
    (by norm_num [i3136, i3134, i3135, RationalInterval.add]) (by norm_num [i3136, i3134, i3135, RationalInterval.add])

def n3137 (b : ℝ) : ℝ := (n3023 b) * (n3096 b)
def i3137 : RationalInterval := ⟨(185812005224829487129648414407 / 250000000000000000000000000000 : ℚ), (47230422948622101278982054033 / 62500000000000000000000000000 : ℚ)⟩
theorem b3137 (b : ℝ) (hb : rootInterval.Contains b) : i3137.Contains (n3137 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b3023 b hb) (b3096 b hb))
    (by norm_num [i3137, i3023, i3096, RationalInterval.mul]) (by norm_num [i3137, i3023, i3096, RationalInterval.mul])

def n3138 (b : ℝ) : ℝ := (n3136 b) + (n3137 b)
def i3138 : RationalInterval := ⟨(-239600357076653994017694675033 / 1000000000000000000000000000000 : ℚ), (-40213284550671710444098286999 / 500000000000000000000000000000 : ℚ)⟩
theorem b3138 (b : ℝ) (hb : rootInterval.Contains b) : i3138.Contains (n3138 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3136 b hb) (b3137 b hb))
    (by norm_num [i3138, i3136, i3137, RationalInterval.add]) (by norm_num [i3138, i3136, i3137, RationalInterval.add])

def n3139 (b : ℝ) : ℝ := (n3002 b) * (n3099 b)
def i3139 : RationalInterval := ⟨(-123256571628945582511806411857 / 500000000000000000000000000000 : ℚ), (-121261670648255766380303495867 / 500000000000000000000000000000 : ℚ)⟩
theorem b3139 (b : ℝ) (hb : rootInterval.Contains b) : i3139.Contains (n3139 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b3002 b hb) (b3099 b hb))
    (by norm_num [i3139, i3002, i3099, RationalInterval.mul]) (by norm_num [i3139, i3002, i3099, RationalInterval.mul])

def n3140 (b : ℝ) : ℝ := (n3009 b) * (n3101 b)
def i3140 : RationalInterval := ⟨(589017201702622681892728419 / 100000000000000000000000000000 : ℚ), (6028069914305869905242976211 / 1000000000000000000000000000000 : ℚ)⟩
theorem b3140 (b : ℝ) (hb : rootInterval.Contains b) : i3140.Contains (n3140 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b3009 b hb) (b3101 b hb))
    (by norm_num [i3140, i3009, i3101, RationalInterval.mul]) (by norm_num [i3140, i3009, i3101, RationalInterval.mul])

def n3141 (b : ℝ) : ℝ := (n3139 b) + (n3140 b)
def i3141 : RationalInterval := ⟨(-60155742810216234551171384881 / 250000000000000000000000000000 : ℚ), (-236495271382205662855364015523 / 1000000000000000000000000000000 : ℚ)⟩
theorem b3141 (b : ℝ) (hb : rootInterval.Contains b) : i3141.Contains (n3141 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3139 b hb) (b3140 b hb))
    (by norm_num [i3141, i3139, i3140, RationalInterval.add]) (by norm_num [i3141, i3139, i3140, RationalInterval.add])

def n3142 (b : ℝ) : ℝ := (n3016 b) * (n3104 b)
def i3142 : RationalInterval := ⟨(63892093447065528499437133841 / 500000000000000000000000000000 : ℚ), (130558401894653025272778364987 / 1000000000000000000000000000000 : ℚ)⟩
theorem b3142 (b : ℝ) (hb : rootInterval.Contains b) : i3142.Contains (n3142 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b3016 b hb) (b3104 b hb))
    (by norm_num [i3142, i3016, i3104, RationalInterval.mul]) (by norm_num [i3142, i3016, i3104, RationalInterval.mul])

def n3143 (b : ℝ) : ℝ := (n3141 b) + (n3142 b)
def i3143 : RationalInterval := ⟨(-56419392173366940602905635921 / 500000000000000000000000000000 : ℚ), (-13242108685944079697823206317 / 125000000000000000000000000000 : ℚ)⟩
theorem b3143 (b : ℝ) (hb : rootInterval.Contains b) : i3143.Contains (n3143 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3141 b hb) (b3142 b hb))
    (by norm_num [i3143, i3141, i3142, RationalInterval.add]) (by norm_num [i3143, i3141, i3142, RationalInterval.add])

def n3144 (b : ℝ) : ℝ := (n3023 b) * (n3107 b)
def i3144 : RationalInterval := ⟨(24117788975105368030922295897 / 125000000000000000000000000000 : ℚ), (19617132875806293893900101071 / 100000000000000000000000000000 : ℚ)⟩
theorem b3144 (b : ℝ) (hb : rootInterval.Contains b) : i3144.Contains (n3144 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b3023 b hb) (b3107 b hb))
    (by norm_num [i3144, i3023, i3107, RationalInterval.mul]) (by norm_num [i3144, i3023, i3107, RationalInterval.mul])

def n3145 (b : ℝ) : ℝ := (n3143 b) + (n3144 b)
def i3145 : RationalInterval := ⟨(40051763727054531520783547667 / 500000000000000000000000000000 : ℚ), (45117229635255150678207680087 / 500000000000000000000000000000 : ℚ)⟩
theorem b3145 (b : ℝ) (hb : rootInterval.Contains b) : i3145.Contains (n3145 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3143 b hb) (b3144 b hb))
    (by norm_num [i3145, i3143, i3144, RationalInterval.add]) (by norm_num [i3145, i3143, i3144, RationalInterval.add])

def n3146 (b : ℝ) : ℝ := (n3002 b) * (n3110 b)
def i3146 : RationalInterval := ⟨(120081658290112829095376341937 / 500000000000000000000000000000 : ℚ), (244114293283831731842643495313 / 1000000000000000000000000000000 : ℚ)⟩
theorem b3146 (b : ℝ) (hb : rootInterval.Contains b) : i3146.Contains (n3146 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b3002 b hb) (b3110 b hb))
    (by norm_num [i3146, i3002, i3110, RationalInterval.mul]) (by norm_num [i3146, i3002, i3110, RationalInterval.mul])

def n3147 (b : ℝ) : ℝ := (n3009 b) * (n3112 b)
def i3147 : RationalInterval := ⟨(-1003983217464433664587318395613 / 250000000000000000000000000000 : ℚ), (-3924064542807424935573831897529 / 1000000000000000000000000000000 : ℚ)⟩
theorem b3147 (b : ℝ) (hb : rootInterval.Contains b) : i3147.Contains (n3147 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b3009 b hb) (b3112 b hb))
    (by norm_num [i3147, i3009, i3112, RationalInterval.mul]) (by norm_num [i3147, i3009, i3112, RationalInterval.mul])

def n3148 (b : ℝ) : ℝ := (n3146 b) + (n3147 b)
def i3148 : RationalInterval := ⟨(-1887884776638754500079260449289 / 500000000000000000000000000000 : ℚ), (-459993781190449150466398550277 / 125000000000000000000000000000 : ℚ)⟩
theorem b3148 (b : ℝ) (hb : rootInterval.Contains b) : i3148.Contains (n3148 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3146 b hb) (b3147 b hb))
    (by norm_num [i3148, i3146, i3147, RationalInterval.add]) (by norm_num [i3148, i3146, i3147, RationalInterval.add])

def n3149 (b : ℝ) : ℝ := (n3016 b) * (n3115 b)
def i3149 : RationalInterval := ⟨(462171057323817952889810650903 / 200000000000000000000000000000 : ℚ), (472204864410582943629775723111 / 200000000000000000000000000000 : ℚ)⟩
theorem b3149 (b : ℝ) (hb : rootInterval.Contains b) : i3149.Contains (n3149 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b3016 b hb) (b3115 b hb))
    (by norm_num [i3149, i3016, i3115, RationalInterval.mul]) (by norm_num [i3149, i3016, i3115, RationalInterval.mul])

