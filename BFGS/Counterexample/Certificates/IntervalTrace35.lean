import BFGS.Counterexample.Certificates.IntervalTrace34

/-! Generated arithmetic proofs. Each bound is checked by the Lean kernel. -/
namespace BFGS.Counterexample.Trace
noncomputable section
open BFGS RationalInterval
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false

def n3150 (b : ℝ) : ℝ := (n3148 b) + (n3149 b)
def i3150 : RationalInterval := ⟨(-1464914266658419235709467644063 / 1000000000000000000000000000000 : ℚ), (-1318925927470678485582309786661 / 1000000000000000000000000000000 : ℚ)⟩
theorem b3150 (b : ℝ) (hb : rootInterval.Contains b) : i3150.Contains (n3150 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3148 b hb) (b3149 b hb))
    (by norm_num [i3150, i3148, i3149, RationalInterval.add]) (by norm_num [i3150, i3148, i3149, RationalInterval.add])

def n3151 (b : ℝ) : ℝ := (n3023 b) * (n3118 b)
def i3151 : RationalInterval := ⟨(27434761405324086145270574007 / 20000000000000000000000000000 : ℚ), (348673753103344379200806833881 / 250000000000000000000000000000 : ℚ)⟩
theorem b3151 (b : ℝ) (hb : rootInterval.Contains b) : i3151.Contains (n3151 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b3023 b hb) (b3118 b hb))
    (by norm_num [i3151, i3023, i3118, RationalInterval.mul]) (by norm_num [i3151, i3023, i3118, RationalInterval.mul])

def n3152 (b : ℝ) : ℝ := (n3150 b) + (n3151 b)
def i3152 : RationalInterval := ⟨(-93176196392214928445938943713 / 1000000000000000000000000000000 : ℚ), (75769084942699031220917548863 / 1000000000000000000000000000000 : ℚ)⟩
theorem b3152 (b : ℝ) (hb : rootInterval.Contains b) : i3152.Contains (n3152 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3150 b hb) (b3151 b hb))
    (by norm_num [i3152, i3150, i3151, RationalInterval.add]) (by norm_num [i3152, i3150, i3151, RationalInterval.add])

def n3153 (b : ℝ) : ℝ := (n3002 b) * (n3121 b)
def i3153 : RationalInterval := ⟨(-767087057477200712644250565383 / 1000000000000000000000000000000 : ℚ), (-188667948680181241878515850121 / 250000000000000000000000000000 : ℚ)⟩
theorem b3153 (b : ℝ) (hb : rootInterval.Contains b) : i3153.Contains (n3153 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b3002 b hb) (b3121 b hb))
    (by norm_num [i3153, i3002, i3121, RationalInterval.mul]) (by norm_num [i3153, i3002, i3121, RationalInterval.mul])

def n3154 (b : ℝ) : ℝ := (n3009 b) * (n3123 b)
def i3154 : RationalInterval := ⟨(4612720712654858059696652087 / 250000000000000000000000000000 : ℚ), (944142305884255201248387749 / 50000000000000000000000000000 : ℚ)⟩
theorem b3154 (b : ℝ) (hb : rootInterval.Contains b) : i3154.Contains (n3154 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b3009 b hb) (b3123 b hb))
    (by norm_num [i3154, i3009, i3123, RationalInterval.mul]) (by norm_num [i3154, i3009, i3123, RationalInterval.mul])

def n3155 (b : ℝ) : ℝ := (n3153 b) + (n3154 b)
def i3155 : RationalInterval := ⟨(-149727234925316256081092791407 / 200000000000000000000000000000 : ℚ), (-11496702321922497867017119461 / 15625000000000000000000000000 : ℚ)⟩
theorem b3155 (b : ℝ) (hb : rootInterval.Contains b) : i3155.Contains (n3155 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3153 b hb) (b3154 b hb))
    (by norm_num [i3155, i3153, i3154, RationalInterval.add]) (by norm_num [i3155, i3153, i3154, RationalInterval.add])

def n3156 (b : ℝ) : ℝ := (n3016 b) * (n3126 b)
def i3156 : RationalInterval := ⟨(352424032695795523715599478739 / 1000000000000000000000000000000 : ℚ), (360075214440678738936067346067 / 1000000000000000000000000000000 : ℚ)⟩
theorem b3156 (b : ℝ) (hb : rootInterval.Contains b) : i3156.Contains (n3156 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b3016 b hb) (b3126 b hb))
    (by norm_num [i3156, i3016, i3126, RationalInterval.mul]) (by norm_num [i3156, i3016, i3126, RationalInterval.mul])

def n3157 (b : ℝ) : ℝ := (n3155 b) + (n3156 b)
def i3157 : RationalInterval := ⟨(-49526517741348219586233059787 / 125000000000000000000000000000 : ℚ), (-375713734162361124553028299437 / 1000000000000000000000000000000 : ℚ)⟩
theorem b3157 (b : ℝ) (hb : rootInterval.Contains b) : i3157.Contains (n3157 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3155 b hb) (b3156 b hb))
    (by norm_num [i3157, i3155, i3156, RationalInterval.add]) (by norm_num [i3157, i3155, i3156, RationalInterval.add])

def n3158 (b : ℝ) : ℝ := (n3023 b) * (n3129 b)
def i3158 : RationalInterval := ⟨(38202349137653373121965944089 / 100000000000000000000000000000 : ℚ), (7768338133885841302509620681 / 20000000000000000000000000000 : ℚ)⟩
theorem b3158 (b : ℝ) (hb : rootInterval.Contains b) : i3158.Contains (n3158 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b3023 b hb) (b3129 b hb))
    (by norm_num [i3158, i3023, i3129, RationalInterval.mul]) (by norm_num [i3158, i3023, i3129, RationalInterval.mul])

def n3159 (b : ℝ) : ℝ := (n3157 b) + (n3158 b)
def i3159 : RationalInterval := ⟨(-7094325277126012735102518703 / 500000000000000000000000000000 : ℚ), (12703172531930940572452734613 / 1000000000000000000000000000000 : ℚ)⟩
theorem b3159 (b : ℝ) (hb : rootInterval.Contains b) : i3159.Contains (n3159 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3157 b hb) (b3158 b hb))
    (by norm_num [i3159, i3157, i3158, RationalInterval.add]) (by norm_num [i3159, i3157, i3158, RationalInterval.add])

def n3160 (b : ℝ) : ℝ := (n3034 b) * (n3088 b)
def i3160 : RationalInterval := ⟨(-4936838048897333161784800114761 / 1000000000000000000000000000000 : ℚ), (-4928634875650518492436251596113 / 1000000000000000000000000000000 : ℚ)⟩
theorem b3160 (b : ℝ) (hb : rootInterval.Contains b) : i3160.Contains (n3160 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b3034 b hb) (b3088 b hb))
    (by norm_num [i3160, i3034, i3088, RationalInterval.mul]) (by norm_num [i3160, i3034, i3088, RationalInterval.mul])

def n3161 (b : ℝ) : ℝ := (n3041 b) * (n3090 b)
def i3161 : RationalInterval := ⟨(5764985411404388673060854644033 / 250000000000000000000000000000 : ℚ), (11550779207517454304786745219383 / 500000000000000000000000000000 : ℚ)⟩
theorem b3161 (b : ℝ) (hb : rootInterval.Contains b) : i3161.Contains (n3161 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b3041 b hb) (b3090 b hb))
    (by norm_num [i3161, i3041, i3090, RationalInterval.mul]) (by norm_num [i3161, i3041, i3090, RationalInterval.mul])

def n3162 (b : ℝ) : ℝ := (n3160 b) + (n3161 b)
def i3162 : RationalInterval := ⟨(18123103596720221530458618461371 / 1000000000000000000000000000000 : ℚ), (18172923539384390117137238842653 / 1000000000000000000000000000000 : ℚ)⟩
theorem b3162 (b : ℝ) (hb : rootInterval.Contains b) : i3162.Contains (n3162 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3160 b hb) (b3161 b hb))
    (by norm_num [i3162, i3160, i3161, RationalInterval.add]) (by norm_num [i3162, i3160, i3161, RationalInterval.add])

def n3163 (b : ℝ) : ℝ := (n3048 b) * (n3093 b)
def i3163 : RationalInterval := ⟨(-19105262955846115831511928669151 / 1000000000000000000000000000000 : ℚ), (-19086663574124761775928697089369 / 1000000000000000000000000000000 : ℚ)⟩
theorem b3163 (b : ℝ) (hb : rootInterval.Contains b) : i3163.Contains (n3163 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b3048 b hb) (b3093 b hb))
    (by norm_num [i3163, i3048, i3093, RationalInterval.mul]) (by norm_num [i3163, i3048, i3093, RationalInterval.mul])

def n3164 (b : ℝ) : ℝ := (n3162 b) + (n3163 b)
def i3164 : RationalInterval := ⟨(-49107967956294715052665510389 / 50000000000000000000000000000 : ℚ), (-228435008685092914697864561679 / 250000000000000000000000000000 : ℚ)⟩
theorem b3164 (b : ℝ) (hb : rootInterval.Contains b) : i3164.Contains (n3164 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3162 b hb) (b3163 b hb))
    (by norm_num [i3164, i3162, i3163, RationalInterval.add]) (by norm_num [i3164, i3162, i3163, RationalInterval.add])

def n3165 (b : ℝ) : ℝ := (n3055 b) * (n3096 b)
def i3165 : RationalInterval := ⟨(940868146584471343694710429723 / 1000000000000000000000000000000 : ℚ), (236661112052928194880634751311 / 250000000000000000000000000000 : ℚ)⟩
theorem b3165 (b : ℝ) (hb : rootInterval.Contains b) : i3165.Contains (n3165 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b3055 b hb) (b3096 b hb))
    (by norm_num [i3165, i3055, i3096, RationalInterval.mul]) (by norm_num [i3165, i3055, i3096, RationalInterval.mul])

def n3166 (b : ℝ) : ℝ := (n3164 b) + (n3165 b)
def i3166 : RationalInterval := ⟨(-41291212541422957358599778057 / 1000000000000000000000000000000 : ℚ), (128532865122426252855784213 / 3906250000000000000000000000 : ℚ)⟩
theorem b3166 (b : ℝ) (hb : rootInterval.Contains b) : i3166.Contains (n3166 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3164 b hb) (b3165 b hb))
    (by norm_num [i3166, i3164, i3165, RationalInterval.add]) (by norm_num [i3166, i3164, i3165, RationalInterval.add])

def n3167 (b : ℝ) : ℝ := (n3034 b) * (n3099 b)
def i3167 : RationalInterval := ⟨(8725997827605482557688824817 / 7812500000000000000000000000 : ℚ), (1118786725864277069426486490311 / 1000000000000000000000000000000 : ℚ)⟩
theorem b3167 (b : ℝ) (hb : rootInterval.Contains b) : i3167.Contains (n3167 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b3034 b hb) (b3099 b hb))
    (by norm_num [i3167, i3034, i3099, RationalInterval.mul]) (by norm_num [i3167, i3034, i3099, RationalInterval.mul])

def n3168 (b : ℝ) : ℝ := (n3041 b) * (n3101 b)
def i3168 : RationalInterval := ⟨(-17872583603153397226860556739 / 500000000000000000000000000000 : ℚ), (-35680773352234963738781407597 / 1000000000000000000000000000000 : ℚ)⟩
theorem b3168 (b : ℝ) (hb : rootInterval.Contains b) : i3168.Contains (n3168 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b3041 b hb) (b3101 b hb))
    (by norm_num [i3168, i3041, i3101, RationalInterval.mul]) (by norm_num [i3168, i3041, i3101, RationalInterval.mul])

def n3169 (b : ℝ) : ℝ := (n3167 b) + (n3168 b)
def i3169 : RationalInterval := ⟨(540591277363597486465224231549 / 500000000000000000000000000000 : ℚ), (541552976256021052843852541357 / 500000000000000000000000000000 : ℚ)⟩
theorem b3169 (b : ℝ) (hb : rootInterval.Contains b) : i3169.Contains (n3169 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3167 b hb) (b3168 b hb))
    (by norm_num [i3169, i3167, i3168, RationalInterval.add]) (by norm_num [i3169, i3167, i3168, RationalInterval.add])

def n3170 (b : ℝ) : ℝ := (n3048 b) * (n3104 b)
def i3170 : RationalInterval := ⟨(-662393171941628155139304487151 / 500000000000000000000000000000 : ℚ), (-330874159017491486368261670063 / 250000000000000000000000000000 : ℚ)⟩
theorem b3170 (b : ℝ) (hb : rootInterval.Contains b) : i3170.Contains (n3170 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b3048 b hb) (b3104 b hb))
    (by norm_num [i3170, i3048, i3104, RationalInterval.mul]) (by norm_num [i3170, i3048, i3104, RationalInterval.mul])

def n3171 (b : ℝ) : ℝ := (n3169 b) + (n3170 b)
def i3171 : RationalInterval := ⟨(-60900947289015334337040127801 / 250000000000000000000000000000 : ℚ), (-120195341778961919892670798769 / 500000000000000000000000000000 : ℚ)⟩
theorem b3171 (b : ℝ) (hb : rootInterval.Contains b) : i3171.Contains (n3171 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3169 b hb) (b3170 b hb))
    (by norm_num [i3171, i3169, i3170, RationalInterval.add]) (by norm_num [i3171, i3169, i3170, RationalInterval.add])

def n3172 (b : ℝ) : ℝ := (n3055 b) * (n3107 b)
def i3172 : RationalInterval := ⟨(244243200381657230002667129369 / 1000000000000000000000000000000 : ℚ), (245742690401516839311974335461 / 1000000000000000000000000000000 : ℚ)⟩
theorem b3172 (b : ℝ) (hb : rootInterval.Contains b) : i3172.Contains (n3172 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b3055 b hb) (b3107 b hb))
    (by norm_num [i3172, i3055, i3107, RationalInterval.mul]) (by norm_num [i3172, i3055, i3107, RationalInterval.mul])

def n3173 (b : ℝ) : ℝ := (n3171 b) + (n3172 b)
def i3173 : RationalInterval := ⟨(127882245119178530901323633 / 200000000000000000000000000000 : ℚ), (5352006843592999526632737923 / 1000000000000000000000000000000 : ℚ)⟩
theorem b3173 (b : ℝ) (hb : rootInterval.Contains b) : i3173.Contains (n3173 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3171 b hb) (b3172 b hb))
    (by norm_num [i3173, i3171, i3172, RationalInterval.add]) (by norm_num [i3173, i3171, i3172, RationalInterval.add])

def n3174 (b : ℝ) : ℝ := (n3034 b) * (n3110 b)
def i3174 : RationalInterval := ⟨(-110789967346273479302964529719 / 100000000000000000000000000000 : ℚ), (-110605875972979714305695955441 / 100000000000000000000000000000 : ℚ)⟩
theorem b3174 (b : ℝ) (hb : rootInterval.Contains b) : i3174.Contains (n3174 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b3034 b hb) (b3110 b hb))
    (by norm_num [i3174, i3034, i3110, RationalInterval.mul]) (by norm_num [i3174, i3034, i3110, RationalInterval.mul])

def n3175 (b : ℝ) : ℝ := (n3041 b) * (n3112 b)
def i3175 : RationalInterval := ⟨(23770724720216573140558799272053 / 1000000000000000000000000000000 : ℚ), (2976703031879524534071391288833 / 125000000000000000000000000000 : ℚ)⟩
theorem b3175 (b : ℝ) (hb : rootInterval.Contains b) : i3175.Contains (n3175 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b3041 b hb) (b3112 b hb))
    (by norm_num [i3175, i3041, i3112, RationalInterval.mul]) (by norm_num [i3175, i3041, i3112, RationalInterval.mul])

def n3176 (b : ℝ) : ℝ := (n3174 b) + (n3175 b)
def i3176 : RationalInterval := ⟨(22662825046753838347529153974863 / 1000000000000000000000000000000 : ℚ), (11353782747653199564757085378127 / 500000000000000000000000000000 : ℚ)⟩
theorem b3176 (b : ℝ) (hb : rootInterval.Contains b) : i3176.Contains (n3176 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3174 b hb) (b3175 b hb))
    (by norm_num [i3176, i3174, i3175, RationalInterval.add]) (by norm_num [i3176, i3174, i3175, RationalInterval.add])

def n3177 (b : ℝ) : ℝ := (n3048 b) * (n3115 b)
def i3177 : RationalInterval := ⟨(-4791499794790341891681807291517 / 200000000000000000000000000000 : ℚ), (-11967087918393017553313027679881 / 500000000000000000000000000000 : ℚ)⟩
theorem b3177 (b : ℝ) (hb : rootInterval.Contains b) : i3177.Contains (n3177 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b3048 b hb) (b3115 b hb))
    (by norm_num [i3177, i3048, i3115, RationalInterval.mul]) (by norm_num [i3177, i3048, i3115, RationalInterval.mul])

def n3178 (b : ℝ) : ℝ := (n3176 b) + (n3177 b)
def i3178 : RationalInterval := ⟨(-647336963598935555439941241361 / 500000000000000000000000000000 : ℚ), (-306652585369908994277971150877 / 250000000000000000000000000000 : ℚ)⟩
theorem b3178 (b : ℝ) (hb : rootInterval.Contains b) : i3178.Contains (n3178 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3176 b hb) (b3177 b hb))
    (by norm_num [i3178, i3176, i3177, RationalInterval.add]) (by norm_num [i3178, i3176, i3177, RationalInterval.add])

def n3179 (b : ℝ) : ℝ := (n3055 b) * (n3118 b)
def i3179 : RationalInterval := ⟨(434116411843615890994271970473 / 250000000000000000000000000000 : ℚ), (54597699560930572337859550381 / 31250000000000000000000000000 : ℚ)⟩
theorem b3179 (b : ℝ) (hb : rootInterval.Contains b) : i3179.Contains (n3179 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b3055 b hb) (b3118 b hb))
    (by norm_num [i3179, i3055, i3118, RationalInterval.mul]) (by norm_num [i3179, i3055, i3118, RationalInterval.mul])

def n3180 (b : ℝ) : ℝ := (n3178 b) + (n3179 b)
def i3180 : RationalInterval := ⟨(44179172017659245309720539917 / 100000000000000000000000000000 : ℚ), (130129011117535584424905252171 / 250000000000000000000000000000 : ℚ)⟩
theorem b3180 (b : ℝ) (hb : rootInterval.Contains b) : i3180.Contains (n3180 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3178 b hb) (b3179 b hb))
    (by norm_num [i3180, i3178, i3179, RationalInterval.add]) (by norm_num [i3180, i3178, i3179, RationalInterval.add])

def n3181 (b : ℝ) : ℝ := (n3034 b) * (n3121 b)
def i3181 : RationalInterval := ⟨(139023954391974416750251758781 / 40000000000000000000000000000 : ℚ), (3481383613651633274091086115131 / 1000000000000000000000000000000 : ℚ)⟩
theorem b3181 (b : ℝ) (hb : rootInterval.Contains b) : i3181.Contains (n3181 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b3034 b hb) (b3121 b hb))
    (by norm_num [i3181, i3034, i3121, RationalInterval.mul]) (by norm_num [i3181, i3034, i3121, RationalInterval.mul])

def n3182 (b : ℝ) : ℝ := (n3041 b) * (n3123 b)
def i3182 : RationalInterval := ⟨(-6998202797525716822070872653 / 62500000000000000000000000000 : ℚ), (-55884765948989055107148208357 / 500000000000000000000000000000 : ℚ)⟩
theorem b3182 (b : ℝ) (hb : rootInterval.Contains b) : i3182.Contains (n3182 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b3041 b hb) (b3123 b hb))
    (by norm_num [i3182, i3041, i3123, RationalInterval.mul]) (by norm_num [i3182, i3041, i3123, RationalInterval.mul])

def n3183 (b : ℝ) : ℝ := (n3181 b) + (n3182 b)
def i3183 : RationalInterval := ⟨(3363627615038948949603160007077 / 1000000000000000000000000000000 : ℚ), (3369614081753655163876789698417 / 1000000000000000000000000000000 : ℚ)⟩
theorem b3183 (b : ℝ) (hb : rootInterval.Contains b) : i3183.Contains (n3183 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3181 b hb) (b3182 b hb))
    (by norm_num [i3183, i3181, i3182, RationalInterval.add]) (by norm_num [i3183, i3181, i3182, RationalInterval.add])

def n3184 (b : ℝ) : ℝ := (n3048 b) * (n3126 b)
def i3184 : RationalInterval := ⟨(-3653711442077498231570848226027 / 1000000000000000000000000000000 : ℚ), (-3650154475917548888835974155057 / 1000000000000000000000000000000 : ℚ)⟩
theorem b3184 (b : ℝ) (hb : rootInterval.Contains b) : i3184.Contains (n3184 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b3048 b hb) (b3126 b hb))
    (by norm_num [i3184, i3048, i3126, RationalInterval.mul]) (by norm_num [i3184, i3048, i3126, RationalInterval.mul])

def n3185 (b : ℝ) : ℝ := (n3183 b) + (n3184 b)
def i3185 : RationalInterval := ⟨(-5801676540770985639353764379 / 20000000000000000000000000000 : ℚ), (-876688731762167890497451427 / 3125000000000000000000000000 : ℚ)⟩
theorem b3185 (b : ℝ) (hb : rootInterval.Contains b) : i3185.Contains (n3185 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3183 b hb) (b3184 b hb))
    (by norm_num [i3185, i3183, i3184, RationalInterval.add]) (by norm_num [i3185, i3183, i3184, RationalInterval.add])

def n3186 (b : ℝ) : ℝ := (n3055 b) * (n3129 b)
def i3186 : RationalInterval := ⟨(483598642951324812734152061097 / 1000000000000000000000000000000 : ℚ), (486567615424622052308717099351 / 1000000000000000000000000000000 : ℚ)⟩
theorem b3186 (b : ℝ) (hb : rootInterval.Contains b) : i3186.Contains (n3186 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b3055 b hb) (b3129 b hb))
    (by norm_num [i3186, i3055, i3129, RationalInterval.mul]) (by norm_num [i3186, i3055, i3129, RationalInterval.mul])

def n3187 (b : ℝ) : ℝ := (n3185 b) + (n3186 b)
def i3187 : RationalInterval := ⟨(193514815912775530766463842147 / 1000000000000000000000000000000 : ℚ), (206027221260728327349532642711 / 1000000000000000000000000000000 : ℚ)⟩
theorem b3187 (b : ℝ) (hb : rootInterval.Contains b) : i3187.Contains (n3187 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3185 b hb) (b3186 b hb))
    (by norm_num [i3187, i3185, i3186, RationalInterval.add]) (by norm_num [i3187, i3185, i3186, RationalInterval.add])

def n3188 (b : ℝ) : ℝ := (n3066 b) * (n3088 b)
def i3188 : RationalInterval := ⟨(2247906471478116105162779602823 / 1000000000000000000000000000000 : ℚ), (450361230174004575501345480117 / 200000000000000000000000000000 : ℚ)⟩
theorem b3188 (b : ℝ) (hb : rootInterval.Contains b) : i3188.Contains (n3188 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b3066 b hb) (b3088 b hb))
    (by norm_num [i3188, i3066, i3088, RationalInterval.mul]) (by norm_num [i3188, i3066, i3088, RationalInterval.mul])

def n3189 (b : ℝ) : ℝ := (n3073 b) * (n3090 b)
def i3189 : RationalInterval := ⟨(-2245768689459970431702679078761 / 125000000000000000000000000000 : ℚ), (-8973148047241597500297547554601 / 500000000000000000000000000000 : ℚ)⟩
theorem b3189 (b : ℝ) (hb : rootInterval.Contains b) : i3189.Contains (n3189 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b3073 b hb) (b3090 b hb))
    (by norm_num [i3189, i3073, i3090, RationalInterval.mul]) (by norm_num [i3189, i3073, i3090, RationalInterval.mul])

def n3190 (b : ℝ) : ℝ := (n3188 b) + (n3189 b)
def i3190 : RationalInterval := ⟨(-3143648608840329469691730605453 / 200000000000000000000000000000 : ℚ), (-15694489943613172123088367708617 / 1000000000000000000000000000000 : ℚ)⟩
theorem b3190 (b : ℝ) (hb : rootInterval.Contains b) : i3190.Contains (n3190 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3188 b hb) (b3189 b hb))
    (by norm_num [i3190, i3188, i3189, RationalInterval.add]) (by norm_num [i3190, i3188, i3189, RationalInterval.add])

def n3191 (b : ℝ) : ℝ := (n3080 b) * (n3093 b)
def i3191 : RationalInterval := ⟨(9450438565910824595686158146623 / 500000000000000000000000000000 : ℚ), (4727423609172249826847510218087 / 250000000000000000000000000000 : ℚ)⟩
theorem b3191 (b : ℝ) (hb : rootInterval.Contains b) : i3191.Contains (n3191 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b3080 b hb) (b3093 b hb))
    (by norm_num [i3191, i3080, i3093, RationalInterval.mul]) (by norm_num [i3191, i3080, i3093, RationalInterval.mul])

def n3192 (b : ℝ) : ℝ := (n3190 b) + (n3191 b)
def i3192 : RationalInterval := ⟨(3182634087620001842913663265981 / 1000000000000000000000000000000 : ℚ), (3215204493075827184301673163731 / 1000000000000000000000000000000 : ℚ)⟩
theorem b3192 (b : ℝ) (hb : rootInterval.Contains b) : i3192.Contains (n3192 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3190 b hb) (b3191 b hb))
    (by norm_num [i3192, i3190, i3191, RationalInterval.add]) (by norm_num [i3192, i3190, i3191, RationalInterval.add])

def n3193 (b : ℝ) : ℝ := (n3087 b) * (n3096 b)
def i3193 : RationalInterval := ⟨(-3194926328713326415739096518203 / 1000000000000000000000000000000 : ℚ), (-1596096718932930503077978381683 / 500000000000000000000000000000 : ℚ)⟩
theorem b3193 (b : ℝ) (hb : rootInterval.Contains b) : i3193.Contains (n3193 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b3087 b hb) (b3096 b hb))
    (by norm_num [i3193, i3087, i3096, RationalInterval.mul]) (by norm_num [i3193, i3087, i3096, RationalInterval.mul])

def n3194 (b : ℝ) : ℝ := (n3192 b) + (n3193 b)
def i3194 : RationalInterval := ⟨(-6146120546662286412716626111 / 500000000000000000000000000000 : ℚ), (4602211041993235629143280073 / 200000000000000000000000000000 : ℚ)⟩
theorem b3194 (b : ℝ) (hb : rootInterval.Contains b) : i3194.Contains (n3194 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3192 b hb) (b3193 b hb))
    (by norm_num [i3194, i3192, i3193, RationalInterval.add]) (by norm_num [i3194, i3192, i3193, RationalInterval.add])

def n3195 (b : ℝ) : ℝ := (n3066 b) * (n3099 b)
def i3195 : RationalInterval := ⟨(-255152266071965749593238487183 / 500000000000000000000000000000 : ℚ), (-509420786415273000874799111523 / 1000000000000000000000000000000 : ℚ)⟩
theorem b3195 (b : ℝ) (hb : rootInterval.Contains b) : i3195.Contains (n3195 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b3066 b hb) (b3099 b hb))
    (by norm_num [i3195, i3066, i3099, RationalInterval.mul]) (by norm_num [i3195, i3066, i3099, RationalInterval.mul])

def n3196 (b : ℝ) : ℝ := (n3073 b) * (n3101 b)
def i3196 : RationalInterval := ⟨(6942100432212584209609122543 / 250000000000000000000000000000 : ℚ), (6949780258910192550354416937 / 250000000000000000000000000000 : ℚ)⟩
theorem b3196 (b : ℝ) (hb : rootInterval.Contains b) : i3196.Contains (n3196 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b3073 b hb) (b3101 b hb))
    (by norm_num [i3196, i3073, i3101, RationalInterval.mul]) (by norm_num [i3196, i3073, i3101, RationalInterval.mul])

def n3197 (b : ℝ) : ℝ := (n3195 b) + (n3196 b)
def i3197 : RationalInterval := ⟨(-241268065207540581174020242097 / 500000000000000000000000000000 : ℚ), (-19264866615185289226935257751 / 40000000000000000000000000000 : ℚ)⟩
theorem b3197 (b : ℝ) (hb : rootInterval.Contains b) : i3197.Contains (n3197 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3195 b hb) (b3196 b hb))
    (by norm_num [i3197, i3195, i3196, RationalInterval.add]) (by norm_num [i3197, i3195, i3196, RationalInterval.add])

def n3198 (b : ℝ) : ℝ := (n3080 b) * (n3104 b)
def i3198 : RationalInterval := ⟨(327653484402718593141399889127 / 250000000000000000000000000000 : ℚ), (655612671090328964192839324873 / 500000000000000000000000000000 : ℚ)⟩
theorem b3198 (b : ℝ) (hb : rootInterval.Contains b) : i3198.Contains (n3198 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b3080 b hb) (b3104 b hb))
    (by norm_num [i3198, i3080, i3104, RationalInterval.mul]) (by norm_num [i3198, i3080, i3104, RationalInterval.mul])

def n3199 (b : ℝ) : ℝ := (n3197 b) + (n3198 b)
def i3199 : RationalInterval := ⟨(414038903597896605108779536157 / 500000000000000000000000000000 : ℚ), (829603676801025697712297205971 / 1000000000000000000000000000000 : ℚ)⟩
theorem b3199 (b : ℝ) (hb : rootInterval.Contains b) : i3199.Contains (n3199 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3197 b hb) (b3198 b hb))
    (by norm_num [i3199, i3197, i3198, RationalInterval.add]) (by norm_num [i3199, i3197, i3198, RationalInterval.add])

def n3200 (b : ℝ) : ℝ := (n3087 b) * (n3107 b)
def i3200 : RationalInterval := ⟨(-829381921729776036943717350407 / 1000000000000000000000000000000 : ℚ), (-828672481188822657265373467543 / 1000000000000000000000000000000 : ℚ)⟩
theorem b3200 (b : ℝ) (hb : rootInterval.Contains b) : i3200.Contains (n3200 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b3087 b hb) (b3107 b hb))
    (by norm_num [i3200, i3087, i3107, RationalInterval.mul]) (by norm_num [i3200, i3087, i3107, RationalInterval.mul])

def n3201 (b : ℝ) : ℝ := (n3199 b) + (n3200 b)
def i3201 : RationalInterval := ⟨(-1304114533982826726158278093 / 1000000000000000000000000000000 : ℚ), (232798903050760111730934607 / 250000000000000000000000000000 : ℚ)⟩
theorem b3201 (b : ℝ) (hb : rootInterval.Contains b) : i3201.Contains (n3201 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3199 b hb) (b3200 b hb))
    (by norm_num [i3201, i3199, i3200, RationalInterval.add]) (by norm_num [i3201, i3199, i3200, RationalInterval.add])

def n3202 (b : ℝ) : ℝ := (n3066 b) * (n3110 b)
def i3202 : RationalInterval := ⟨(100892709911017981340426236639 / 200000000000000000000000000000 : ℚ), (505338695444444706099172989703 / 1000000000000000000000000000000 : ℚ)⟩
theorem b3202 (b : ℝ) (hb : rootInterval.Contains b) : i3202.Contains (n3202 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b3066 b hb) (b3110 b hb))
    (by norm_num [i3202, i3066, i3110, RationalInterval.mul]) (by norm_num [i3202, i3066, i3110, RationalInterval.mul])

def n3203 (b : ℝ) : ℝ := (n3073 b) * (n3112 b)
def i3203 : RationalInterval := ⟨(-9259962600569688029823080668171 / 500000000000000000000000000000 : ℚ), (-18499459832350906910040865947337 / 1000000000000000000000000000000 : ℚ)⟩
theorem b3203 (b : ℝ) (hb : rootInterval.Contains b) : i3203.Contains (n3203 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b3073 b hb) (b3112 b hb))
    (by norm_num [i3203, i3073, i3112, RationalInterval.mul]) (by norm_num [i3203, i3073, i3112, RationalInterval.mul])

def n3204 (b : ℝ) : ℝ := (n3202 b) + (n3203 b)
def i3204 : RationalInterval := ⟨(-18015461651584286152944030153147 / 1000000000000000000000000000000 : ℚ), (-8997060568453231101970846478817 / 500000000000000000000000000000 : ℚ)⟩
theorem b3204 (b : ℝ) (hb : rootInterval.Contains b) : i3204.Contains (n3204 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3202 b hb) (b3203 b hb))
    (by norm_num [i3204, i3202, i3203, RationalInterval.add]) (by norm_num [i3204, i3202, i3203, RationalInterval.add])

def n3205 (b : ℝ) : ℝ := (n3080 b) * (n3115 b)
def i3205 : RationalInterval := ⟨(23701204507831414210444832009609 / 1000000000000000000000000000000 : ℚ), (1482016323563909728897106825651 / 62500000000000000000000000000 : ℚ)⟩
theorem b3205 (b : ℝ) (hb : rootInterval.Contains b) : i3205.Contains (n3205 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b3080 b hb) (b3115 b hb))
    (by norm_num [i3205, i3080, i3115, RationalInterval.mul]) (by norm_num [i3205, i3080, i3115, RationalInterval.mul])

def n3206 (b : ℝ) : ℝ := (n3204 b) + (n3205 b)
def i3206 : RationalInterval := ⟨(2842871428123564028750400928231 / 500000000000000000000000000000 : ℚ), (2859070020058046729206008126391 / 500000000000000000000000000000 : ℚ)⟩
theorem b3206 (b : ℝ) (hb : rootInterval.Contains b) : i3206.Contains (n3206 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3204 b hb) (b3205 b hb))
    (by norm_num [i3206, i3204, i3205, RationalInterval.add]) (by norm_num [i3206, i3204, i3205, RationalInterval.add])

def n3207 (b : ℝ) : ℝ := (n3087 b) * (n3118 b)
def i3207 : RationalInterval := ⟨(-92133655959172414803173902273 / 15625000000000000000000000000 : ℚ), (-294575507989662448590793242431 / 50000000000000000000000000000 : ℚ)⟩
theorem b3207 (b : ℝ) (hb : rootInterval.Contains b) : i3207.Contains (n3207 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b3087 b hb) (b3118 b hb))
    (by norm_num [i3207, i3087, i3118, RationalInterval.mul]) (by norm_num [i3207, i3087, i3118, RationalInterval.mul])

def n3208 (b : ℝ) : ℝ := (n3206 b) + (n3207 b)
def i3208 : RationalInterval := ⟨(-21081112513990648990232788901 / 100000000000000000000000000000 : ℚ), (-86685059838577756701924297919 / 500000000000000000000000000000 : ℚ)⟩
theorem b3208 (b : ℝ) (hb : rootInterval.Contains b) : i3208.Contains (n3208 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3206 b hb) (b3207 b hb))
    (by norm_num [i3208, i3206, i3207, RationalInterval.add]) (by norm_num [i3208, i3206, i3207, RationalInterval.add])

def n3209 (b : ℝ) : ℝ := (n3066 b) * (n3121 b)
def i3209 : RationalInterval := ⟨(-317587936128867892692143479809 / 200000000000000000000000000000 : ℚ), (-1585189685647742090532917822301 / 1000000000000000000000000000000 : ℚ)⟩
theorem b3209 (b : ℝ) (hb : rootInterval.Contains b) : i3209.Contains (n3209 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b3066 b hb) (b3121 b hb))
    (by norm_num [i3209, i3066, i3121, RationalInterval.mul]) (by norm_num [i3209, i3066, i3121, RationalInterval.mul])

def n3210 (b : ℝ) : ℝ := (n3073 b) * (n3123 b)
def i3210 : RationalInterval := ⟨(43492068293332014265998146477 / 500000000000000000000000000000 : ℚ), (87080364392779728982995471083 / 1000000000000000000000000000000 : ℚ)⟩
theorem b3210 (b : ℝ) (hb : rootInterval.Contains b) : i3210.Contains (n3210 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b3073 b hb) (b3123 b hb))
    (by norm_num [i3210, i3073, i3123, RationalInterval.mul]) (by norm_num [i3210, i3073, i3123, RationalInterval.mul])

def n3211 (b : ℝ) : ℝ := (n3209 b) + (n3210 b)
def i3211 : RationalInterval := ⟨(-1500955544057675434928721106091 / 1000000000000000000000000000000 : ℚ), (-749054660627481180774961175609 / 500000000000000000000000000000 : ℚ)⟩
theorem b3211 (b : ℝ) (hb : rootInterval.Contains b) : i3211.Contains (n3211 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3209 b hb) (b3210 b hb))
    (by norm_num [i3211, i3209, i3210, RationalInterval.add]) (by norm_num [i3211, i3209, i3210, RationalInterval.add])

def n3212 (b : ℝ) : ℝ := (n3080 b) * (n3126 b)
def i3212 : RationalInterval := ⟨(361462447292337178487006162803 / 100000000000000000000000000000 : ℚ), (723262140795381599133071574309 / 200000000000000000000000000000 : ℚ)⟩
theorem b3212 (b : ℝ) (hb : rootInterval.Contains b) : i3212.Contains (n3212 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b3080 b hb) (b3126 b hb))
    (by norm_num [i3212, i3080, i3126, RationalInterval.mul]) (by norm_num [i3212, i3080, i3126, RationalInterval.mul])

def n3213 (b : ℝ) : ℝ := (n3211 b) + (n3212 b)
def i3213 : RationalInterval := ⟨(2113668928865696349941340521939 / 1000000000000000000000000000000 : ℚ), (2118201382721945634115435520327 / 1000000000000000000000000000000 : ℚ)⟩
theorem b3213 (b : ℝ) (hb : rootInterval.Contains b) : i3213.Contains (n3213 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3211 b hb) (b3212 b hb))
    (by norm_num [i3213, i3211, i3212, RationalInterval.add]) (by norm_num [i3213, i3211, i3212, RationalInterval.add])

def n3214 (b : ℝ) : ℝ := (n3087 b) * (n3129 b)
def i3214 : RationalInterval := ⟨(-1642166378470872116783965054327 / 1000000000000000000000000000000 : ℚ), (-20509521182565845853627622903 / 12500000000000000000000000000 : ℚ)⟩
theorem b3214 (b : ℝ) (hb : rootInterval.Contains b) : i3214.Contains (n3214 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b3087 b hb) (b3129 b hb))
    (by norm_num [i3214, i3087, i3129, RationalInterval.mul]) (by norm_num [i3214, i3087, i3129, RationalInterval.mul])

def n3215 (b : ℝ) : ℝ := (n3213 b) + (n3214 b)
def i3215 : RationalInterval := ⟨(117875637598706058289343866903 / 250000000000000000000000000000 : ℚ), (477439688116677965825225688087 / 1000000000000000000000000000000 : ℚ)⟩
theorem b3215 (b : ℝ) (hb : rootInterval.Contains b) : i3215.Contains (n3215 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b3213 b hb) (b3214 b hb))
    (by norm_num [i3215, i3213, i3214, RationalInterval.add]) (by norm_num [i3215, i3213, i3214, RationalInterval.add])

