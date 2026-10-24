import BFGS.Counterexample.Certificates.IntervalTrace9

/-! Generated arithmetic proofs. Each bound is checked by the Lean kernel. -/
namespace BFGS.Counterexample.Trace
noncomputable section
open BFGS RationalInterval
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false

def n900 (b : ℝ) : ℝ := (n897 b) + (n675 b)
def i900 : RationalInterval := ⟨(2709491272922078168723893472531 / 1000000000000000000000000000000 : ℚ), (169343205391954967925280053603 / 62500000000000000000000000000 : ℚ)⟩
theorem b900 (b : ℝ) (hb : rootInterval.Contains b) : i900.Contains (n900 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b897 b hb) (b675 b hb))
    (by norm_num [i900, i897, i675, RationalInterval.add]) (by norm_num [i900, i897, i675, RationalInterval.add])

def n901 (b : ℝ) : ℝ := (n898 b) + (n675 b)
def i901 : RationalInterval := ⟨(2709491272922078168723893472531 / 1000000000000000000000000000000 : ℚ), (169343205391954967925280053603 / 62500000000000000000000000000 : ℚ)⟩
theorem b901 (b : ℝ) (hb : rootInterval.Contains b) : i901.Contains (n901 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b898 b hb) (b675 b hb))
    (by norm_num [i901, i898, i675, RationalInterval.add]) (by norm_num [i901, i898, i675, RationalInterval.add])

def n902 (b : ℝ) : ℝ := (n899 b) + (n675 b)
def i902 : RationalInterval := ⟨(1250549064544054267270525428567 / 1000000000000000000000000000000 : ℚ), (62527453554013995769646826049 / 50000000000000000000000000000 : ℚ)⟩
theorem b902 (b : ℝ) (hb : rootInterval.Contains b) : i902.Contains (n902 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b899 b hb) (b675 b hb))
    (by norm_num [i902, i899, i675, RationalInterval.add]) (by norm_num [i902, i899, i675, RationalInterval.add])

def n903 (b : ℝ) : ℝ := (n63 b) * (n196 b)
def i903 : RationalInterval := ⟨(3624341266239489854163794033917 / 1000000000000000000000000000000 : ℚ), (14497365076415782169990058683 / 4000000000000000000000000000 : ℚ)⟩
theorem b903 (b : ℝ) (hb : rootInterval.Contains b) : i903.Contains (n903 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b63 b hb) (b196 b hb))
    (by norm_num [i903, i63, i196, RationalInterval.mul]) (by norm_num [i903, i63, i196, RationalInterval.mul])

def n904 (b : ℝ) : ℝ := (n65 b) * (n198 b)
def i904 : RationalInterval := ⟨(-110324910536872321008832141559 / 200000000000000000000000000000 : ℚ), (-551624551592399094313807892583 / 1000000000000000000000000000000 : ℚ)⟩
theorem b904 (b : ℝ) (hb : rootInterval.Contains b) : i904.Contains (n904 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b65 b hb) (b198 b hb))
    (by norm_num [i904, i65, i198, RationalInterval.mul]) (by norm_num [i904, i65, i198, RationalInterval.mul])

def n905 (b : ℝ) : ℝ := (n903 b) + (n904 b)
def i905 : RationalInterval := ⟨(1536358356777564124559816663061 / 500000000000000000000000000000 : ℚ), (3072716717511546448183706778167 / 1000000000000000000000000000000 : ℚ)⟩
theorem b905 (b : ℝ) (hb : rootInterval.Contains b) : i905.Contains (n905 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b903 b hb) (b904 b hb))
    (by norm_num [i905, i903, i904, RationalInterval.add]) (by norm_num [i905, i903, i904, RationalInterval.add])

def n906 (b : ℝ) : ℝ := (n65 b) * (n196 b)
def i906 : RationalInterval := ⟨(53133081980825783884397195029 / 25000000000000000000000000000 : ℚ), (265665410114869453258305142131 / 125000000000000000000000000000 : ℚ)⟩
theorem b906 (b : ℝ) (hb : rootInterval.Contains b) : i906.Contains (n906 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b65 b hb) (b196 b hb))
    (by norm_num [i906, i65, i196, RationalInterval.mul]) (by norm_num [i906, i65, i196, RationalInterval.mul])

def n907 (b : ℝ) : ℝ := (n0 b) * (n198 b)
def i907 : RationalInterval := ⟨(-357090588223006683557907011033 / 1000000000000000000000000000000 : ℚ), (-178545293757379868994729030251 / 500000000000000000000000000000 : ℚ)⟩
theorem b907 (b : ℝ) (hb : rootInterval.Contains b) : i907.Contains (n907 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b0 b hb) (b198 b hb))
    (by norm_num [i907, i0, i198, RationalInterval.mul]) (by norm_num [i907, i0, i198, RationalInterval.mul])

def n908 (b : ℝ) : ℝ := (n906 b) + (n907 b)
def i908 : RationalInterval := ⟨(1768232691010024671817980790127 / 1000000000000000000000000000000 : ℚ), (884116346702097944038491538273 / 500000000000000000000000000000 : ℚ)⟩
theorem b908 (b : ℝ) (hb : rootInterval.Contains b) : i908.Contains (n908 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b906 b hb) (b907 b hb))
    (by norm_num [i908, i906, i907, RationalInterval.add]) (by norm_num [i908, i906, i907, RationalInterval.add])

def n909 (b : ℝ) : ℝ := -(n905 b)
def i909 : RationalInterval := ⟨(-3072716717511546448183706778167 / 1000000000000000000000000000000 : ℚ), (-1536358356777564124559816663061 / 500000000000000000000000000000 : ℚ)⟩
theorem b909 (b : ℝ) (hb : rootInterval.Contains b) : i909.Contains (n909 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b905 b hb))
    (by norm_num [i909, i905, RationalInterval.neg]) (by norm_num [i909, i905, RationalInterval.neg])

def n910 (b : ℝ) : ℝ := -(n908 b)
def i910 : RationalInterval := ⟨(-884116346702097944038491538273 / 500000000000000000000000000000 : ℚ), (-1768232691010024671817980790127 / 1000000000000000000000000000000 : ℚ)⟩
theorem b910 (b : ℝ) (hb : rootInterval.Contains b) : i910.Contains (n910 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b908 b hb))
    (by norm_num [i910, i908, RationalInterval.neg]) (by norm_num [i910, i908, RationalInterval.neg])

def n911 (b : ℝ) : ℝ := (n909 b) + (n15 b)
def i911 : RationalInterval := ⟨(-2072716717511546448183706778167 / 1000000000000000000000000000000 : ℚ), (-1036358356777564124559816663061 / 500000000000000000000000000000 : ℚ)⟩
theorem b911 (b : ℝ) (hb : rootInterval.Contains b) : i911.Contains (n911 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b909 b hb) (b15 b hb))
    (by norm_num [i911, i909, i15, RationalInterval.add]) (by norm_num [i911, i909, i15, RationalInterval.add])

def n912 (b : ℝ) : ℝ := (n210 b) * (n911 b)
def i912 : RationalInterval := ⟨(630138211510678469664352846951 / 1000000000000000000000000000000 : ℚ), (630138221309443546794325961571 / 1000000000000000000000000000000 : ℚ)⟩
theorem b912 (b : ℝ) (hb : rootInterval.Contains b) : i912.Contains (n912 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b210 b hb) (b911 b hb))
    (by norm_num [i912, i210, i911, RationalInterval.mul]) (by norm_num [i912, i210, i911, RationalInterval.mul])

def n913 (b : ℝ) : ℝ := (n211 b) * (n910 b)
def i913 : RationalInterval := ⟨(1899544873874794109018960619851 / 1000000000000000000000000000000 : ℚ), (379908979163726164534224636467 / 200000000000000000000000000000 : ℚ)⟩
theorem b913 (b : ℝ) (hb : rootInterval.Contains b) : i913.Contains (n913 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b211 b hb) (b910 b hb))
    (by norm_num [i913, i211, i910, RationalInterval.mul]) (by norm_num [i913, i211, i910, RationalInterval.mul])

def n914 (b : ℝ) : ℝ := (n912 b) + (n913 b)
def i914 : RationalInterval := ⟨(1264841542692736289341656733401 / 500000000000000000000000000000 : ℚ), (1264841558564037184732724571953 / 500000000000000000000000000000 : ℚ)⟩
theorem b914 (b : ℝ) (hb : rootInterval.Contains b) : i914.Contains (n914 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b912 b hb) (b913 b hb))
    (by norm_num [i914, i912, i913, RationalInterval.add]) (by norm_num [i914, i912, i913, RationalInterval.add])

def n915 (b : ℝ) : ℝ := (n212 b) * (n911 b)
def i915 : RationalInterval := ⟨(2226640434964072553468400983499 / 1000000000000000000000000000000 : ℚ), (111332023096097285875958093329 / 50000000000000000000000000000 : ℚ)⟩
theorem b915 (b : ℝ) (hb : rootInterval.Contains b) : i915.Contains (n915 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b212 b hb) (b911 b hb))
    (by norm_num [i915, i212, i911, RationalInterval.mul]) (by norm_num [i915, i212, i911, RationalInterval.mul])

def n916 (b : ℝ) : ℝ := (n213 b) * (n910 b)
def i916 : RationalInterval := ⟨(839022960942646715620961391067 / 125000000000000000000000000000 : ℚ), (6712183741969888294502032879341 / 1000000000000000000000000000000 : ℚ)⟩
theorem b916 (b : ℝ) (hb : rootInterval.Contains b) : i916.Contains (n916 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b213 b hb) (b910 b hb))
    (by norm_num [i916, i213, i910, RationalInterval.mul]) (by norm_num [i916, i213, i910, RationalInterval.mul])

def n917 (b : ℝ) : ℝ := (n915 b) + (n916 b)
def i917 : RationalInterval := ⟨(1787764824501049255687218422407 / 200000000000000000000000000000 : ℚ), (8938824203891834012021194745921 / 1000000000000000000000000000000 : ℚ)⟩
theorem b917 (b : ℝ) (hb : rootInterval.Contains b) : i917.Contains (n917 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b915 b hb) (b916 b hb))
    (by norm_num [i917, i915, i916, RationalInterval.add]) (by norm_num [i917, i915, i916, RationalInterval.add])

def n918 (b : ℝ) : ℝ := -(n196 b)
def i918 : RationalInterval := ⟨(-749508994092494958215536766851 / 500000000000000000000000000000 : ℚ), (-1499017987006458498787906232757 / 1000000000000000000000000000000 : ℚ)⟩
theorem b918 (b : ℝ) (hb : rootInterval.Contains b) : i918.Contains (n918 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b196 b hb))
    (by norm_num [i918, i196, RationalInterval.neg]) (by norm_num [i918, i196, RationalInterval.neg])

def n919 (b : ℝ) : ℝ := -(n198 b)
def i919 : RationalInterval := ⟨(389067928155278712648699664163 / 1000000000000000000000000000000 : ℚ), (97266982230677460743126848381 / 250000000000000000000000000000 : ℚ)⟩
theorem b919 (b : ℝ) (hb : rootInterval.Contains b) : i919.Contains (n919 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b198 b hb))
    (by norm_num [i919, i198, RationalInterval.neg]) (by norm_num [i919, i198, RationalInterval.neg])

def n920 (b : ℝ) : ℝ := (n914 b) + (n918 b)
def i920 : RationalInterval := ⟨(10306650972004826622522399331 / 10000000000000000000000000000 : ℚ), (1030665130121615870677542911149 / 1000000000000000000000000000000 : ℚ)⟩
theorem b920 (b : ℝ) (hb : rootInterval.Contains b) : i920.Contains (n920 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b914 b hb) (b918 b hb))
    (by norm_num [i920, i914, i918, RationalInterval.add]) (by norm_num [i920, i914, i918, RationalInterval.add])

def n921 (b : ℝ) : ℝ := (n917 b) + (n919 b)
def i921 : RationalInterval := ⟨(4663946025330262495542395888099 / 500000000000000000000000000000 : ℚ), (1865578426562908770998740427889 / 200000000000000000000000000000 : ℚ)⟩
theorem b921 (b : ℝ) (hb : rootInterval.Contains b) : i921.Contains (n921 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b917 b hb) (b919 b hb))
    (by norm_num [i921, i917, i919, RationalInterval.add]) (by norm_num [i921, i917, i919, RationalInterval.add])

def n922 (b : ℝ) : ℝ := (n909 b) * (n21 b)
def i922 : RationalInterval := ⟨(3207546973609973848810475142669 / 1000000000000000000000000000000 : ℚ), (3207546978893383826299590315503 / 1000000000000000000000000000000 : ℚ)⟩
theorem b922 (b : ℝ) (hb : rootInterval.Contains b) : i922.Contains (n922 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b909 b hb) (b21 b hb))
    (by norm_num [i922, i909, i21, RationalInterval.mul]) (by norm_num [i922, i909, i21, RationalInterval.mul])

def n923 (b : ℝ) : ℝ := (n910 b) * (n320 b)
def i923 : RationalInterval := ⟨(1624458974911873019778576384839 / 1000000000000000000000000000000 : ℚ), (1624458978104501838953703069607 / 1000000000000000000000000000000 : ℚ)⟩
theorem b923 (b : ℝ) (hb : rootInterval.Contains b) : i923.Contains (n923 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b910 b hb) (b320 b hb))
    (by norm_num [i923, i910, i320, RationalInterval.mul]) (by norm_num [i923, i910, i320, RationalInterval.mul])

def n924 (b : ℝ) : ℝ := (n922 b) + (n923 b)
def i924 : RationalInterval := ⟨(1208001487130461717147262881877 / 250000000000000000000000000000 : ℚ), (483200595699788566525329338511 / 100000000000000000000000000000 : ℚ)⟩
theorem b924 (b : ℝ) (hb : rootInterval.Contains b) : i924.Contains (n924 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b922 b hb) (b923 b hb))
    (by norm_num [i924, i922, i923, RationalInterval.add]) (by norm_num [i924, i922, i923, RationalInterval.add])

def n925 (b : ℝ) : ℝ := (n302 b) * (n920 b)
def i925 : RationalInterval := ⟨(-365321932949431602434045716429 / 250000000000000000000000000000 : ℚ), (-292257537022298998192975628803 / 200000000000000000000000000000 : ℚ)⟩
theorem b925 (b : ℝ) (hb : rootInterval.Contains b) : i925.Contains (n925 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b302 b hb) (b920 b hb))
    (by norm_num [i925, i302, i920, RationalInterval.mul]) (by norm_num [i925, i302, i920, RationalInterval.mul])

def n926 (b : ℝ) : ℝ := (n303 b) * (n921 b)
def i926 : RationalInterval := ⟨(-1070154541460933789045983821111 / 125000000000000000000000000000 : ℚ), (-107015453202404739534444253107 / 12500000000000000000000000000 : ℚ)⟩
theorem b926 (b : ℝ) (hb : rootInterval.Contains b) : i926.Contains (n926 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b303 b hb) (b921 b hb))
    (by norm_num [i926, i303, i921, RationalInterval.mul]) (by norm_num [i926, i303, i921, RationalInterval.mul])

def n927 (b : ℝ) : ℝ := (n925 b) + (n926 b)
def i927 : RationalInterval := ⟨(-2505631015871299180526013358651 / 250000000000000000000000000000 : ℚ), (-400900957652154966148816735703 / 40000000000000000000000000000 : ℚ)⟩
theorem b927 (b : ℝ) (hb : rootInterval.Contains b) : i927.Contains (n927 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b925 b hb) (b926 b hb))
    (by norm_num [i927, i925, i926, RationalInterval.add]) (by norm_num [i927, i925, i926, RationalInterval.add])

def n928 (b : ℝ) : ℝ := (n924 b) + (n927 b)
def i928 : RationalInterval := ⟨(-648814764370418731689375238387 / 125000000000000000000000000000 : ℚ), (-1038103596861197697693425001493 / 200000000000000000000000000000 : ℚ)⟩
theorem b928 (b : ℝ) (hb : rootInterval.Contains b) : i928.Contains (n928 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b924 b hb) (b927 b hb))
    (by norm_num [i928, i924, i927, RationalInterval.add]) (by norm_num [i928, i924, i927, RationalInterval.add])

def n929 (b : ℝ) : ℝ := (n63 b) * (n21 b)
def i929 : RationalInterval := ⟨(-315487935036304095607836379867 / 125000000000000000000000000000 : ℚ), (-630975869843109215430596187771 / 250000000000000000000000000000 : ℚ)⟩
theorem b929 (b : ℝ) (hb : rootInterval.Contains b) : i929.Contains (n929 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b63 b hb) (b21 b hb))
    (by norm_num [i929, i63, i21, RationalInterval.mul]) (by norm_num [i929, i63, i21, RationalInterval.mul])

def n930 (b : ℝ) : ℝ := (n65 b) * (n320 b)
def i930 : RationalInterval := ⟨(-1302529259048840330602118446911 / 1000000000000000000000000000000 : ℚ), (-130252925824334179347609708853 / 100000000000000000000000000000 : ℚ)⟩
theorem b930 (b : ℝ) (hb : rootInterval.Contains b) : i930.Contains (n930 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b65 b hb) (b320 b hb))
    (by norm_num [i930, i65, i320, RationalInterval.mul]) (by norm_num [i930, i65, i320, RationalInterval.mul])

def n931 (b : ℝ) : ℝ := (n929 b) + (n930 b)
def i931 : RationalInterval := ⟨(-3826432739339273095464809485847 / 1000000000000000000000000000000 : ℚ), (-1913216368807889327599240919807 / 500000000000000000000000000000 : ℚ)⟩
theorem b931 (b : ℝ) (hb : rootInterval.Contains b) : i931.Contains (n931 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b929 b hb) (b930 b hb))
    (by norm_num [i931, i929, i930, RationalInterval.add]) (by norm_num [i931, i929, i930, RationalInterval.add])

def n932 (b : ℝ) : ℝ := (n65 b) * (n21 b)
def i932 : RationalInterval := ⟨(-11562684833544194587273828921 / 7812500000000000000000000000 : ℚ), (-59200946326040969142697862491 / 40000000000000000000000000000 : ℚ)⟩
theorem b932 (b : ℝ) (hb : rootInterval.Contains b) : i932.Contains (n932 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b65 b hb) (b21 b hb))
    (by norm_num [i932, i65, i21, RationalInterval.mul]) (by norm_num [i932, i65, i21, RationalInterval.mul])

def n933 (b : ℝ) : ℝ := (n0 b) * (n320 b)
def i933 : RationalInterval := ⟨(-42159194784570136434725637387 / 50000000000000000000000000000 : ℚ), (-843183895166728635568287592723 / 1000000000000000000000000000000 : ℚ)⟩
theorem b933 (b : ℝ) (hb : rootInterval.Contains b) : i933.Contains (n933 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b0 b hb) (b320 b hb))
    (by norm_num [i933, i0, i320, RationalInterval.mul]) (by norm_num [i933, i0, i320, RationalInterval.mul])

def n934 (b : ℝ) : ℝ := (n932 b) + (n933 b)
def i934 : RationalInterval := ⟨(-580801888596264908966390712407 / 250000000000000000000000000000 : ℚ), (-1161603776658876432067867077499 / 500000000000000000000000000000 : ℚ)⟩
theorem b934 (b : ℝ) (hb : rootInterval.Contains b) : i934.Contains (n934 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b932 b hb) (b933 b hb))
    (by norm_num [i934, i932, i933, RationalInterval.add]) (by norm_num [i934, i932, i933, RationalInterval.add])

def n935 (b : ℝ) : ℝ := (n21 b) * (n931 b)
def i935 : RationalInterval := ⟨(1997167961029059768694990097283 / 500000000000000000000000000000 : ℚ), (249645995330846421067655692411 / 62500000000000000000000000000 : ℚ)⟩
theorem b935 (b : ℝ) (hb : rootInterval.Contains b) : i935.Contains (n935 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b21 b hb) (b931 b hb))
    (by norm_num [i935, i21, i931, RationalInterval.mul]) (by norm_num [i935, i21, i931, RationalInterval.mul])

def n936 (b : ℝ) : ℝ := (n320 b) * (n934 b)
def i936 : RationalInterval := ⟨(2134309234162146621711334470799 / 1000000000000000000000000000000 : ℚ), (2134309236447498394372687899129 / 1000000000000000000000000000000 : ℚ)⟩
theorem b936 (b : ℝ) (hb : rootInterval.Contains b) : i936.Contains (n936 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b320 b hb) (b934 b hb))
    (by norm_num [i936, i320, i934, RationalInterval.mul]) (by norm_num [i936, i320, i934, RationalInterval.mul])

def n937 (b : ℝ) : ℝ := (n935 b) + (n936 b)
def i937 : RationalInterval := ⟨(1225729031244053231820262933073 / 200000000000000000000000000000 : ℚ), (1225729032348208226291035795541 / 200000000000000000000000000000 : ℚ)⟩
theorem b937 (b : ℝ) (hb : rootInterval.Contains b) : i937.Contains (n937 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b935 b hb) (b936 b hb))
    (by norm_num [i937, i935, i936, RationalInterval.add]) (by norm_num [i937, i935, i936, RationalInterval.add])

def n938 (b : ℝ) : ℝ := (n931 b) * (n302 b)
def i938 : RationalInterval := ⟨(1356289024575786123742628014739 / 250000000000000000000000000000 : ℚ), (2712578050392498574853634687961 / 500000000000000000000000000000 : ℚ)⟩
theorem b938 (b : ℝ) (hb : rootInterval.Contains b) : i938.Contains (n938 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b931 b hb) (b302 b hb))
    (by norm_num [i938, i931, i302, RationalInterval.mul]) (by norm_num [i938, i931, i302, RationalInterval.mul])

def n939 (b : ℝ) : ℝ := (n931 b) * (n303 b)
def i939 : RationalInterval := ⟨(3511939729495255167371271139149 / 1000000000000000000000000000000 : ℚ), (1755969865557680300987432316499 / 500000000000000000000000000000 : ℚ)⟩
theorem b939 (b : ℝ) (hb : rootInterval.Contains b) : i939.Contains (n939 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b931 b hb) (b303 b hb))
    (by norm_num [i939, i931, i303, RationalInterval.mul]) (by norm_num [i939, i931, i303, RationalInterval.mul])

def n940 (b : ℝ) : ℝ := (n934 b) * (n302 b)
def i940 : RationalInterval := ⟨(102933369094701542802031779763 / 31250000000000000000000000000 : ℚ), (3293867812566920077235160050579 / 1000000000000000000000000000000 : ℚ)⟩
theorem b940 (b : ℝ) (hb : rootInterval.Contains b) : i940.Contains (n940 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b934 b hb) (b302 b hb))
    (by norm_num [i940, i934, i302, RationalInterval.mul]) (by norm_num [i940, i934, i302, RationalInterval.mul])

def n941 (b : ℝ) : ℝ := (n934 b) * (n303 b)
def i941 : RationalInterval := ⟨(2132264034371572937597149874917 / 1000000000000000000000000000000 : ℚ), (426452807074878051860475725153 / 200000000000000000000000000000 : ℚ)⟩
theorem b941 (b : ℝ) (hb : rootInterval.Contains b) : i941.Contains (n941 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b934 b hb) (b303 b hb))
    (by norm_num [i941, i934, i303, RationalInterval.mul]) (by norm_num [i941, i934, i303, RationalInterval.mul])

def n942 (b : ℝ) : ℝ := (n302 b) * (n931 b)
def i942 : RationalInterval := ⟨(1356289024575786123742628014739 / 250000000000000000000000000000 : ℚ), (2712578050392498574853634687961 / 500000000000000000000000000000 : ℚ)⟩
theorem b942 (b : ℝ) (hb : rootInterval.Contains b) : i942.Contains (n942 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b302 b hb) (b931 b hb))
    (by norm_num [i942, i302, i931, RationalInterval.mul]) (by norm_num [i942, i302, i931, RationalInterval.mul])

def n943 (b : ℝ) : ℝ := (n302 b) * (n934 b)
def i943 : RationalInterval := ⟨(102933369094701542802031779763 / 31250000000000000000000000000 : ℚ), (3293867812566920077235160050579 / 1000000000000000000000000000000 : ℚ)⟩
theorem b943 (b : ℝ) (hb : rootInterval.Contains b) : i943.Contains (n943 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b302 b hb) (b934 b hb))
    (by norm_num [i943, i302, i934, RationalInterval.mul]) (by norm_num [i943, i302, i934, RationalInterval.mul])

def n944 (b : ℝ) : ℝ := (n303 b) * (n931 b)
def i944 : RationalInterval := ⟨(3511939729495255167371271139149 / 1000000000000000000000000000000 : ℚ), (1755969865557680300987432316499 / 500000000000000000000000000000 : ℚ)⟩
theorem b944 (b : ℝ) (hb : rootInterval.Contains b) : i944.Contains (n944 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b303 b hb) (b931 b hb))
    (by norm_num [i944, i303, i931, RationalInterval.mul]) (by norm_num [i944, i303, i931, RationalInterval.mul])

def n945 (b : ℝ) : ℝ := (n303 b) * (n934 b)
def i945 : RationalInterval := ⟨(2132264034371572937597149874917 / 1000000000000000000000000000000 : ℚ), (426452807074878051860475725153 / 200000000000000000000000000000 : ℚ)⟩
theorem b945 (b : ℝ) (hb : rootInterval.Contains b) : i945.Contains (n945 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b303 b hb) (b934 b hb))
    (by norm_num [i945, i303, i934, RationalInterval.mul]) (by norm_num [i945, i303, i934, RationalInterval.mul])

def n946 (b : ℝ) : ℝ := (n938 b) + (n942 b)
def i946 : RationalInterval := ⟨(1356289024575786123742628014739 / 125000000000000000000000000000 : ℚ), (2712578050392498574853634687961 / 250000000000000000000000000000 : ℚ)⟩
theorem b946 (b : ℝ) (hb : rootInterval.Contains b) : i946.Contains (n946 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b938 b hb) (b942 b hb))
    (by norm_num [i946, i938, i942, RationalInterval.add]) (by norm_num [i946, i938, i942, RationalInterval.add])

def n947 (b : ℝ) : ℝ := (n939 b) + (n943 b)
def i947 : RationalInterval := ⟨(1361161508105140907407257618313 / 200000000000000000000000000000 : ℚ), (6805807543682280679210024683577 / 1000000000000000000000000000000 : ℚ)⟩
theorem b947 (b : ℝ) (hb : rootInterval.Contains b) : i947.Contains (n947 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b939 b hb) (b943 b hb))
    (by norm_num [i947, i939, i943, RationalInterval.add]) (by norm_num [i947, i939, i943, RationalInterval.add])

def n948 (b : ℝ) : ℝ := (n940 b) + (n944 b)
def i948 : RationalInterval := ⟨(1361161508105140907407257618313 / 200000000000000000000000000000 : ℚ), (6805807543682280679210024683577 / 1000000000000000000000000000000 : ℚ)⟩
theorem b948 (b : ℝ) (hb : rootInterval.Contains b) : i948.Contains (n948 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b940 b hb) (b944 b hb))
    (by norm_num [i948, i940, i944, RationalInterval.add]) (by norm_num [i948, i940, i944, RationalInterval.add])

def n949 (b : ℝ) : ℝ := (n941 b) + (n945 b)
def i949 : RationalInterval := ⟨(2132264034371572937597149874917 / 500000000000000000000000000000 : ℚ), (426452807074878051860475725153 / 100000000000000000000000000000 : ℚ)⟩
theorem b949 (b : ℝ) (hb : rootInterval.Contains b) : i949.Contains (n949 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b941 b hb) (b945 b hb))
    (by norm_num [i949, i941, i945, RationalInterval.add]) (by norm_num [i949, i941, i945, RationalInterval.add])

def n950 (b : ℝ) : ℝ := (n302 b) * (n302 b)
def i950 : RationalInterval := ⟨(1256366441651481363681 / 625000000000000000000 : ℚ), (804074522668290555889 / 400000000000000000000 : ℚ)⟩
theorem b950 (b : ℝ) (hb : rootInterval.Contains b) : i950.Contains (n950 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b302 b hb) (b302 b hb))
    (by norm_num [i950, i302, i302, RationalInterval.mul]) (by norm_num [i950, i302, i302, RationalInterval.mul])

def n951 (b : ℝ) : ℝ := (n302 b) * (n303 b)
def i951 : RationalInterval := ⟨(813300694263981363681 / 625000000000000000000 : ℚ), (520512444338290555889 / 400000000000000000000 : ℚ)⟩
theorem b951 (b : ℝ) (hb : rootInterval.Contains b) : i951.Contains (n951 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b302 b hb) (b303 b hb))
    (by norm_num [i951, i302, i303, RationalInterval.mul]) (by norm_num [i951, i302, i303, RationalInterval.mul])

def n952 (b : ℝ) : ℝ := (n303 b) * (n302 b)
def i952 : RationalInterval := ⟨(813300694263981363681 / 625000000000000000000 : ℚ), (520512444338290555889 / 400000000000000000000 : ℚ)⟩
theorem b952 (b : ℝ) (hb : rootInterval.Contains b) : i952.Contains (n952 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b303 b hb) (b302 b hb))
    (by norm_num [i952, i303, i302, RationalInterval.mul]) (by norm_num [i952, i303, i302, RationalInterval.mul])

def n953 (b : ℝ) : ℝ := (n303 b) * (n303 b)
def i953 : RationalInterval := ⟨(526484946876481363681 / 625000000000000000000 : ℚ), (336950366008290555889 / 400000000000000000000 : ℚ)⟩
theorem b953 (b : ℝ) (hb : rootInterval.Contains b) : i953.Contains (n953 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b303 b hb) (b303 b hb))
    (by norm_num [i953, i303, i303, RationalInterval.mul]) (by norm_num [i953, i303, i303, RationalInterval.mul])

def n954 (b : ℝ) : ℝ := (n63 b) * (n920 b)
def i954 : RationalInterval := ⟨(498390556462395530643423615423 / 200000000000000000000000000000 : ℚ), (498390572383868456082745155373 / 200000000000000000000000000000 : ℚ)⟩
theorem b954 (b : ℝ) (hb : rootInterval.Contains b) : i954.Contains (n954 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b63 b hb) (b920 b hb))
    (by norm_num [i954, i63, i920, RationalInterval.mul]) (by norm_num [i954, i63, i920, RationalInterval.mul])

def n955 (b : ℝ) : ℝ := (n65 b) * (n921 b)
def i955 : RationalInterval := ⟨(13225182281522641658297936136659 / 1000000000000000000000000000000 : ℚ), (1322518239809474223986472163861 / 100000000000000000000000000000 : ℚ)⟩
theorem b955 (b : ℝ) (hb : rootInterval.Contains b) : i955.Contains (n955 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b65 b hb) (b921 b hb))
    (by norm_num [i955, i65, i921, RationalInterval.mul]) (by norm_num [i955, i65, i921, RationalInterval.mul])

def n956 (b : ℝ) : ℝ := (n954 b) + (n955 b)
def i956 : RationalInterval := ⟨(7858567531917309655757527106887 / 500000000000000000000000000000 : ℚ), (628685410400563380811137896619 / 40000000000000000000000000000 : ℚ)⟩
theorem b956 (b : ℝ) (hb : rootInterval.Contains b) : i956.Contains (n956 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b954 b hb) (b955 b hb))
    (by norm_num [i956, i954, i955, RationalInterval.add]) (by norm_num [i956, i954, i955, RationalInterval.add])

def n957 (b : ℝ) : ℝ := (n65 b) * (n920 b)
def i957 : RationalInterval := ⟨(292257537022298998192975628803 / 200000000000000000000000000000 : ℚ), (365321932949431602434045716429 / 250000000000000000000000000000 : ℚ)⟩
theorem b957 (b : ℝ) (hb : rootInterval.Contains b) : i957.Contains (n957 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b65 b hb) (b920 b hb))
    (by norm_num [i957, i65, i920, RationalInterval.mul]) (by norm_num [i957, i65, i920, RationalInterval.mul])

def n958 (b : ℝ) : ℝ := (n0 b) * (n921 b)
def i958 : RationalInterval := ⟨(107015453202404739534444253107 / 12500000000000000000000000000 : ℚ), (1070154541460933789045983821111 / 125000000000000000000000000000 : ℚ)⟩
theorem b958 (b : ℝ) (hb : rootInterval.Contains b) : i958.Contains (n958 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b0 b hb) (b921 b hb))
    (by norm_num [i958, i0, i921, RationalInterval.mul]) (by norm_num [i958, i0, i921, RationalInterval.mul])

def n959 (b : ℝ) : ℝ := (n957 b) + (n958 b)
def i959 : RationalInterval := ⟨(400900957652154966148816735703 / 40000000000000000000000000000 : ℚ), (2505631015871299180526013358651 / 250000000000000000000000000000 : ℚ)⟩
theorem b959 (b : ℝ) (hb : rootInterval.Contains b) : i959.Contains (n959 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b957 b hb) (b958 b hb))
    (by norm_num [i959, i957, i958, RationalInterval.add]) (by norm_num [i959, i957, i958, RationalInterval.add])

def n960 (b : ℝ) : ℝ := (n920 b) * (n931 b)
def i960 : RationalInterval := ⟨(-3943770797192722968226541579357 / 1000000000000000000000000000000 : ℚ), (-3943770669445875478557010815223 / 1000000000000000000000000000000 : ℚ)⟩
theorem b960 (b : ℝ) (hb : rootInterval.Contains b) : i960.Contains (n960 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b920 b hb) (b931 b hb))
    (by norm_num [i960, i920, i931, RationalInterval.mul]) (by norm_num [i960, i920, i931, RationalInterval.mul])

def n961 (b : ℝ) : ℝ := (n921 b) * (n934 b)
def i961 : RationalInterval := ⟨(-10835314734721857156520233053891 / 500000000000000000000000000000 : ℚ), (-4334125853725430942735954874193 / 200000000000000000000000000000 : ℚ)⟩
theorem b961 (b : ℝ) (hb : rootInterval.Contains b) : i961.Contains (n961 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b921 b hb) (b934 b hb))
    (by norm_num [i961, i921, i934, RationalInterval.mul]) (by norm_num [i961, i921, i934, RationalInterval.mul])

def n962 (b : ℝ) : ℝ := (n960 b) + (n961 b)
def i962 : RationalInterval := ⟨(-25614400266636437281267007687139 / 1000000000000000000000000000000 : ℚ), (-6403599984518257548059196296547 / 250000000000000000000000000000 : ℚ)⟩
theorem b962 (b : ℝ) (hb : rootInterval.Contains b) : i962.Contains (n962 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b960 b hb) (b961 b hb))
    (by norm_num [i962, i960, i961, RationalInterval.add]) (by norm_num [i962, i960, i961, RationalInterval.add])

def n963 (b : ℝ) : ℝ := (n962 b) * (n13 b)
def i963 : RationalInterval := ⟨(-25614400266636437281267007687139 / 500000000000000000000000000000 : ℚ), (-6403599984518257548059196296547 / 125000000000000000000000000000 : ℚ)⟩
theorem b963 (b : ℝ) (hb : rootInterval.Contains b) : i963.Contains (n963 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b962 b hb) (b13 b hb))
    (by norm_num [i963, i962, i13, RationalInterval.mul]) (by norm_num [i963, i962, i13, RationalInterval.mul])

def n964 (b : ℝ) : ℝ := (n909 b) * (n302 b)
def i964 : RationalInterval := ⟨(2178264843522185039807367405661 / 500000000000000000000000000000 : ℚ), (2178264846342274041548253869151 / 500000000000000000000000000000 : ℚ)⟩
theorem b964 (b : ℝ) (hb : rootInterval.Contains b) : i964.Contains (n964 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b909 b hb) (b302 b hb))
    (by norm_num [i964, i909, i302, RationalInterval.mul]) (by norm_num [i964, i909, i302, RationalInterval.mul])

def n965 (b : ℝ) : ℝ := (n909 b) * (n303 b)
def i965 : RationalInterval := ⟨(2820171330266805955054918148261 / 1000000000000000000000000000000 : ℚ), (2820171333928774859004654349219 / 1000000000000000000000000000000 : ℚ)⟩
theorem b965 (b : ℝ) (hb : rootInterval.Contains b) : i965.Contains (n965 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b909 b hb) (b303 b hb))
    (by norm_num [i965, i909, i303, RationalInterval.mul]) (by norm_num [i965, i909, i303, RationalInterval.mul])

def n966 (b : ℝ) : ℝ := (n910 b) * (n302 b)
def i966 : RationalInterval := ⟨(2507018684151574187116313814843 / 1000000000000000000000000000000 : ℚ), (2507018687563737343827746941109 / 1000000000000000000000000000000 : ℚ)⟩
theorem b966 (b : ℝ) (hb : rootInterval.Contains b) : i966.Contains (n966 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b910 b hb) (b302 b hb))
    (by norm_num [i966, i910, i302, RationalInterval.mul]) (by norm_num [i966, i910, i302, RationalInterval.mul])

def n967 (b : ℝ) : ℝ := (n910 b) * (n303 b)
def i967 : RationalInterval := ⟨(81145116932328092560366170989 / 50000000000000000000000000000 : ℚ), (405725585215409849947313850709 / 250000000000000000000000000000 : ℚ)⟩
theorem b967 (b : ℝ) (hb : rootInterval.Contains b) : i967.Contains (n967 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b910 b hb) (b303 b hb))
    (by norm_num [i967, i910, i303, RationalInterval.mul]) (by norm_num [i967, i910, i303, RationalInterval.mul])

def n968 (b : ℝ) : ℝ := (n302 b) * (n909 b)
def i968 : RationalInterval := ⟨(2178264843522185039807367405661 / 500000000000000000000000000000 : ℚ), (2178264846342274041548253869151 / 500000000000000000000000000000 : ℚ)⟩
theorem b968 (b : ℝ) (hb : rootInterval.Contains b) : i968.Contains (n968 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b302 b hb) (b909 b hb))
    (by norm_num [i968, i302, i909, RationalInterval.mul]) (by norm_num [i968, i302, i909, RationalInterval.mul])

def n969 (b : ℝ) : ℝ := (n302 b) * (n910 b)
def i969 : RationalInterval := ⟨(2507018684151574187116313814843 / 1000000000000000000000000000000 : ℚ), (2507018687563737343827746941109 / 1000000000000000000000000000000 : ℚ)⟩
theorem b969 (b : ℝ) (hb : rootInterval.Contains b) : i969.Contains (n969 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b302 b hb) (b910 b hb))
    (by norm_num [i969, i302, i910, RationalInterval.mul]) (by norm_num [i969, i302, i910, RationalInterval.mul])

def n970 (b : ℝ) : ℝ := (n303 b) * (n909 b)
def i970 : RationalInterval := ⟨(2820171330266805955054918148261 / 1000000000000000000000000000000 : ℚ), (2820171333928774859004654349219 / 1000000000000000000000000000000 : ℚ)⟩
theorem b970 (b : ℝ) (hb : rootInterval.Contains b) : i970.Contains (n970 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b303 b hb) (b909 b hb))
    (by norm_num [i970, i303, i909, RationalInterval.mul]) (by norm_num [i970, i303, i909, RationalInterval.mul])

def n971 (b : ℝ) : ℝ := (n303 b) * (n910 b)
def i971 : RationalInterval := ⟨(81145116932328092560366170989 / 50000000000000000000000000000 : ℚ), (405725585215409849947313850709 / 250000000000000000000000000000 : ℚ)⟩
theorem b971 (b : ℝ) (hb : rootInterval.Contains b) : i971.Contains (n971 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b303 b hb) (b910 b hb))
    (by norm_num [i971, i303, i910, RationalInterval.mul]) (by norm_num [i971, i303, i910, RationalInterval.mul])

def n972 (b : ℝ) : ℝ := (n964 b) + (n968 b)
def i972 : RationalInterval := ⟨(2178264843522185039807367405661 / 250000000000000000000000000000 : ℚ), (2178264846342274041548253869151 / 250000000000000000000000000000 : ℚ)⟩
theorem b972 (b : ℝ) (hb : rootInterval.Contains b) : i972.Contains (n972 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b964 b hb) (b968 b hb))
    (by norm_num [i972, i964, i968, RationalInterval.add]) (by norm_num [i972, i964, i968, RationalInterval.add])

def n973 (b : ℝ) : ℝ := (n965 b) + (n969 b)
def i973 : RationalInterval := ⟨(166474687950574379442850998847 / 31250000000000000000000000000 : ℚ), (665898752686564025354050161291 / 125000000000000000000000000000 : ℚ)⟩
theorem b973 (b : ℝ) (hb : rootInterval.Contains b) : i973.Contains (n973 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b965 b hb) (b969 b hb))
    (by norm_num [i973, i965, i969, RationalInterval.add]) (by norm_num [i973, i965, i969, RationalInterval.add])

def n974 (b : ℝ) : ℝ := (n966 b) + (n970 b)
def i974 : RationalInterval := ⟨(166474687950574379442850998847 / 31250000000000000000000000000 : ℚ), (665898752686564025354050161291 / 125000000000000000000000000000 : ℚ)⟩
theorem b974 (b : ℝ) (hb : rootInterval.Contains b) : i974.Contains (n974 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b966 b hb) (b970 b hb))
    (by norm_num [i974, i966, i970, RationalInterval.add]) (by norm_num [i974, i966, i970, RationalInterval.add])

def n975 (b : ℝ) : ℝ := (n967 b) + (n971 b)
def i975 : RationalInterval := ⟨(81145116932328092560366170989 / 25000000000000000000000000000 : ℚ), (405725585215409849947313850709 / 125000000000000000000000000000 : ℚ)⟩
theorem b975 (b : ℝ) (hb : rootInterval.Contains b) : i975.Contains (n975 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b967 b hb) (b971 b hb))
    (by norm_num [i975, i967, i971, RationalInterval.add]) (by norm_num [i975, i967, i971, RationalInterval.add])

def n976 (b : ℝ) : ℝ := (n956 b) * (n302 b)
def i976 : RationalInterval := ⟨(-22283917698616593758212187897189 / 1000000000000000000000000000000 : ℚ), (-11141958710157069003124733088293 / 500000000000000000000000000000 : ℚ)⟩
theorem b976 (b : ℝ) (hb : rootInterval.Contains b) : i976.Contains (n976 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b956 b hb) (b302 b hb))
    (by norm_num [i976, i956, i302, RationalInterval.mul]) (by norm_num [i976, i956, i302, RationalInterval.mul])

def n977 (b : ℝ) : ℝ := (n956 b) * (n303 b)
def i977 : RationalInterval := ⟨(-3606337517152387874518241047363 / 250000000000000000000000000000 : ℚ), (-14425349888396828350491939069699 / 1000000000000000000000000000000 : ℚ)⟩
theorem b977 (b : ℝ) (hb : rootInterval.Contains b) : i977.Contains (n977 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b956 b hb) (b303 b hb))
    (by norm_num [i977, i956, i303, RationalInterval.mul]) (by norm_num [i977, i956, i303, RationalInterval.mul])

def n978 (b : ℝ) : ℝ := (n959 b) * (n302 b)
def i978 : RationalInterval := ⟨(-14210038767771496228543644212169 / 1000000000000000000000000000000 : ℚ), (-14210038594441322186135619964241 / 1000000000000000000000000000000 : ℚ)⟩
theorem b978 (b : ℝ) (hb : rootInterval.Contains b) : i978.Contains (n978 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b959 b hb) (b302 b hb))
    (by norm_num [i978, i959, i302, RationalInterval.mul]) (by norm_num [i978, i959, i302, RationalInterval.mul])

def n979 (b : ℝ) : ℝ := (n959 b) * (n303 b)
def i979 : RationalInterval := ⟨(-9198776736028897867491617494867 / 1000000000000000000000000000000 : ℚ), (-9198776623789385109275410767953 / 1000000000000000000000000000000 : ℚ)⟩
theorem b979 (b : ℝ) (hb : rootInterval.Contains b) : i979.Contains (n979 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b959 b hb) (b303 b hb))
    (by norm_num [i979, i959, i303, RationalInterval.mul]) (by norm_num [i979, i959, i303, RationalInterval.mul])

def n980 (b : ℝ) : ℝ := (n931 b) * (n909 b)
def i980 : RationalInterval := ⟨(11757543826166507752343731996023 / 1000000000000000000000000000000 : ℚ), (5878771923300643026042956820843 / 500000000000000000000000000000 : ℚ)⟩
theorem b980 (b : ℝ) (hb : rootInterval.Contains b) : i980.Contains (n980 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b931 b hb) (b909 b hb))
    (by norm_num [i980, i931, i909, RationalInterval.mul]) (by norm_num [i980, i931, i909, RationalInterval.mul])

def n981 (b : ℝ) : ℝ := (n931 b) * (n910 b)
def i981 : RationalInterval := ⟨(1353204691320640789594029732377 / 200000000000000000000000000000 : ℚ), (3383011734405939142750133375229 / 500000000000000000000000000000 : ℚ)⟩
theorem b981 (b : ℝ) (hb : rootInterval.Contains b) : i981.Contains (n981 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b931 b hb) (b910 b hb))
    (by norm_num [i981, i931, i910, RationalInterval.mul]) (by norm_num [i981, i931, i910, RationalInterval.mul])

def n982 (b : ℝ) : ℝ := (n934 b) * (n909 b)
def i982 : RationalInterval := ⟨(892319834767121995831034996693 / 125000000000000000000000000000 : ℚ), (7138558690608087971005280788491 / 1000000000000000000000000000000 : ℚ)⟩
theorem b982 (b : ℝ) (hb : rootInterval.Contains b) : i982.Contains (n982 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b934 b hb) (b909 b hb))
    (by norm_num [i982, i934, i909, RationalInterval.mul]) (by norm_num [i982, i934, i909, RationalInterval.mul])

def n983 (b : ℝ) : ℝ := (n934 b) * (n910 b)
def i983 : RationalInterval := ⟨(2053985771888932759155375587583 / 500000000000000000000000000000 : ℚ), (2053985775613634449761994361001 / 500000000000000000000000000000 : ℚ)⟩
theorem b983 (b : ℝ) (hb : rootInterval.Contains b) : i983.Contains (n983 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b934 b hb) (b910 b hb))
    (by norm_num [i983, i934, i910, RationalInterval.mul]) (by norm_num [i983, i934, i910, RationalInterval.mul])

def n984 (b : ℝ) : ℝ := (n976 b) + (n980 b)
def i984 : RationalInterval := ⟨(-5263186936225043002934227950583 / 500000000000000000000000000000 : ℚ), (-105263735737128519541635525349 / 10000000000000000000000000000 : ℚ)⟩
theorem b984 (b : ℝ) (hb : rootInterval.Contains b) : i984.Contains (n984 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b976 b hb) (b980 b hb))
    (by norm_num [i984, i976, i980, RationalInterval.add]) (by norm_num [i984, i976, i980, RationalInterval.add])

def n985 (b : ℝ) : ℝ := (n977 b) + (n981 b)
def i985 : RationalInterval := ⟨(-7659326612006347550102815527567 / 1000000000000000000000000000000 : ℚ), (-7659326419584950064991672319241 / 1000000000000000000000000000000 : ℚ)⟩
theorem b985 (b : ℝ) (hb : rootInterval.Contains b) : i985.Contains (n985 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b977 b hb) (b981 b hb))
    (by norm_num [i985, i977, i981, RationalInterval.add]) (by norm_num [i985, i977, i981, RationalInterval.add])

def n986 (b : ℝ) : ℝ := (n978 b) + (n982 b)
def i986 : RationalInterval := ⟨(-56571840717076162095162913909 / 8000000000000000000000000000 : ℚ), (-28285919615332936860521356703 / 4000000000000000000000000000 : ℚ)⟩
theorem b986 (b : ℝ) (hb : rootInterval.Contains b) : i986.Contains (n986 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b978 b hb) (b982 b hb))
    (by norm_num [i986, i978, i982, RationalInterval.add]) (by norm_num [i986, i978, i982, RationalInterval.add])

def n987 (b : ℝ) : ℝ := (n979 b) + (n983 b)
def i987 : RationalInterval := ⟨(-5090805192251032349180866319701 / 1000000000000000000000000000000 : ℚ), (-5090805072562116209751422045951 / 1000000000000000000000000000000 : ℚ)⟩
theorem b987 (b : ℝ) (hb : rootInterval.Contains b) : i987.Contains (n987 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b979 b hb) (b983 b hb))
    (by norm_num [i987, i979, i983, RationalInterval.add]) (by norm_num [i987, i979, i983, RationalInterval.add])

def n988 (b : ℝ) : ℝ := (n909 b) * (n931 b)
def i988 : RationalInterval := ⟨(11757543826166507752343731996023 / 1000000000000000000000000000000 : ℚ), (5878771923300643026042956820843 / 500000000000000000000000000000 : ℚ)⟩
theorem b988 (b : ℝ) (hb : rootInterval.Contains b) : i988.Contains (n988 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b909 b hb) (b931 b hb))
    (by norm_num [i988, i909, i931, RationalInterval.mul]) (by norm_num [i988, i909, i931, RationalInterval.mul])

def n989 (b : ℝ) : ℝ := (n909 b) * (n934 b)
def i989 : RationalInterval := ⟨(892319834767121995831034996693 / 125000000000000000000000000000 : ℚ), (7138558690608087971005280788491 / 1000000000000000000000000000000 : ℚ)⟩
theorem b989 (b : ℝ) (hb : rootInterval.Contains b) : i989.Contains (n989 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b909 b hb) (b934 b hb))
    (by norm_num [i989, i909, i934, RationalInterval.mul]) (by norm_num [i989, i909, i934, RationalInterval.mul])

