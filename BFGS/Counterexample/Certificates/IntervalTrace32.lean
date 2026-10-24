import BFGS.Counterexample.Certificates.IntervalTrace31

/-! Generated arithmetic proofs. Each bound is checked by the Lean kernel. -/
namespace BFGS.Counterexample.Trace
noncomputable section
open BFGS RationalInterval
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false

def n2880 (b : ℝ) : ℝ := (n2878 b) + (n2879 b)
def i2880 : RationalInterval := ⟨(369948462702334298215425759481 / 1000000000000000000000000000000 : ℚ), (369950329157932458075655248119 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2880 (b : ℝ) (hb : rootInterval.Contains b) : i2880.Contains (n2880 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2878 b hb) (b2879 b hb))
    (by norm_num [i2880, i2878, i2879, RationalInterval.add]) (by norm_num [i2880, i2878, i2879, RationalInterval.add])

def n2881 (b : ℝ) : ℝ := (n2510 b) * (n2091 b)
def i2881 : RationalInterval := ⟨(1731972403978078325905477840881 / 125000000000000000000000000000 : ℚ), (6927904669584410103850632464517 / 500000000000000000000000000000 : ℚ)⟩
theorem b2881 (b : ℝ) (hb : rootInterval.Contains b) : i2881.Contains (n2881 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2510 b hb) (b2091 b hb))
    (by norm_num [i2881, i2510, i2091, RationalInterval.mul]) (by norm_num [i2881, i2510, i2091, RationalInterval.mul])

def n2882 (b : ℝ) : ℝ := (n2880 b) + (n2881 b)
def i2882 : RationalInterval := ⟨(14225727694526960905459248486529 / 1000000000000000000000000000000 : ℚ), (14225759668326752665776920177153 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2882 (b : ℝ) (hb : rootInterval.Contains b) : i2882.Contains (n2882 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2880 b hb) (b2881 b hb))
    (by norm_num [i2882, i2880, i2881, RationalInterval.add]) (by norm_num [i2882, i2880, i2881, RationalInterval.add])

def n2883 (b : ℝ) : ℝ := (n2611 b) * (n2136 b)
def i2883 : RationalInterval := ⟨(-15805383251322125559125627344789 / 500000000000000000000000000000 : ℚ), (-6322145257392581721232064137291 / 200000000000000000000000000000 : ℚ)⟩
theorem b2883 (b : ℝ) (hb : rootInterval.Contains b) : i2883.Contains (n2883 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2611 b hb) (b2136 b hb))
    (by norm_num [i2883, i2611, i2136, RationalInterval.mul]) (by norm_num [i2883, i2611, i2136, RationalInterval.mul])

def n2884 (b : ℝ) : ℝ := (n2882 b) + (n2883 b)
def i2884 : RationalInterval := ⟨(-17385038808117290212792006203049 / 1000000000000000000000000000000 : ℚ), (-8692483309318077970191700254651 / 500000000000000000000000000000 : ℚ)⟩
theorem b2884 (b : ℝ) (hb : rootInterval.Contains b) : i2884.Contains (n2884 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2882 b hb) (b2883 b hb))
    (by norm_num [i2884, i2882, i2883, RationalInterval.add]) (by norm_num [i2884, i2882, i2883, RationalInterval.add])

def n2885 (b : ℝ) : ℝ := (n2681 b) * (n2181 b)
def i2885 : RationalInterval := ⟨(11896922690902615696135302427613 / 500000000000000000000000000000 : ℚ), (23793869811681432253617951776117 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2885 (b : ℝ) (hb : rootInterval.Contains b) : i2885.Contains (n2885 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2681 b hb) (b2181 b hb))
    (by norm_num [i2885, i2681, i2181, RationalInterval.mul]) (by norm_num [i2885, i2681, i2181, RationalInterval.mul])

def n2886 (b : ℝ) : ℝ := (n2884 b) + (n2885 b)
def i2886 : RationalInterval := ⟨(6408806573687941179478598652177 / 1000000000000000000000000000000 : ℚ), (1281780638609055262646910253363 / 200000000000000000000000000000 : ℚ)⟩
theorem b2886 (b : ℝ) (hb : rootInterval.Contains b) : i2886.Contains (n2886 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2884 b hb) (b2885 b hb))
    (by norm_num [i2886, i2884, i2885, RationalInterval.add]) (by norm_num [i2886, i2884, i2885, RationalInterval.add])

def n2887 (b : ℝ) : ℝ := (n2688 b) * (n228 b)
def i2887 : RationalInterval := ⟨(6951168346308175051258923492447 / 1000000000000000000000000000000 : ℚ), (6951203215780301174015860795969 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2887 (b : ℝ) (hb : rootInterval.Contains b) : i2887.Contains (n2887 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2688 b hb) (b228 b hb))
    (by norm_num [i2887, i2688, i228, RationalInterval.mul]) (by norm_num [i2887, i2688, i228, RationalInterval.mul])

def n2888 (b : ℝ) : ℝ := (n2695 b) * (n228 b)
def i2888 : RationalInterval := ⟨(13413014645809704578852133261979 / 1000000000000000000000000000000 : ℚ), (13413109385195963463613085924039 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2888 (b : ℝ) (hb : rootInterval.Contains b) : i2888.Contains (n2888 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2695 b hb) (b228 b hb))
    (by norm_num [i2888, i2695, i228, RationalInterval.mul]) (by norm_num [i2888, i2695, i228, RationalInterval.mul])

def n2889 (b : ℝ) : ℝ := (n2702 b) * (n228 b)
def i2889 : RationalInterval := ⟨(-31945228606959370289594657767199 / 500000000000000000000000000000 : ℚ), (-12778052575017270916865876962283 / 200000000000000000000000000000 : ℚ)⟩
theorem b2889 (b : ℝ) (hb : rootInterval.Contains b) : i2889.Contains (n2889 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2702 b hb) (b228 b hb))
    (by norm_num [i2889, i2702, i228, RationalInterval.mul]) (by norm_num [i2889, i2702, i228, RationalInterval.mul])

def n2890 (b : ℝ) : ℝ := (n2709 b) * (n228 b)
def i2890 : RationalInterval := ⟨(1506480294567102695857672196697 / 50000000000000000000000000000 : ℚ), (30129711304953418750255813672163 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2890 (b : ℝ) (hb : rootInterval.Contains b) : i2890.Contains (n2890 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2709 b hb) (b228 b hb))
    (by norm_num [i2890, i2709, i228, RationalInterval.mul]) (by norm_num [i2890, i2709, i228, RationalInterval.mul])

def n2891 (b : ℝ) : ℝ := (n2716 b) * (n228 b)
def i2891 : RationalInterval := ⟨(25092068285256187437331826990703 / 500000000000000000000000000000 : ℚ), (50184275615655436304621690222033 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2891 (b : ℝ) (hb : rootInterval.Contains b) : i2891.Contains (n2891 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2716 b hb) (b228 b hb))
    (by norm_num [i2891, i2716, i228, RationalInterval.mul]) (by norm_num [i2891, i2716, i228, RationalInterval.mul])

def n2892 (b : ℝ) : ℝ := (n2723 b) * (n228 b)
def i2892 : RationalInterval := ⟨(680233374802365152013531033523 / 250000000000000000000000000000 : ℚ), (2720945488265412800236792225991 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2892 (b : ℝ) (hb : rootInterval.Contains b) : i2892.Contains (n2892 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2723 b hb) (b228 b hb))
    (by norm_num [i2892, i2723, i228, RationalInterval.mul]) (by norm_num [i2892, i2723, i228, RationalInterval.mul])

def n2893 (b : ℝ) : ℝ := (n2730 b) * (n228 b)
def i2893 : RationalInterval := ⟨(1929021216506571328697366666727 / 250000000000000000000000000000 : ℚ), (3858057347419344273094747420949 / 500000000000000000000000000000 : ℚ)⟩
theorem b2893 (b : ℝ) (hb : rootInterval.Contains b) : i2893.Contains (n2893 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2730 b hb) (b228 b hb))
    (by norm_num [i2893, i2730, i228, RationalInterval.mul]) (by norm_num [i2893, i2730, i228, RationalInterval.mul])

def n2894 (b : ℝ) : ℝ := (n2737 b) * (n228 b)
def i2894 : RationalInterval := ⟨(-30839560090808341349680042580307 / 1000000000000000000000000000000 : ℚ), (-15419736673292051299500322030373 / 500000000000000000000000000000 : ℚ)⟩
theorem b2894 (b : ℝ) (hb : rootInterval.Contains b) : i2894.Contains (n2894 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2737 b hb) (b228 b hb))
    (by norm_num [i2894, i2737, i228, RationalInterval.mul]) (by norm_num [i2894, i2737, i228, RationalInterval.mul])

def n2895 (b : ℝ) : ℝ := (n2744 b) * (n228 b)
def i2895 : RationalInterval := ⟨(16001394865532677289954833856429 / 1000000000000000000000000000000 : ℚ), (8000720866812429285683547228467 / 500000000000000000000000000000 : ℚ)⟩
theorem b2895 (b : ℝ) (hb : rootInterval.Contains b) : i2895.Contains (n2895 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2744 b hb) (b228 b hb))
    (by norm_num [i2895, i2744, i228, RationalInterval.mul]) (by norm_num [i2895, i2744, i228, RationalInterval.mul])

def n2896 (b : ℝ) : ℝ := (n2751 b) * (n228 b)
def i2896 : RationalInterval := ⟨(21552444640267495211010090000267 / 1000000000000000000000000000000 : ℚ), (4310501607323133855329143592709 / 200000000000000000000000000000 : ℚ)⟩
theorem b2896 (b : ℝ) (hb : rootInterval.Contains b) : i2896.Contains (n2896 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2751 b hb) (b228 b hb))
    (by norm_num [i2896, i2751, i228, RationalInterval.mul]) (by norm_num [i2896, i2751, i228, RationalInterval.mul])

def n2897 (b : ℝ) : ℝ := (n2760 b) * (n228 b)
def i2897 : RationalInterval := ⟨(71619015942296676233998031563 / 25000000000000000000000000000 : ℚ), (2864800803466888228663618228479 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2897 (b : ℝ) (hb : rootInterval.Contains b) : i2897.Contains (n2897 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2760 b hb) (b228 b hb))
    (by norm_num [i2897, i2760, i228, RationalInterval.mul]) (by norm_num [i2897, i2760, i228, RationalInterval.mul])

def n2898 (b : ℝ) : ℝ := (n2769 b) * (n228 b)
def i2898 : RationalInterval := ⟨(6924437251421943896864222927767 / 1000000000000000000000000000000 : ℚ), (6924527658687999287116747861257 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2898 (b : ℝ) (hb : rootInterval.Contains b) : i2898.Contains (n2898 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2769 b hb) (b228 b hb))
    (by norm_num [i2898, i2769, i228, RationalInterval.mul]) (by norm_num [i2898, i2769, i228, RationalInterval.mul])

def n2899 (b : ℝ) : ℝ := (n2778 b) * (n228 b)
def i2899 : RationalInterval := ⟨(-30745352445539429087495195286847 / 1000000000000000000000000000000 : ℚ), (-30744968903536419324013038845213 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2899 (b : ℝ) (hb : rootInterval.Contains b) : i2899.Contains (n2899 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2778 b hb) (b228 b hb))
    (by norm_num [i2899, i2778, i228, RationalInterval.mul]) (by norm_num [i2899, i2778, i228, RationalInterval.mul])

def n2900 (b : ℝ) : ℝ := (n2787 b) * (n228 b)
def i2900 : RationalInterval := ⟨(801220433877787176249282312253 / 50000000000000000000000000000 : ℚ), (16024609607701076786243580012931 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2900 (b : ℝ) (hb : rootInterval.Contains b) : i2900.Contains (n2900 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2787 b hb) (b228 b hb))
    (by norm_num [i2900, i2787, i228, RationalInterval.mul]) (by norm_num [i2900, i2787, i228, RationalInterval.mul])

def n2901 (b : ℝ) : ℝ := (n2796 b) * (n228 b)
def i2901 : RationalInterval := ⟨(22523214570334392056950162213071 / 1000000000000000000000000000000 : ℚ), (1126175034231329091163007758481 / 50000000000000000000000000000 : ℚ)⟩
theorem b2901 (b : ℝ) (hb : rootInterval.Contains b) : i2901.Contains (n2901 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2796 b hb) (b228 b hb))
    (by norm_num [i2901, i2796, i228, RationalInterval.mul]) (by norm_num [i2901, i2796, i228, RationalInterval.mul])

def n2902 (b : ℝ) : ℝ := (n2805 b) * (n228 b)
def i2902 : RationalInterval := ⟨(1635813780658810585720411329081 / 1000000000000000000000000000000 : ℚ), (1635832058398698327183188140307 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2902 (b : ℝ) (hb : rootInterval.Contains b) : i2902.Contains (n2902 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2805 b hb) (b228 b hb))
    (by norm_num [i2902, i2805, i228, RationalInterval.mul]) (by norm_num [i2902, i2805, i228, RationalInterval.mul])

def n2903 (b : ℝ) : ℝ := (n2814 b) * (n228 b)
def i2903 : RationalInterval := ⟨(408440763282058559908650004757 / 100000000000000000000000000000 : ℚ), (4084449131266239568193281615401 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2903 (b : ℝ) (hb : rootInterval.Contains b) : i2903.Contains (n2903 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2814 b hb) (b228 b hb))
    (by norm_num [i2903, i2814, i228, RationalInterval.mul]) (by norm_num [i2903, i2814, i228, RationalInterval.mul])

def n2904 (b : ℝ) : ℝ := (n2823 b) * (n228 b)
def i2904 : RationalInterval := ⟨(-1849959414724814772155369934269 / 100000000000000000000000000000 : ℚ), (-9249710785864025682784384938407 / 500000000000000000000000000000 : ℚ)⟩
theorem b2904 (b : ℝ) (hb : rootInterval.Contains b) : i2904.Contains (n2904 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2823 b hb) (b228 b hb))
    (by norm_num [i2904, i2823, i228, RationalInterval.mul]) (by norm_num [i2904, i2823, i228, RationalInterval.mul])

def n2905 (b : ℝ) : ℝ := (n2832 b) * (n228 b)
def i2905 : RationalInterval := ⟨(20204011873856531013633894229 / 2000000000000000000000000000 : ℚ), (10102096619365562364830655265397 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2905 (b : ℝ) (hb : rootInterval.Contains b) : i2905.Contains (n2905 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2832 b hb) (b228 b hb))
    (by norm_num [i2905, i2832, i228, RationalInterval.mul]) (by norm_num [i2905, i2832, i228, RationalInterval.mul])

def n2906 (b : ℝ) : ℝ := (n2841 b) * (n228 b)
def i2906 : RationalInterval := ⟨(2668786496725573354370803600579 / 200000000000000000000000000000 : ℚ), (13344061051029631705876697327641 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2906 (b : ℝ) (hb : rootInterval.Contains b) : i2906.Contains (n2906 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2841 b hb) (b228 b hb))
    (by norm_num [i2906, i2841, i228, RationalInterval.mul]) (by norm_num [i2906, i2841, i228, RationalInterval.mul])

def n2907 (b : ℝ) : ℝ := (n2850 b) * (n228 b)
def i2907 : RationalInterval := ⟨(853750005135135056657680033629 / 1000000000000000000000000000000 : ℚ), (213442661937114746546751280641 / 250000000000000000000000000000 : ℚ)⟩
theorem b2907 (b : ℝ) (hb : rootInterval.Contains b) : i2907.Contains (n2907 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2850 b hb) (b228 b hb))
    (by norm_num [i2907, i2850, i228, RationalInterval.mul]) (by norm_num [i2907, i2850, i228, RationalInterval.mul])

def n2908 (b : ℝ) : ℝ := (n2859 b) * (n228 b)
def i2908 : RationalInterval := ⟨(70466455710765364090529860747 / 31250000000000000000000000000 : ℚ), (1127488551752537724615973318137 / 500000000000000000000000000000 : ℚ)⟩
theorem b2908 (b : ℝ) (hb : rootInterval.Contains b) : i2908.Contains (n2908 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2859 b hb) (b228 b hb))
    (by norm_num [i2908, i2859, i228, RationalInterval.mul]) (by norm_num [i2908, i2859, i228, RationalInterval.mul])

def n2909 (b : ℝ) : ℝ := (n2868 b) * (n228 b)
def i2909 : RationalInterval := ⟨(-10082718088774729951715775950007 / 1000000000000000000000000000000 : ℚ), (-10082551976920396525156678649483 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2909 (b : ℝ) (hb : rootInterval.Contains b) : i2909.Contains (n2909 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2868 b hb) (b228 b hb))
    (by norm_num [i2909, i2868, i228, RationalInterval.mul]) (by norm_num [i2909, i2868, i228, RationalInterval.mul])

def n2910 (b : ℝ) : ℝ := (n2877 b) * (n228 b)
def i2910 : RationalInterval := ⟨(5075263269099947841642190660753 / 1000000000000000000000000000000 : ℚ), (5075351998868714827886723089577 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2910 (b : ℝ) (hb : rootInterval.Contains b) : i2910.Contains (n2910 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2877 b hb) (b228 b hb))
    (by norm_num [i2910, i2877, i228, RationalInterval.mul]) (by norm_num [i2910, i2877, i228, RationalInterval.mul])

def n2911 (b : ℝ) : ℝ := (n2886 b) * (n228 b)
def i2911 : RationalInterval := ⟨(8111145819823800555277601419161 / 1000000000000000000000000000000 : ℚ), (8111268103697927833937478947063 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2911 (b : ℝ) (hb : rootInterval.Contains b) : i2911.Contains (n2911 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2886 b hb) (b228 b hb))
    (by norm_num [i2911, i2886, i228, RationalInterval.mul]) (by norm_num [i2911, i2886, i228, RationalInterval.mul])

def n2912 (b : ℝ) : ℝ := (n136 b) * (n2897 b)
def i2912 : RationalInterval := ⟨(3778422581199707360318427122237 / 1000000000000000000000000000000 : ℚ), (1889237779164179464204455445049 / 500000000000000000000000000000 : ℚ)⟩
theorem b2912 (b : ℝ) (hb : rootInterval.Contains b) : i2912.Contains (n2912 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b136 b hb) (b2897 b hb))
    (by norm_num [i2912, i136, i2897, RationalInterval.mul]) (by norm_num [i2912, i136, i2897, RationalInterval.mul])

def n2913 (b : ℝ) : ℝ := -(n2912 b)
def i2913 : RationalInterval := ⟨(-1889237779164179464204455445049 / 500000000000000000000000000000 : ℚ), (-3778422581199707360318427122237 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2913 (b : ℝ) (hb : rootInterval.Contains b) : i2913.Contains (n2913 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b2912 b hb))
    (by norm_num [i2913, i2912, RationalInterval.neg]) (by norm_num [i2913, i2912, RationalInterval.neg])

def n2914 (b : ℝ) : ℝ := (n2887 b) + (n2913 b)
def i2914 : RationalInterval := ⟨(3172692787979816122850012602349 / 1000000000000000000000000000000 : ℚ), (793195158645148453424358418433 / 250000000000000000000000000000 : ℚ)⟩
theorem b2914 (b : ℝ) (hb : rootInterval.Contains b) : i2914.Contains (n2914 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2887 b hb) (b2913 b hb))
    (by norm_num [i2914, i2887, i2913, RationalInterval.add]) (by norm_num [i2914, i2887, i2913, RationalInterval.add])

def n2915 (b : ℝ) : ℝ := (n136 b) * (n2898 b)
def i2915 : RationalInterval := ⟨(9132857289589456628248648679371 / 1000000000000000000000000000000 : ℚ), (4566488266768546926413854778207 / 500000000000000000000000000000 : ℚ)⟩
theorem b2915 (b : ℝ) (hb : rootInterval.Contains b) : i2915.Contains (n2915 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b136 b hb) (b2898 b hb))
    (by norm_num [i2915, i136, i2898, RationalInterval.mul]) (by norm_num [i2915, i136, i2898, RationalInterval.mul])

def n2916 (b : ℝ) : ℝ := -(n2915 b)
def i2916 : RationalInterval := ⟨(-4566488266768546926413854778207 / 500000000000000000000000000000 : ℚ), (-9132857289589456628248648679371 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2916 (b : ℝ) (hb : rootInterval.Contains b) : i2916.Contains (n2916 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b2915 b hb))
    (by norm_num [i2916, i2915, RationalInterval.neg]) (by norm_num [i2916, i2915, RationalInterval.neg])

def n2917 (b : ℝ) : ℝ := (n2888 b) + (n2916 b)
def i2917 : RationalInterval := ⟨(856007622454522145204884741113 / 200000000000000000000000000000 : ℚ), (1070063023901626708841109311167 / 250000000000000000000000000000 : ℚ)⟩
theorem b2917 (b : ℝ) (hb : rootInterval.Contains b) : i2917.Contains (n2917 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2888 b hb) (b2916 b hb))
    (by norm_num [i2917, i2888, i2916, RationalInterval.add]) (by norm_num [i2917, i2888, i2916, RationalInterval.add])

def n2918 (b : ℝ) : ℝ := (n136 b) * (n2900 b)
def i2918 : RationalInterval := ⟨(5283773694827063305167717332801 / 250000000000000000000000000000 : ℚ), (21135359799249700275659439240223 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2918 (b : ℝ) (hb : rootInterval.Contains b) : i2918.Contains (n2918 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b136 b hb) (b2900 b hb))
    (by norm_num [i2918, i136, i2900, RationalInterval.mul]) (by norm_num [i2918, i136, i2900, RationalInterval.mul])

def n2919 (b : ℝ) : ℝ := -(n2918 b)
def i2919 : RationalInterval := ⟨(-21135359799249700275659439240223 / 1000000000000000000000000000000 : ℚ), (-5283773694827063305167717332801 / 250000000000000000000000000000 : ℚ)⟩
theorem b2919 (b : ℝ) (hb : rootInterval.Contains b) : i2919.Contains (n2919 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b2918 b hb))
    (by norm_num [i2919, i2918, RationalInterval.neg]) (by norm_num [i2919, i2918, RationalInterval.neg])

def n2920 (b : ℝ) : ℝ := (n2890 b) + (n2919 b)
def i2920 : RationalInterval := ⟨(8994246092092353641494004693717 / 1000000000000000000000000000000 : ℚ), (8994616525645165529584944340959 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2920 (b : ℝ) (hb : rootInterval.Contains b) : i2920.Contains (n2920 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2890 b hb) (b2919 b hb))
    (by norm_num [i2920, i2890, i2919, RationalInterval.add]) (by norm_num [i2920, i2890, i2919, RationalInterval.add])

def n2921 (b : ℝ) : ℝ := (n136 b) * (n2901 b)
def i2921 : RationalInterval := ⟨(2970657353150609211640668501787 / 100000000000000000000000000000 : ℚ), (29706950906276945998701682106453 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2921 (b : ℝ) (hb : rootInterval.Contains b) : i2921.Contains (n2921 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b136 b hb) (b2901 b hb))
    (by norm_num [i2921, i136, i2901, RationalInterval.mul]) (by norm_num [i2921, i136, i2901, RationalInterval.mul])

def n2922 (b : ℝ) : ℝ := -(n2921 b)
def i2922 : RationalInterval := ⟨(-29706950906276945998701682106453 / 1000000000000000000000000000000 : ℚ), (-2970657353150609211640668501787 / 100000000000000000000000000000 : ℚ)⟩
theorem b2922 (b : ℝ) (hb : rootInterval.Contains b) : i2922.Contains (n2922 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b2921 b hb))
    (by norm_num [i2922, i2921, RationalInterval.neg]) (by norm_num [i2922, i2921, RationalInterval.neg])

def n2923 (b : ℝ) : ℝ := (n2891 b) + (n2922 b)
def i2923 : RationalInterval := ⟨(20477185664235428875961971874953 / 1000000000000000000000000000000 : ℚ), (20477702084149344188215005204163 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2923 (b : ℝ) (hb : rootInterval.Contains b) : i2923.Contains (n2923 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2891 b hb) (b2922 b hb))
    (by norm_num [i2923, i2891, i2922, RationalInterval.add]) (by norm_num [i2923, i2891, i2922, RationalInterval.add])

def n2924 (b : ℝ) : ℝ := (n150 b) * (n2897 b)
def i2924 : RationalInterval := ⟨(4952577148883591509603595840501 / 1000000000000000000000000000000 : ℚ), (4952646587740556574356925828371 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2924 (b : ℝ) (hb : rootInterval.Contains b) : i2924.Contains (n2924 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b150 b hb) (b2897 b hb))
    (by norm_num [i2924, i150, i2897, RationalInterval.mul]) (by norm_num [i2924, i150, i2897, RationalInterval.mul])

def n2925 (b : ℝ) : ℝ := -(n2924 b)
def i2925 : RationalInterval := ⟨(-4952646587740556574356925828371 / 1000000000000000000000000000000 : ℚ), (-4952577148883591509603595840501 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2925 (b : ℝ) (hb : rootInterval.Contains b) : i2925.Contains (n2925 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b2924 b hb))
    (by norm_num [i2925, i2924, RationalInterval.neg]) (by norm_num [i2925, i2924, RationalInterval.neg])

def n2926 (b : ℝ) : ℝ := (n2892 b) + (n2925 b)
def i2926 : RationalInterval := ⟨(-2231713088531095966302801694279 / 1000000000000000000000000000000 : ℚ), (-223163166061817870936680361451 / 100000000000000000000000000000 : ℚ)⟩
theorem b2926 (b : ℝ) (hb : rootInterval.Contains b) : i2926.Contains (n2926 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2892 b hb) (b2925 b hb))
    (by norm_num [i2926, i2892, i2925, RationalInterval.add]) (by norm_num [i2926, i2892, i2925, RationalInterval.add])

def n2927 (b : ℝ) : ℝ := (n150 b) * (n2898 b)
def i2927 : RationalInterval := ⟨(1496364532566195918019546846851 / 125000000000000000000000000000 : ℚ), (11971072557300966446173208704249 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2927 (b : ℝ) (hb : rootInterval.Contains b) : i2927.Contains (n2927 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b150 b hb) (b2898 b hb))
    (by norm_num [i2927, i150, i2898, RationalInterval.mul]) (by norm_num [i2927, i150, i2898, RationalInterval.mul])

def n2928 (b : ℝ) : ℝ := -(n2927 b)
def i2928 : RationalInterval := ⟨(-11971072557300966446173208704249 / 1000000000000000000000000000000 : ℚ), (-1496364532566195918019546846851 / 125000000000000000000000000000 : ℚ)⟩
theorem b2928 (b : ℝ) (hb : rootInterval.Contains b) : i2928.Contains (n2928 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b2927 b hb))
    (by norm_num [i2928, i2927, RationalInterval.neg]) (by norm_num [i2928, i2927, RationalInterval.neg])

def n2929 (b : ℝ) : ℝ := (n2893 b) + (n2928 b)
def i2929 : RationalInterval := ⟨(-4254987691274681131383742037341 / 1000000000000000000000000000000 : ℚ), (-425480156569087879796687993291 / 100000000000000000000000000000 : ℚ)⟩
theorem b2929 (b : ℝ) (hb : rootInterval.Contains b) : i2929.Contains (n2929 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2893 b hb) (b2928 b hb))
    (by norm_num [i2929, i2893, i2928, RationalInterval.add]) (by norm_num [i2929, i2893, i2928, RationalInterval.add])

def n2930 (b : ℝ) : ℝ := (n150 b) * (n2900 b)
def i2930 : RationalInterval := ⟨(27702880023085083136583021613001 / 1000000000000000000000000000000 : ℚ), (1731451712048602208094366080577 / 62500000000000000000000000000 : ℚ)⟩
theorem b2930 (b : ℝ) (hb : rootInterval.Contains b) : i2930.Contains (n2930 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b150 b hb) (b2900 b hb))
    (by norm_num [i2930, i150, i2900, RationalInterval.mul]) (by norm_num [i2930, i150, i2900, RationalInterval.mul])

def n2931 (b : ℝ) : ℝ := -(n2930 b)
def i2931 : RationalInterval := ⟨(-1731451712048602208094366080577 / 62500000000000000000000000000 : ℚ), (-27702880023085083136583021613001 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2931 (b : ℝ) (hb : rootInterval.Contains b) : i2931.Contains (n2931 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b2930 b hb))
    (by norm_num [i2931, i2930, RationalInterval.neg]) (by norm_num [i2931, i2930, RationalInterval.neg])

def n2932 (b : ℝ) : ℝ := (n2895 b) + (n2931 b)
def i2932 : RationalInterval := ⟨(-11701832527244958039555023432803 / 1000000000000000000000000000000 : ℚ), (-11701438289460224565215927156067 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2932 (b : ℝ) (hb : rootInterval.Contains b) : i2932.Contains (n2932 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2895 b hb) (b2931 b hb))
    (by norm_num [i2932, i2895, i2931, RationalInterval.add]) (by norm_num [i2932, i2895, i2931, RationalInterval.add])

def n2933 (b : ℝ) : ℝ := (n150 b) * (n2901 b)
def i2933 : RationalInterval := ⟨(38937967917038289371126610475361 / 1000000000000000000000000000000 : ℚ), (9734615638432228243949520008451 / 250000000000000000000000000000 : ℚ)⟩
theorem b2933 (b : ℝ) (hb : rootInterval.Contains b) : i2933.Contains (n2933 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b150 b hb) (b2901 b hb))
    (by norm_num [i2933, i150, i2901, RationalInterval.mul]) (by norm_num [i2933, i150, i2901, RationalInterval.mul])

def n2934 (b : ℝ) : ℝ := -(n2933 b)
def i2934 : RationalInterval := ⟨(-9734615638432228243949520008451 / 250000000000000000000000000000 : ℚ), (-38937967917038289371126610475361 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2934 (b : ℝ) (hb : rootInterval.Contains b) : i2934.Contains (n2934 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b2933 b hb))
    (by norm_num [i2934, i2933, RationalInterval.neg]) (by norm_num [i2934, i2933, RationalInterval.neg])

def n2935 (b : ℝ) : ℝ := (n2896 b) + (n2934 b)
def i2935 : RationalInterval := ⟨(-17386017913461417764787990033537 / 1000000000000000000000000000000 : ℚ), (-2173182485052827511810111563977 / 125000000000000000000000000000 : ℚ)⟩
theorem b2935 (b : ℝ) (hb : rootInterval.Contains b) : i2935.Contains (n2935 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2896 b hb) (b2934 b hb))
    (by norm_num [i2935, i2896, i2934, RationalInterval.add]) (by norm_num [i2935, i2896, i2934, RationalInterval.add])

def n2936 (b : ℝ) : ℝ := (n2897 b) * (n64 b)
def i2936 : RationalInterval := ⟨(71619015942296676233998031563 / 50000000000000000000000000000 : ℚ), (2238125627708506428643451741 / 1562500000000000000000000000 : ℚ)⟩
theorem b2936 (b : ℝ) (hb : rootInterval.Contains b) : i2936.Contains (n2936 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2897 b hb) (b64 b hb))
    (by norm_num [i2936, i2897, i64, RationalInterval.mul]) (by norm_num [i2936, i2897, i64, RationalInterval.mul])

def n2937 (b : ℝ) : ℝ := -(n2936 b)
def i2937 : RationalInterval := ⟨(-2238125627708506428643451741 / 1562500000000000000000000000 : ℚ), (-71619015942296676233998031563 / 50000000000000000000000000000 : ℚ)⟩
theorem b2937 (b : ℝ) (hb : rootInterval.Contains b) : i2937.Contains (n2937 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b2936 b hb))
    (by norm_num [i2937, i2936, RationalInterval.neg]) (by norm_num [i2937, i2936, RationalInterval.neg])

def n2938 (b : ℝ) : ℝ := (n2902 b) + (n2937 b)
def i2938 : RationalInterval := ⟨(203413378925366471388602214841 / 1000000000000000000000000000000 : ℚ), (203451739552764802503227509047 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2938 (b : ℝ) (hb : rootInterval.Contains b) : i2938.Contains (n2938 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2902 b hb) (b2937 b hb))
    (by norm_num [i2938, i2902, i2937, RationalInterval.add]) (by norm_num [i2938, i2902, i2937, RationalInterval.add])

def n2939 (b : ℝ) : ℝ := (n2898 b) * (n64 b)
def i2939 : RationalInterval := ⟨(3462218625710971948432111463883 / 1000000000000000000000000000000 : ℚ), (3462263829343999643558373930629 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2939 (b : ℝ) (hb : rootInterval.Contains b) : i2939.Contains (n2939 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2898 b hb) (b64 b hb))
    (by norm_num [i2939, i2898, i64, RationalInterval.mul]) (by norm_num [i2939, i2898, i64, RationalInterval.mul])

def n2940 (b : ℝ) : ℝ := -(n2939 b)
def i2940 : RationalInterval := ⟨(-3462263829343999643558373930629 / 1000000000000000000000000000000 : ℚ), (-3462218625710971948432111463883 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2940 (b : ℝ) (hb : rootInterval.Contains b) : i2940.Contains (n2940 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b2939 b hb))
    (by norm_num [i2940, i2939, RationalInterval.neg]) (by norm_num [i2940, i2939, RationalInterval.neg])

def n2941 (b : ℝ) : ℝ := (n2903 b) + (n2940 b)
def i2941 : RationalInterval := ⟨(622143803476585955528126116941 / 1000000000000000000000000000000 : ℚ), (311115252777633809880585075759 / 500000000000000000000000000000 : ℚ)⟩
theorem b2941 (b : ℝ) (hb : rootInterval.Contains b) : i2941.Contains (n2941 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2903 b hb) (b2940 b hb))
    (by norm_num [i2941, i2903, i2940, RationalInterval.add]) (by norm_num [i2941, i2903, i2940, RationalInterval.add])

def n2942 (b : ℝ) : ℝ := (n2900 b) * (n64 b)
def i2942 : RationalInterval := ⟨(801220433877787176249282312253 / 100000000000000000000000000000 : ℚ), (4006152401925269196560895003233 / 500000000000000000000000000000 : ℚ)⟩
theorem b2942 (b : ℝ) (hb : rootInterval.Contains b) : i2942.Contains (n2942 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2900 b hb) (b64 b hb))
    (by norm_num [i2942, i2900, i64, RationalInterval.mul]) (by norm_num [i2942, i2900, i64, RationalInterval.mul])

def n2943 (b : ℝ) : ℝ := -(n2942 b)
def i2943 : RationalInterval := ⟨(-4006152401925269196560895003233 / 500000000000000000000000000000 : ℚ), (-801220433877787176249282312253 / 100000000000000000000000000000 : ℚ)⟩
theorem b2943 (b : ℝ) (hb : rootInterval.Contains b) : i2943.Contains (n2943 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b2942 b hb))
    (by norm_num [i2943, i2942, RationalInterval.neg]) (by norm_num [i2943, i2942, RationalInterval.neg])

def n2944 (b : ℝ) : ℝ := (n2905 b) + (n2943 b)
def i2944 : RationalInterval := ⟨(1044850566538863556847578554017 / 500000000000000000000000000000 : ℚ), (2089892280587690602337832142867 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2944 (b : ℝ) (hb : rootInterval.Contains b) : i2944.Contains (n2944 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2905 b hb) (b2943 b hb))
    (by norm_num [i2944, i2905, i2943, RationalInterval.add]) (by norm_num [i2944, i2905, i2943, RationalInterval.add])

def n2945 (b : ℝ) : ℝ := (n2901 b) * (n64 b)
def i2945 : RationalInterval := ⟨(2252321457033439205695016221307 / 200000000000000000000000000000 : ℚ), (1126175034231329091163007758481 / 100000000000000000000000000000 : ℚ)⟩
theorem b2945 (b : ℝ) (hb : rootInterval.Contains b) : i2945.Contains (n2945 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2901 b hb) (b64 b hb))
    (by norm_num [i2945, i2901, i64, RationalInterval.mul]) (by norm_num [i2945, i2901, i64, RationalInterval.mul])

def n2946 (b : ℝ) : ℝ := -(n2945 b)
def i2946 : RationalInterval := ⟨(-1126175034231329091163007758481 / 100000000000000000000000000000 : ℚ), (-2252321457033439205695016221307 / 200000000000000000000000000000 : ℚ)⟩
theorem b2946 (b : ℝ) (hb : rootInterval.Contains b) : i2946.Contains (n2946 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b2945 b hb))
    (by norm_num [i2946, i2945, RationalInterval.neg]) (by norm_num [i2946, i2945, RationalInterval.neg])

def n2947 (b : ℝ) : ℝ := (n2906 b) + (n2946 b)
def i2947 : RationalInterval := ⟨(416436428262915172044788083617 / 200000000000000000000000000000 : ℚ), (1041226882931217838700808110553 / 500000000000000000000000000000 : ℚ)⟩
theorem b2947 (b : ℝ) (hb : rootInterval.Contains b) : i2947.Contains (n2947 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2906 b hb) (b2946 b hb))
    (by norm_num [i2947, i2906, i2946, RationalInterval.add]) (by norm_num [i2947, i2906, i2946, RationalInterval.add])

def n2948 (b : ℝ) : ℝ := (n61 b) * (n2897 b)
def i2948 : RationalInterval := ⟨(1015421850420190541723950294133 / 1000000000000000000000000000000 : ℚ), (1015436087290655869322084829157 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2948 (b : ℝ) (hb : rootInterval.Contains b) : i2948.Contains (n2948 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b61 b hb) (b2897 b hb))
    (by norm_num [i2948, i61, i2897, RationalInterval.mul]) (by norm_num [i2948, i61, i2897, RationalInterval.mul])

def n2949 (b : ℝ) : ℝ := -(n2948 b)
def i2949 : RationalInterval := ⟨(-1015436087290655869322084829157 / 1000000000000000000000000000000 : ℚ), (-1015421850420190541723950294133 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2949 (b : ℝ) (hb : rootInterval.Contains b) : i2949.Contains (n2949 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b2948 b hb))
    (by norm_num [i2949, i2948, RationalInterval.neg]) (by norm_num [i2949, i2948, RationalInterval.neg])

def n2950 (b : ℝ) : ℝ := (n2907 b) + (n2949 b)
def i2950 : RationalInterval := ⟨(-20210760269440101583050599441 / 125000000000000000000000000000 : ℚ), (-161651202671731555536945171569 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2950 (b : ℝ) (hb : rootInterval.Contains b) : i2950.Contains (n2950 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2907 b hb) (b2949 b hb))
    (by norm_num [i2950, i2907, i2949, RationalInterval.add]) (by norm_num [i2950, i2907, i2949, RationalInterval.add])

def n2951 (b : ℝ) : ℝ := (n61 b) * (n2898 b)
def i2951 : RationalInterval := ⟨(30679809660391098197822411491 / 12500000000000000000000000000 : ℚ), (2454416817938922448605479271111 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2951 (b : ℝ) (hb : rootInterval.Contains b) : i2951.Contains (n2951 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b61 b hb) (b2898 b hb))
    (by norm_num [i2951, i61, i2898, RationalInterval.mul]) (by norm_num [i2951, i61, i2898, RationalInterval.mul])

def n2952 (b : ℝ) : ℝ := -(n2951 b)
def i2952 : RationalInterval := ⟨(-2454416817938922448605479271111 / 1000000000000000000000000000000 : ℚ), (-30679809660391098197822411491 / 12500000000000000000000000000 : ℚ)⟩
theorem b2952 (b : ℝ) (hb : rootInterval.Contains b) : i2952.Contains (n2952 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b2951 b hb))
    (by norm_num [i2952, i2951, RationalInterval.neg]) (by norm_num [i2952, i2951, RationalInterval.neg])

def n2953 (b : ℝ) : ℝ := (n2908 b) + (n2952 b)
def i2953 : RationalInterval := ⟨(-199490235194430797708523727207 / 1000000000000000000000000000000 : ℚ), (-99703834663106203296923141503 / 500000000000000000000000000000 : ℚ)⟩
theorem b2953 (b : ℝ) (hb : rootInterval.Contains b) : i2953.Contains (n2953 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2908 b hb) (b2952 b hb))
    (by norm_num [i2953, i2908, i2952, RationalInterval.add]) (by norm_num [i2953, i2908, i2952, RationalInterval.add])

def n2954 (b : ℝ) : ℝ := (n61 b) * (n2900 b)
def i2954 : RationalInterval := ⟨(5679893285731180801272823307021 / 1000000000000000000000000000000 : ℚ), (709995563247906766700960422201 / 125000000000000000000000000000 : ℚ)⟩
theorem b2954 (b : ℝ) (hb : rootInterval.Contains b) : i2954.Contains (n2954 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b61 b hb) (b2900 b hb))
    (by norm_num [i2954, i61, i2900, RationalInterval.mul]) (by norm_num [i2954, i61, i2900, RationalInterval.mul])

def n2955 (b : ℝ) : ℝ := -(n2954 b)
def i2955 : RationalInterval := ⟨(-709995563247906766700960422201 / 125000000000000000000000000000 : ℚ), (-5679893285731180801272823307021 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2955 (b : ℝ) (hb : rootInterval.Contains b) : i2955.Contains (n2955 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b2954 b hb))
    (by norm_num [i2955, i2954, RationalInterval.neg]) (by norm_num [i2955, i2954, RationalInterval.neg])

def n2956 (b : ℝ) : ℝ := (n2910 b) + (n2955 b)
def i2956 : RationalInterval := ⟨(-120940247376661258393098543371 / 200000000000000000000000000000 : ℚ), (-151135321715616493346525054361 / 250000000000000000000000000000 : ℚ)⟩
theorem b2956 (b : ℝ) (hb : rootInterval.Contains b) : i2956.Contains (n2956 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2910 b hb) (b2955 b hb))
    (by norm_num [i2956, i2910, i2955, RationalInterval.add]) (by norm_num [i2956, i2910, i2955, RationalInterval.add])

def n2957 (b : ℝ) : ℝ := (n61 b) * (n2901 b)
def i2957 : RationalInterval := ⟨(3991705958869694841003226833909 / 500000000000000000000000000000 : ℚ), (399175666587493213860465646011 / 50000000000000000000000000000 : ℚ)⟩
theorem b2957 (b : ℝ) (hb : rootInterval.Contains b) : i2957.Contains (n2957 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b61 b hb) (b2901 b hb))
    (by norm_num [i2957, i61, i2901, RationalInterval.mul]) (by norm_num [i2957, i61, i2901, RationalInterval.mul])

def n2958 (b : ℝ) : ℝ := -(n2957 b)
def i2958 : RationalInterval := ⟨(-399175666587493213860465646011 / 50000000000000000000000000000 : ℚ), (-3991705958869694841003226833909 / 500000000000000000000000000000 : ℚ)⟩
theorem b2958 (b : ℝ) (hb : rootInterval.Contains b) : i2958.Contains (n2958 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b2957 b hb))
    (by norm_num [i2958, i2957, RationalInterval.neg]) (by norm_num [i2958, i2957, RationalInterval.neg])

def n2959 (b : ℝ) : ℝ := (n2911 b) + (n2958 b)
def i2959 : RationalInterval := ⟨(127632488073936278068288498941 / 1000000000000000000000000000000 : ℚ), (25571237191707630386205055849 / 200000000000000000000000000000 : ℚ)⟩
theorem b2959 (b : ℝ) (hb : rootInterval.Contains b) : i2959.Contains (n2959 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2911 b hb) (b2958 b hb))
    (by norm_num [i2959, i2911, i2958, RationalInterval.add]) (by norm_num [i2959, i2911, i2958, RationalInterval.add])

def n2960 (b : ℝ) : ℝ := ((464 : ℚ) : ℝ)
def i2960 : RationalInterval := ⟨(464 : ℚ), (464 : ℚ)⟩
theorem b2960 (b : ℝ) (hb : rootInterval.Contains b) : i2960.Contains (n2960 b) := by
  exact RationalInterval.contains_point (464 : ℚ)

def n2961 (b : ℝ) : ℝ := (n2914 b) * (n2960 b)
def i2961 : RationalInterval := ⟨(92008090851414667562650365468121 / 62500000000000000000000000000 : ℚ), (23002659600709305149306394134557 / 15625000000000000000000000000 : ℚ)⟩
theorem b2961 (b : ℝ) (hb : rootInterval.Contains b) : i2961.Contains (n2961 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2914 b hb) (b2960 b hb))
    (by norm_num [i2961, i2914, i2960, RationalInterval.mul]) (by norm_num [i2961, i2914, i2960, RationalInterval.mul])

def n2962 (b : ℝ) : ℝ := ((1077 : ℚ) : ℝ)
def i2962 : RationalInterval := ⟨(1077 : ℚ), (1077 : ℚ)⟩
theorem b2962 (b : ℝ) (hb : rootInterval.Contains b) : i2962.Contains (n2962 b) := by
  exact RationalInterval.contains_point (1077 : ℚ)

def n2963 (b : ℝ) : ℝ := (n2926 b) * (n2962 b)
def i2963 : RationalInterval := ⟨(-2403554996347990355708117424738483 / 1000000000000000000000000000000 : ℚ), (-240346729848577846998804749282727 / 100000000000000000000000000000 : ℚ)⟩
theorem b2963 (b : ℝ) (hb : rootInterval.Contains b) : i2963.Contains (n2963 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2926 b hb) (b2962 b hb))
    (by norm_num [i2963, i2926, i2962, RationalInterval.mul]) (by norm_num [i2963, i2926, i2962, RationalInterval.mul])

def n2964 (b : ℝ) : ℝ := (n2961 b) + (n2963 b)
def i2964 : RationalInterval := ⟨(-931425542725355674705711577248547 / 1000000000000000000000000000000 : ℚ), (-465648542020191470216219134107811 / 500000000000000000000000000000 : ℚ)⟩
theorem b2964 (b : ℝ) (hb : rootInterval.Contains b) : i2964.Contains (n2964 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2961 b hb) (b2963 b hb))
    (by norm_num [i2964, i2961, i2963, RationalInterval.add]) (by norm_num [i2964, i2961, i2963, RationalInterval.add])

def n2965 (b : ℝ) : ℝ := ((4501 : ℚ) : ℝ)
def i2965 : RationalInterval := ⟨(4501 : ℚ), (4501 : ℚ)⟩
theorem b2965 (b : ℝ) (hb : rootInterval.Contains b) : i2965.Contains (n2965 b) := by
  exact RationalInterval.contains_point (4501 : ℚ)

def n2966 (b : ℝ) : ℝ := (n2938 b) * (n2965 b)
def i2966 : RationalInterval := ⟨(915563618543074487720098568999341 / 1000000000000000000000000000000 : ℚ), (915736279726994376067027018220547 / 1000000000000000000000000000000 : ℚ)⟩
theorem b2966 (b : ℝ) (hb : rootInterval.Contains b) : i2966.Contains (n2966 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2938 b hb) (b2965 b hb))
    (by norm_num [i2966, i2938, i2965, RationalInterval.mul]) (by norm_num [i2966, i2938, i2965, RationalInterval.mul])

def n2967 (b : ℝ) : ℝ := (n2964 b) + (n2966 b)
def i2967 : RationalInterval := ⟨(-7930962091140593492806504124603 / 500000000000000000000000000000 : ℚ), (-622432172535542574616449999803 / 40000000000000000000000000000 : ℚ)⟩
theorem b2967 (b : ℝ) (hb : rootInterval.Contains b) : i2967.Contains (n2967 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b2964 b hb) (b2966 b hb))
    (by norm_num [i2967, i2964, i2966, RationalInterval.add]) (by norm_num [i2967, i2964, i2966, RationalInterval.add])

def n2968 (b : ℝ) : ℝ := ((-1708 : ℚ) : ℝ)
def i2968 : RationalInterval := ⟨(-1708 : ℚ), (-1708 : ℚ)⟩
theorem b2968 (b : ℝ) (hb : rootInterval.Contains b) : i2968.Contains (n2968 b) := by
  exact RationalInterval.contains_point (-1708 : ℚ)

def n2969 (b : ℝ) : ℝ := (n2950 b) * (n2968 b)
def i2969 : RationalInterval := ⟨(69025063540829374214275588259963 / 250000000000000000000000000000 : ℚ), (8629994635050923375962605961307 / 31250000000000000000000000000 : ℚ)⟩
theorem b2969 (b : ℝ) (hb : rootInterval.Contains b) : i2969.Contains (n2969 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b2950 b hb) (b2968 b hb))
    (by norm_num [i2969, i2950, i2968, RationalInterval.mul]) (by norm_num [i2969, i2950, i2968, RationalInterval.mul])

