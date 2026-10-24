import BFGS.Counterexample.Certificates.IntervalTrace20

/-! Generated arithmetic proofs. Each bound is checked by the Lean kernel. -/
namespace BFGS.Counterexample.Trace
noncomputable section
open BFGS RationalInterval
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false

def n1890 (b : ℝ) : ℝ := (n1889 b) * (n1520 b)
def i1890 : RationalInterval := ⟨(-418974072807879303961740468167 / 40000000000000000000000000000 : ℚ), (-10474351342884265543414978180103 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1890 (b : ℝ) (hb : rootInterval.Contains b) : i1890.Contains (n1890 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1889 b hb) (b1520 b hb))
    (by norm_num [i1890, i1889, i1520, RationalInterval.mul]) (by norm_num [i1890, i1889, i1520, RationalInterval.mul])

def n1891 (b : ℝ) : ℝ := (n1889 b) * (n1521 b)
def i1891 : RationalInterval := ⟨(-1213356809318645426096174586191 / 200000000000000000000000000000 : ℚ), (-1516695942102423524405906268071 / 250000000000000000000000000000 : ℚ)⟩
theorem b1891 (b : ℝ) (hb : rootInterval.Contains b) : i1891.Contains (n1891 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1889 b hb) (b1521 b hb))
    (by norm_num [i1891, i1889, i1521, RationalInterval.mul]) (by norm_num [i1891, i1889, i1521, RationalInterval.mul])

def n1892 (b : ℝ) : ℝ := (n1889 b) * (n1522 b)
def i1892 : RationalInterval := ⟨(-1213356809318645426096174586191 / 200000000000000000000000000000 : ℚ), (-1516695942102423524405906268071 / 250000000000000000000000000000 : ℚ)⟩
theorem b1892 (b : ℝ) (hb : rootInterval.Contains b) : i1892.Contains (n1892 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1889 b hb) (b1522 b hb))
    (by norm_num [i1892, i1889, i1522, RationalInterval.mul]) (by norm_num [i1892, i1889, i1522, RationalInterval.mul])

def n1893 (b : ℝ) : ℝ := (n1889 b) * (n1523 b)
def i1893 : RationalInterval := ⟨(-439238022789007218962233406193 / 125000000000000000000000000000 : ℚ), (-878476005047399348991201005143 / 250000000000000000000000000000 : ℚ)⟩
theorem b1893 (b : ℝ) (hb : rootInterval.Contains b) : i1893.Contains (n1893 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1889 b hb) (b1523 b hb))
    (by norm_num [i1893, i1889, i1523, RationalInterval.mul]) (by norm_num [i1893, i1889, i1523, RationalInterval.mul])

def n1894 (b : ℝ) : ℝ := (n1880 b) + (n1890 b)
def i1894 : RationalInterval := ⟨(-10035767129192777622549677478629 / 1000000000000000000000000000000 : ℚ), (-10035766520882556641693095643041 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1894 (b : ℝ) (hb : rootInterval.Contains b) : i1894.Contains (n1894 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1880 b hb) (b1890 b hb))
    (by norm_num [i1894, i1880, i1890, RationalInterval.add]) (by norm_num [i1894, i1880, i1890, RationalInterval.add])

def n1895 (b : ℝ) : ℝ := (n1881 b) + (n1891 b)
def i1895 : RationalInterval := ⟨(-529679154614767280595569592523 / 125000000000000000000000000000 : ℚ), (-4237432870996286486527499654937 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1895 (b : ℝ) (hb : rootInterval.Contains b) : i1895.Contains (n1895 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1881 b hb) (b1891 b hb))
    (by norm_num [i1895, i1881, i1891, RationalInterval.add]) (by norm_num [i1895, i1881, i1891, RationalInterval.add])

def n1896 (b : ℝ) : ℝ := (n1882 b) + (n1892 b)
def i1896 : RationalInterval := ⟨(-529679154614767280595569592523 / 125000000000000000000000000000 : ℚ), (-4237432870996286486527499654937 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1896 (b : ℝ) (hb : rootInterval.Contains b) : i1896.Contains (n1896 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1882 b hb) (b1892 b hb))
    (by norm_num [i1896, i1882, i1892, RationalInterval.add]) (by norm_num [i1896, i1882, i1892, RationalInterval.add])

def n1897 (b : ℝ) : ℝ := (n1883 b) + (n1893 b)
def i1897 : RationalInterval := ⟨(-3154668121184270456327154793057 / 1000000000000000000000000000000 : ℚ), (-1577333948938861005104183401003 / 500000000000000000000000000000 : ℚ)⟩
theorem b1897 (b : ℝ) (hb : rootInterval.Contains b) : i1897.Contains (n1897 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1883 b hb) (b1893 b hb))
    (by norm_num [i1897, i1883, i1893, RationalInterval.add]) (by norm_num [i1897, i1883, i1893, RationalInterval.add])

def n1898 (b : ℝ) : ℝ := (n1609 b) * (n1841 b)
def i1898 : RationalInterval := ⟨(-557591923325168003267783754029 / 1000000000000000000000000000000 : ℚ), (-111518381659358215292012443789 / 200000000000000000000000000000 : ℚ)⟩
theorem b1898 (b : ℝ) (hb : rootInterval.Contains b) : i1898.Contains (n1898 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1609 b hb) (b1841 b hb))
    (by norm_num [i1898, i1609, i1841, RationalInterval.mul]) (by norm_num [i1898, i1609, i1841, RationalInterval.mul])

def n1899 (b : ℝ) : ℝ := (n1609 b) * (n1842 b)
def i1899 : RationalInterval := ⟨(3417810355800354953164882986373 / 1000000000000000000000000000000 : ℚ), (68356208549792908661952284427 / 20000000000000000000000000000 : ℚ)⟩
theorem b1899 (b : ℝ) (hb : rootInterval.Contains b) : i1899.Contains (n1899 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1609 b hb) (b1842 b hb))
    (by norm_num [i1899, i1609, i1842, RationalInterval.mul]) (by norm_num [i1899, i1609, i1842, RationalInterval.mul])

def n1900 (b : ℝ) : ℝ := (n1609 b) * (n1843 b)
def i1900 : RationalInterval := ⟨(3417810355800354953164882986373 / 1000000000000000000000000000000 : ℚ), (68356208549792908661952284427 / 20000000000000000000000000000 : ℚ)⟩
theorem b1900 (b : ℝ) (hb : rootInterval.Contains b) : i1900.Contains (n1900 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1609 b hb) (b1843 b hb))
    (by norm_num [i1900, i1609, i1843, RationalInterval.mul]) (by norm_num [i1900, i1609, i1843, RationalInterval.mul])

def n1901 (b : ℝ) : ℝ := (n1609 b) * (n1844 b)
def i1901 : RationalInterval := ⟨(103656913505121279717191702251 / 25000000000000000000000000000 : ℚ), (4146276625983782107388833020689 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1901 (b : ℝ) (hb : rootInterval.Contains b) : i1901.Contains (n1901 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1609 b hb) (b1844 b hb))
    (by norm_num [i1901, i1609, i1844, RationalInterval.mul]) (by norm_num [i1901, i1609, i1844, RationalInterval.mul])

def n1902 (b : ℝ) : ℝ := (n1894 b) + (n1898 b)
def i1902 : RationalInterval := ⟨(-5296679526258972812908730616329 / 500000000000000000000000000000 : ℚ), (-5296679214589673859076578930993 / 500000000000000000000000000000 : ℚ)⟩
theorem b1902 (b : ℝ) (hb : rootInterval.Contains b) : i1902.Contains (n1902 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1894 b hb) (b1898 b hb))
    (by norm_num [i1902, i1894, i1898, RationalInterval.add]) (by norm_num [i1902, i1894, i1898, RationalInterval.add])

def n1903 (b : ℝ) : ℝ := (n1895 b) + (n1899 b)
def i1903 : RationalInterval := ⟨(-819622881117783291599673753811 / 1000000000000000000000000000000 : ℚ), (-819622443506641053429885433587 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1903 (b : ℝ) (hb : rootInterval.Contains b) : i1903.Contains (n1903 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1895 b hb) (b1899 b hb))
    (by norm_num [i1903, i1895, i1899, RationalInterval.add]) (by norm_num [i1903, i1895, i1899, RationalInterval.add])

def n1904 (b : ℝ) : ℝ := (n1896 b) + (n1900 b)
def i1904 : RationalInterval := ⟨(-819622881117783291599673753811 / 1000000000000000000000000000000 : ℚ), (-819622443506641053429885433587 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1904 (b : ℝ) (hb : rootInterval.Contains b) : i1904.Contains (n1904 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1896 b hb) (b1900 b hb))
    (by norm_num [i1904, i1896, i1900, RationalInterval.add]) (by norm_num [i1904, i1896, i1900, RationalInterval.add])

def n1905 (b : ℝ) : ℝ := (n1897 b) + (n1901 b)
def i1905 : RationalInterval := ⟨(991608419020580732360513296983 / 1000000000000000000000000000000 : ℚ), (991608728106060097180466218683 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1905 (b : ℝ) (hb : rootInterval.Contains b) : i1905.Contains (n1905 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1897 b hb) (b1901 b hb))
    (by norm_num [i1905, i1897, i1901, RationalInterval.add]) (by norm_num [i1905, i1897, i1901, RationalInterval.add])

def n1906 (b : ℝ) : ℝ := (n225 b) * (n324 b)
def i1906 : RationalInterval := ⟨(-3830409291397728227794289233 / 1000000000000000000000000000000 : ℚ), (-1915204613406375324961220069 / 500000000000000000000000000000 : ℚ)⟩
theorem b1906 (b : ℝ) (hb : rootInterval.Contains b) : i1906.Contains (n1906 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b225 b hb) (b324 b hb))
    (by norm_num [i1906, i225, i324, RationalInterval.mul]) (by norm_num [i1906, i225, i324, RationalInterval.mul])

def n1907 (b : ℝ) : ℝ := (n227 b) * (n324 b)
def i1907 : RationalInterval := ⟨(-958762798972010959485917729 / 1000000000000000000000000000000 : ℚ), (-119845347355484550447638563 / 125000000000000000000000000000 : ℚ)⟩
theorem b1907 (b : ℝ) (hb : rootInterval.Contains b) : i1907.Contains (n1907 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b227 b hb) (b324 b hb))
    (by norm_num [i1907, i227, i324, RationalInterval.mul]) (by norm_num [i1907, i227, i324, RationalInterval.mul])

def n1908 (b : ℝ) : ℝ := (n324 b) * (n326 b)
def i1908 : RationalInterval := ⟨(-78265912309511134722036925723 / 1000000000000000000000000000000 : ℚ), (-7826591169269668271195443409 / 100000000000000000000000000000 : ℚ)⟩
theorem b1908 (b : ℝ) (hb : rootInterval.Contains b) : i1908.Contains (n1908 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b324 b hb) (b326 b hb))
    (by norm_num [i1908, i324, i326, RationalInterval.mul]) (by norm_num [i1908, i324, i326, RationalInterval.mul])

def n1909 (b : ℝ) : ℝ := (n310 b) * (n1906 b)
def i1909 : RationalInterval := ⟨(-3415789398158213769327708207 / 1000000000000000000000000000000 : ℚ), (-426973666602908286068243601 / 125000000000000000000000000000 : ℚ)⟩
theorem b1909 (b : ℝ) (hb : rootInterval.Contains b) : i1909.Contains (n1909 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b310 b hb) (b1906 b hb))
    (by norm_num [i1909, i310, i1906, RationalInterval.mul]) (by norm_num [i1909, i310, i1906, RationalInterval.mul])

def n1910 (b : ℝ) : ℝ := (n311 b) * (n1907 b)
def i1910 : RationalInterval := ⟨(-247604459225894943597782159 / 500000000000000000000000000000 : ℚ), (-495208906792612912396028287 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1910 (b : ℝ) (hb : rootInterval.Contains b) : i1910.Contains (n1910 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b311 b hb) (b1907 b hb))
    (by norm_num [i1910, i311, i1907, RationalInterval.mul]) (by norm_num [i1910, i311, i1907, RationalInterval.mul])

def n1911 (b : ℝ) : ℝ := (n1909 b) + (n1910 b)
def i1911 : RationalInterval := ⟨(-156439932664400146260930901 / 40000000000000000000000000000 : ℚ), (-782199647923175840188395419 / 200000000000000000000000000000 : ℚ)⟩
theorem b1911 (b : ℝ) (hb : rootInterval.Contains b) : i1911.Contains (n1911 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1909 b hb) (b1910 b hb))
    (by norm_num [i1911, i1909, i1910, RationalInterval.add]) (by norm_num [i1911, i1909, i1910, RationalInterval.add])

def n1912 (b : ℝ) : ℝ := (n1908 b) + (n1911 b)
def i1912 : RationalInterval := ⟨(-10272113828265142297320024781 / 125000000000000000000000000000 : ℚ), (-16435381986462512382579282237 / 200000000000000000000000000000 : ℚ)⟩
theorem b1912 (b : ℝ) (hb : rootInterval.Contains b) : i1912.Contains (n1912 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1908 b hb) (b1911 b hb))
    (by norm_num [i1912, i1908, i1911, RationalInterval.add]) (by norm_num [i1912, i1908, i1911, RationalInterval.add])

def n1913 (b : ℝ) : ℝ := (n90 b) * (n1906 b)
def i1913 : RationalInterval := ⟨(-3429157161551134984287004273 / 1000000000000000000000000000000 : ℚ), (-3429157099067201762986435537 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1913 (b : ℝ) (hb : rootInterval.Contains b) : i1913.Contains (n1913 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b90 b hb) (b1906 b hb))
    (by norm_num [i1913, i90, i1906, RationalInterval.mul]) (by norm_num [i1913, i90, i1906, RationalInterval.mul])

def n1914 (b : ℝ) : ℝ := (n91 b) * (n1907 b)
def i1914 : RationalInterval := ⟨(-504361650420525176543286127 / 1000000000000000000000000000000 : ℚ), (-504361638438040512565209489 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1914 (b : ℝ) (hb : rootInterval.Contains b) : i1914.Contains (n1914 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b91 b hb) (b1907 b hb))
    (by norm_num [i1914, i91, i1907, RationalInterval.mul]) (by norm_num [i1914, i91, i1907, RationalInterval.mul])

def n1915 (b : ℝ) : ℝ := (n1913 b) + (n1914 b)
def i1915 : RationalInterval := ⟨(-4916898514964575201037863 / 1250000000000000000000000000 : ℚ), (-1966759368752621137775822513 / 500000000000000000000000000000 : ℚ)⟩
theorem b1915 (b : ℝ) (hb : rootInterval.Contains b) : i1915.Contains (n1915 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1913 b hb) (b1914 b hb))
    (by norm_num [i1915, i1913, i1914, RationalInterval.add]) (by norm_num [i1915, i1913, i1914, RationalInterval.add])

def n1916 (b : ℝ) : ℝ := (n92 b) * (n1906 b)
def i1916 : RationalInterval := ⟨(-403000940968289720705079029 / 200000000000000000000000000000 : ℚ), (-2015004667883515197852209727 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1916 (b : ℝ) (hb : rootInterval.Contains b) : i1916.Contains (n1916 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b92 b hb) (b1906 b hb))
    (by norm_num [i1916, i92, i1906, RationalInterval.mul]) (by norm_num [i1916, i92, i1906, RationalInterval.mul])

def n1917 (b : ℝ) : ℝ := (n93 b) * (n1907 b)
def i1917 : RationalInterval := ⟨(-384753542685198353150305611 / 1000000000000000000000000000000 : ℚ), (-384753533647521931450986107 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1917 (b : ℝ) (hb : rootInterval.Contains b) : i1917.Contains (n1917 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b93 b hb) (b1907 b hb))
    (by norm_num [i1917, i93, i1907, RationalInterval.mul]) (by norm_num [i1917, i93, i1907, RationalInterval.mul])

def n1918 (b : ℝ) : ℝ := (n1916 b) + (n1917 b)
def i1918 : RationalInterval := ⟨(-599939561881661739168925189 / 250000000000000000000000000000 : ℚ), (-1199879100765518564651597917 / 500000000000000000000000000000 : ℚ)⟩
theorem b1918 (b : ℝ) (hb : rootInterval.Contains b) : i1918.Contains (n1918 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1916 b hb) (b1917 b hb))
    (by norm_num [i1918, i1916, i1917, RationalInterval.add]) (by norm_num [i1918, i1916, i1917, RationalInterval.add])

def n1919 (b : ℝ) : ℝ := (n326 b) + (n1918 b)
def i1919 : RationalInterval := ⟨(240042697281778075503470369917 / 250000000000000000000000000000 : ℚ), (240042697527530006094387284889 / 250000000000000000000000000000 : ℚ)⟩
theorem b1919 (b : ℝ) (hb : rootInterval.Contains b) : i1919.Contains (n1919 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b326 b hb) (b1918 b hb))
    (by norm_num [i1919, i326, i1918, RationalInterval.add]) (by norm_num [i1919, i326, i1918, RationalInterval.add])

def n1920 (b : ℝ) : ℝ := (n1906 b) * (n1501 b)
def i1920 : RationalInterval := ⟨(-434202904748653724053953419 / 250000000000000000000000000000 : ℚ), (-1736811579794626302197043751 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1920 (b : ℝ) (hb : rootInterval.Contains b) : i1920.Contains (n1920 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1906 b hb) (b1501 b hb))
    (by norm_num [i1920, i1906, i1501, RationalInterval.mul]) (by norm_num [i1920, i1906, i1501, RationalInterval.mul])

def n1921 (b : ℝ) : ℝ := (n1907 b) * (n1504 b)
def i1921 : RationalInterval := ⟨(-340528567735169631691352761 / 1000000000000000000000000000000 : ℚ), (-340528558905587417963132737 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1921 (b : ℝ) (hb : rootInterval.Contains b) : i1921.Contains (n1921 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1907 b hb) (b1504 b hb))
    (by norm_num [i1921, i1907, i1504, RationalInterval.mul]) (by norm_num [i1921, i1907, i1504, RationalInterval.mul])

def n1922 (b : ℝ) : ℝ := (n1920 b) + (n1921 b)
def i1922 : RationalInterval := ⟨(-2077340186729784527907166437 / 1000000000000000000000000000000 : ℚ), (-259667517337526715020022061 / 125000000000000000000000000000 : ℚ)⟩
theorem b1922 (b : ℝ) (hb : rootInterval.Contains b) : i1922.Contains (n1922 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1920 b hb) (b1921 b hb))
    (by norm_num [i1922, i1920, i1921, RationalInterval.add]) (by norm_num [i1922, i1920, i1921, RationalInterval.add])

def n1923 (b : ℝ) : ℝ := (n1922 b) * (n13 b)
def i1923 : RationalInterval := ⟨(-2077340186729784527907166437 / 500000000000000000000000000000 : ℚ), (-259667517337526715020022061 / 62500000000000000000000000000 : ℚ)⟩
theorem b1923 (b : ℝ) (hb : rootInterval.Contains b) : i1923.Contains (n1923 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1922 b hb) (b13 b hb))
    (by norm_num [i1923, i1922, i13, RationalInterval.mul]) (by norm_num [i1923, i1922, i13, RationalInterval.mul])

def n1924 (b : ℝ) : ℝ := (n326 b) * (n326 b)
def i1924 : RationalInterval := ⟨(231635514668278011304135741549 / 250000000000000000000000000000 : ℚ), (463271030238496285107995750301 / 500000000000000000000000000000 : ℚ)⟩
theorem b1924 (b : ℝ) (hb : rootInterval.Contains b) : i1924.Contains (n1924 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b326 b hb) (b326 b hb))
    (by norm_num [i1924, i326, i326, RationalInterval.mul]) (by norm_num [i1924, i326, i326, RationalInterval.mul])

def n1925 (b : ℝ) : ℝ := (n1923 b) + (n1924 b)
def i1925 : RationalInterval := ⟨(461193689149826238080364316661 / 500000000000000000000000000000 : ℚ), (461193690099796071387835573813 / 500000000000000000000000000000 : ℚ)⟩
theorem b1925 (b : ℝ) (hb : rootInterval.Contains b) : i1925.Contains (n1925 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1923 b hb) (b1924 b hb))
    (by norm_num [i1925, i1923, i1924, RationalInterval.add]) (by norm_num [i1925, i1923, i1924, RationalInterval.add])

def n1926 (b : ℝ) : ℝ := (n1838 b) + (n1840 b)
def i1926 : RationalInterval := ⟨(-41996912693038953512671704771 / 500000000000000000000000000000 : ℚ), (-41996912295846609291020274869 / 500000000000000000000000000000 : ℚ)⟩
theorem b1926 (b : ℝ) (hb : rootInterval.Contains b) : i1926.Contains (n1926 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1838 b hb) (b1840 b hb))
    (by norm_num [i1926, i1838, i1840, RationalInterval.add]) (by norm_num [i1926, i1838, i1840, RationalInterval.add])

def n1927 (b : ℝ) : ℝ := (n1915 b) * (n310 b)
def i1927 : RationalInterval := ⟨(-876934475746704395203021823 / 250000000000000000000000000000 : ℚ), (-3507737828631663814522852457 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1927 (b : ℝ) (hb : rootInterval.Contains b) : i1927.Contains (n1927 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1915 b hb) (b310 b hb))
    (by norm_num [i1927, i1915, i310, RationalInterval.mul]) (by norm_num [i1927, i1915, i310, RationalInterval.mul])

def n1928 (b : ℝ) : ℝ := (n1915 b) * (n311 b)
def i1928 : RationalInterval := ⟨(-1015847506116640894647622223 / 500000000000000000000000000000 : ℚ), (-406338993717949800460841101 / 200000000000000000000000000000 : ℚ)⟩
theorem b1928 (b : ℝ) (hb : rootInterval.Contains b) : i1928.Contains (n1928 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1915 b hb) (b311 b hb))
    (by norm_num [i1928, i1915, i311, RationalInterval.mul]) (by norm_num [i1928, i1915, i311, RationalInterval.mul])

def n1929 (b : ℝ) : ℝ := (n1919 b) * (n310 b)
def i1929 : RationalInterval := ⟨(214059448023908099598051319863 / 250000000000000000000000000000 : ℚ), (107029724364082112750680154767 / 125000000000000000000000000000 : ℚ)⟩
theorem b1929 (b : ℝ) (hb : rootInterval.Contains b) : i1929.Contains (n1929 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1919 b hb) (b310 b hb))
    (by norm_num [i1929, i1919, i310, RationalInterval.mul]) (by norm_num [i1929, i1919, i310, RationalInterval.mul])

def n1930 (b : ℝ) : ℝ := (n1919 b) * (n311 b)
def i1930 : RationalInterval := ⟨(495936155751896455105517456269 / 1000000000000000000000000000000 : ℚ), (247968078762155783372135700131 / 500000000000000000000000000000 : ℚ)⟩
theorem b1930 (b : ℝ) (hb : rootInterval.Contains b) : i1930.Contains (n1930 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1919 b hb) (b311 b hb))
    (by norm_num [i1930, i1919, i311, RationalInterval.mul]) (by norm_num [i1930, i1919, i311, RationalInterval.mul])

def n1931 (b : ℝ) : ℝ := (n1928 b) + (n1849 b)
def i1931 : RationalInterval := ⟨(-19449764198288235181073686227 / 500000000000000000000000000000 : ℚ), (-38899527887788718807712815269 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1931 (b : ℝ) (hb : rootInterval.Contains b) : i1931.Contains (n1931 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1928 b hb) (b1849 b hb))
    (by norm_num [i1931, i1928, i1849, RationalInterval.add]) (by norm_num [i1931, i1928, i1849, RationalInterval.add])

def n1932 (b : ℝ) : ℝ := (n1930 b) + (n1850 b)
def i1932 : RationalInterval := ⟨(23352856760483849854897153907 / 50000000000000000000000000000 : ℚ), (116764284331024780206159262909 / 250000000000000000000000000000 : ℚ)⟩
theorem b1932 (b : ℝ) (hb : rootInterval.Contains b) : i1932.Contains (n1932 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1930 b hb) (b1850 b hb))
    (by norm_num [i1932, i1930, i1850, RationalInterval.add]) (by norm_num [i1932, i1930, i1850, RationalInterval.add])

def n1933 (b : ℝ) : ℝ := (n310 b) * (n1915 b)
def i1933 : RationalInterval := ⟨(-876934475746704395203021823 / 250000000000000000000000000000 : ℚ), (-3507737828631663814522852457 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1933 (b : ℝ) (hb : rootInterval.Contains b) : i1933.Contains (n1933 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b310 b hb) (b1915 b hb))
    (by norm_num [i1933, i310, i1915, RationalInterval.mul]) (by norm_num [i1933, i310, i1915, RationalInterval.mul])

def n1934 (b : ℝ) : ℝ := (n310 b) * (n1919 b)
def i1934 : RationalInterval := ⟨(214059448023908099598051319863 / 250000000000000000000000000000 : ℚ), (107029724364082112750680154767 / 125000000000000000000000000000 : ℚ)⟩
theorem b1934 (b : ℝ) (hb : rootInterval.Contains b) : i1934.Contains (n1934 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b310 b hb) (b1919 b hb))
    (by norm_num [i1934, i310, i1919, RationalInterval.mul]) (by norm_num [i1934, i310, i1919, RationalInterval.mul])

def n1935 (b : ℝ) : ℝ := (n311 b) * (n1915 b)
def i1935 : RationalInterval := ⟨(-1015847506116640894647622223 / 500000000000000000000000000000 : ℚ), (-406338993717949800460841101 / 200000000000000000000000000000 : ℚ)⟩
theorem b1935 (b : ℝ) (hb : rootInterval.Contains b) : i1935.Contains (n1935 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b311 b hb) (b1915 b hb))
    (by norm_num [i1935, i311, i1915, RationalInterval.mul]) (by norm_num [i1935, i311, i1915, RationalInterval.mul])

def n1936 (b : ℝ) : ℝ := (n311 b) * (n1919 b)
def i1936 : RationalInterval := ⟨(495936155751896455105517456269 / 1000000000000000000000000000000 : ℚ), (247968078762155783372135700131 / 500000000000000000000000000000 : ℚ)⟩
theorem b1936 (b : ℝ) (hb : rootInterval.Contains b) : i1936.Contains (n1936 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b311 b hb) (b1919 b hb))
    (by norm_num [i1936, i311, i1919, RationalInterval.mul]) (by norm_num [i1936, i311, i1919, RationalInterval.mul])

def n1937 (b : ℝ) : ℝ := (n1855 b) + (n1935 b)
def i1937 : RationalInterval := ⟨(-19449764198288235181073686227 / 500000000000000000000000000000 : ℚ), (-38899527887788718807712815269 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1937 (b : ℝ) (hb : rootInterval.Contains b) : i1937.Contains (n1937 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1855 b hb) (b1935 b hb))
    (by norm_num [i1937, i1855, i1935, RationalInterval.add]) (by norm_num [i1937, i1855, i1935, RationalInterval.add])

def n1938 (b : ℝ) : ℝ := (n1856 b) + (n1936 b)
def i1938 : RationalInterval := ⟨(23352856760483849854897153907 / 50000000000000000000000000000 : ℚ), (116764284331024780206159262909 / 250000000000000000000000000000 : ℚ)⟩
theorem b1938 (b : ℝ) (hb : rootInterval.Contains b) : i1938.Contains (n1938 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1856 b hb) (b1936 b hb))
    (by norm_num [i1938, i1856, i1936, RationalInterval.add]) (by norm_num [i1938, i1856, i1936, RationalInterval.add])

def n1939 (b : ℝ) : ℝ := (n1927 b) + (n1933 b)
def i1939 : RationalInterval := ⟨(-876934475746704395203021823 / 125000000000000000000000000000 : ℚ), (-3507737828631663814522852457 / 500000000000000000000000000000 : ℚ)⟩
theorem b1939 (b : ℝ) (hb : rootInterval.Contains b) : i1939.Contains (n1939 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1927 b hb) (b1933 b hb))
    (by norm_num [i1939, i1927, i1933, RationalInterval.add]) (by norm_num [i1939, i1927, i1933, RationalInterval.add])

def n1940 (b : ℝ) : ℝ := (n1931 b) + (n1934 b)
def i1940 : RationalInterval := ⟨(408669131849527964015028953499 / 500000000000000000000000000000 : ℚ), (817338267024868183197728422867 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1940 (b : ℝ) (hb : rootInterval.Contains b) : i1940.Contains (n1940 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1931 b hb) (b1934 b hb))
    (by norm_num [i1940, i1931, i1934, RationalInterval.add]) (by norm_num [i1940, i1931, i1934, RationalInterval.add])

def n1941 (b : ℝ) : ℝ := (n1929 b) + (n1937 b)
def i1941 : RationalInterval := ⟨(408669131849527964015028953499 / 500000000000000000000000000000 : ℚ), (817338267024868183197728422867 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1941 (b : ℝ) (hb : rootInterval.Contains b) : i1941.Contains (n1941 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1929 b hb) (b1937 b hb))
    (by norm_num [i1941, i1929, i1937, RationalInterval.add]) (by norm_num [i1941, i1929, i1937, RationalInterval.add])

def n1942 (b : ℝ) : ℝ := (n1932 b) + (n1938 b)
def i1942 : RationalInterval := ⟨(23352856760483849854897153907 / 25000000000000000000000000000 : ℚ), (116764284331024780206159262909 / 125000000000000000000000000000 : ℚ)⟩
theorem b1942 (b : ℝ) (hb : rootInterval.Contains b) : i1942.Contains (n1942 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1932 b hb) (b1938 b hb))
    (by norm_num [i1942, i1932, i1938, RationalInterval.add]) (by norm_num [i1942, i1932, i1938, RationalInterval.add])

def n1943 (b : ℝ) : ℝ := (n1575 b) * (n1939 b)
def i1943 : RationalInterval := ⟨(15784820184426459708469281267 / 1000000000000000000000000000000 : ℚ), (15784820607567025105029879737 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1943 (b : ℝ) (hb : rootInterval.Contains b) : i1943.Contains (n1943 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1575 b hb) (b1939 b hb))
    (by norm_num [i1943, i1575, i1939, RationalInterval.mul]) (by norm_num [i1943, i1575, i1939, RationalInterval.mul])

def n1944 (b : ℝ) : ℝ := (n1575 b) * (n1940 b)
def i1944 : RationalInterval := ⟨(-1839011105946894976275328113141 / 1000000000000000000000000000000 : ℚ), (-1839011088148184835550456244559 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1944 (b : ℝ) (hb : rootInterval.Contains b) : i1944.Contains (n1944 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1575 b hb) (b1940 b hb))
    (by norm_num [i1944, i1575, i1940, RationalInterval.mul]) (by norm_num [i1944, i1575, i1940, RationalInterval.mul])

def n1945 (b : ℝ) : ℝ := (n1575 b) * (n1941 b)
def i1945 : RationalInterval := ⟨(-1839011105946894976275328113141 / 1000000000000000000000000000000 : ℚ), (-1839011088148184835550456244559 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1945 (b : ℝ) (hb : rootInterval.Contains b) : i1945.Contains (n1945 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1575 b hb) (b1941 b hb))
    (by norm_num [i1945, i1575, i1941, RationalInterval.mul]) (by norm_num [i1945, i1575, i1941, RationalInterval.mul])

def n1946 (b : ℝ) : ℝ := (n1575 b) * (n1942 b)
def i1946 : RationalInterval := ⟨(-525439280958473025762938976191 / 250000000000000000000000000000 : ℚ), (-1050878551264764545146593207987 / 500000000000000000000000000000 : ℚ)⟩
theorem b1946 (b : ℝ) (hb : rootInterval.Contains b) : i1946.Contains (n1946 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1575 b hb) (b1942 b hb))
    (by norm_num [i1946, i1575, i1942, RationalInterval.mul]) (by norm_num [i1946, i1575, i1942, RationalInterval.mul])

def n1947 (b : ℝ) : ℝ := (n1946 b) + (n15 b)
def i1947 : RationalInterval := ⟨(-275439280958473025762938976191 / 250000000000000000000000000000 : ℚ), (-550878551264764545146593207987 / 500000000000000000000000000000 : ℚ)⟩
theorem b1947 (b : ℝ) (hb : rootInterval.Contains b) : i1947.Contains (n1947 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1946 b hb) (b15 b hb))
    (by norm_num [i1947, i1946, i15, RationalInterval.add]) (by norm_num [i1947, i1946, i15, RationalInterval.add])

def n1948 (b : ℝ) : ℝ := (n1912 b) * (n1581 b)
def i1948 : RationalInterval := ⟨(-104005153092675794319344021433 / 250000000000000000000000000000 : ℚ), (-416020604191097868968080672301 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1948 (b : ℝ) (hb : rootInterval.Contains b) : i1948.Contains (n1948 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1912 b hb) (b1581 b hb))
    (by norm_num [i1948, i1912, i1581, RationalInterval.mul]) (by norm_num [i1948, i1912, i1581, RationalInterval.mul])

def n1949 (b : ℝ) : ℝ := (n1948 b) * (n1516 b)
def i1949 : RationalInterval := ⟨(-168216381490608468830991107381 / 500000000000000000000000000000 : ℚ), (-8410818842082914862886476031 / 25000000000000000000000000000 : ℚ)⟩
theorem b1949 (b : ℝ) (hb : rootInterval.Contains b) : i1949.Contains (n1949 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1948 b hb) (b1516 b hb))
    (by norm_num [i1949, i1948, i1516, RationalInterval.mul]) (by norm_num [i1949, i1948, i1516, RationalInterval.mul])

def n1950 (b : ℝ) : ℝ := (n1948 b) * (n1517 b)
def i1950 : RationalInterval := ⟨(-229197491634661240156831958567 / 1000000000000000000000000000000 : ℚ), (-57299371343673152655145389323 / 250000000000000000000000000000 : ℚ)⟩
theorem b1950 (b : ℝ) (hb : rootInterval.Contains b) : i1950.Contains (n1950 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1948 b hb) (b1517 b hb))
    (by norm_num [i1950, i1948, i1517, RationalInterval.mul]) (by norm_num [i1950, i1948, i1517, RationalInterval.mul])

def n1951 (b : ℝ) : ℝ := (n1948 b) * (n1518 b)
def i1951 : RationalInterval := ⟨(-229197491634661240156831958567 / 1000000000000000000000000000000 : ℚ), (-57299371343673152655145389323 / 250000000000000000000000000000 : ℚ)⟩
theorem b1951 (b : ℝ) (hb : rootInterval.Contains b) : i1951.Contains (n1951 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1948 b hb) (b1518 b hb))
    (by norm_num [i1951, i1948, i1518, RationalInterval.mul]) (by norm_num [i1951, i1948, i1518, RationalInterval.mul])

def n1952 (b : ℝ) : ℝ := (n1948 b) * (n1519 b)
def i1952 : RationalInterval := ⟨(-152638645910991396491840509637 / 1000000000000000000000000000000 : ℚ), (-30527728353467540504364129711 / 200000000000000000000000000000 : ℚ)⟩
theorem b1952 (b : ℝ) (hb : rootInterval.Contains b) : i1952.Contains (n1952 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1948 b hb) (b1519 b hb))
    (by norm_num [i1952, i1948, i1519, RationalInterval.mul]) (by norm_num [i1952, i1948, i1519, RationalInterval.mul])

def n1953 (b : ℝ) : ℝ := (n1943 b) + (n1949 b)
def i1953 : RationalInterval := ⟨(-64129588559358095590702586699 / 200000000000000000000000000000 : ℚ), (-320647933075749569410429161503 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1953 (b : ℝ) (hb : rootInterval.Contains b) : i1953.Contains (n1953 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1943 b hb) (b1949 b hb))
    (by norm_num [i1953, i1943, i1949, RationalInterval.add]) (by norm_num [i1953, i1943, i1949, RationalInterval.add])

def n1954 (b : ℝ) : ℝ := (n1944 b) + (n1950 b)
def i1954 : RationalInterval := ⟨(-517052149395389054108040017927 / 250000000000000000000000000000 : ℚ), (-2068208573522877446171037801851 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1954 (b : ℝ) (hb : rootInterval.Contains b) : i1954.Contains (n1954 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1944 b hb) (b1950 b hb))
    (by norm_num [i1954, i1944, i1950, RationalInterval.add]) (by norm_num [i1954, i1944, i1950, RationalInterval.add])

def n1955 (b : ℝ) : ℝ := (n1945 b) + (n1951 b)
def i1955 : RationalInterval := ⟨(-517052149395389054108040017927 / 250000000000000000000000000000 : ℚ), (-2068208573522877446171037801851 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1955 (b : ℝ) (hb : rootInterval.Contains b) : i1955.Contains (n1955 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1945 b hb) (b1951 b hb))
    (by norm_num [i1955, i1945, i1951, RationalInterval.add]) (by norm_num [i1955, i1945, i1951, RationalInterval.add])

def n1956 (b : ℝ) : ℝ := (n1947 b) + (n1952 b)
def i1956 : RationalInterval := ⟨(-1254395769744883499543596414401 / 1000000000000000000000000000000 : ℚ), (-1254395744296866792815007064529 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1956 (b : ℝ) (hb : rootInterval.Contains b) : i1956.Contains (n1956 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1947 b hb) (b1952 b hb))
    (by norm_num [i1956, i1947, i1952, RationalInterval.add]) (by norm_num [i1956, i1947, i1952, RationalInterval.add])

def n1957 (b : ℝ) : ℝ := (n1912 b) + (n1925 b)
def i1957 : RationalInterval := ⟨(420105233836765668891084217537 / 500000000000000000000000000000 : ℚ), (840210470267279580862774736441 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1957 (b : ℝ) (hb : rootInterval.Contains b) : i1957.Contains (n1957 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1912 b hb) (b1925 b hb))
    (by norm_num [i1957, i1912, i1925, RationalInterval.add]) (by norm_num [i1957, i1912, i1925, RationalInterval.add])

def n1958 (b : ℝ) : ℝ := (n1957 b) * (n1581 b)
def i1958 : RationalInterval := ⟨(4253565468659509844352681783373 / 1000000000000000000000000000000 : ℚ), (42535655295097230379069123481 / 10000000000000000000000000000 : ℚ)⟩
theorem b1958 (b : ℝ) (hb : rootInterval.Contains b) : i1958.Contains (n1958 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1957 b hb) (b1581 b hb))
    (by norm_num [i1958, i1957, i1581, RationalInterval.mul]) (by norm_num [i1958, i1957, i1581, RationalInterval.mul])

def n1959 (b : ℝ) : ℝ := (n1594 b) * (n1912 b)
def i1959 : RationalInterval := ⟨(-124828933340013506128865417229 / 1000000000000000000000000000000 : ℚ), (-31207232866810709616325621419 / 250000000000000000000000000000 : ℚ)⟩
theorem b1959 (b : ℝ) (hb : rootInterval.Contains b) : i1959.Contains (n1959 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1594 b hb) (b1912 b hb))
    (by norm_num [i1959, i1594, i1912, RationalInterval.mul]) (by norm_num [i1959, i1594, i1912, RationalInterval.mul])

def n1960 (b : ℝ) : ℝ := (n1959 b) * (n1597 b)
def i1960 : RationalInterval := ⟨(-710939790375325990426682963241 / 500000000000000000000000000000 : ℚ), (-1421879535491219732469782980259 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1960 (b : ℝ) (hb : rootInterval.Contains b) : i1960.Contains (n1960 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1959 b hb) (b1597 b hb))
    (by norm_num [i1960, i1959, i1597, RationalInterval.mul]) (by norm_num [i1960, i1959, i1597, RationalInterval.mul])

def n1961 (b : ℝ) : ℝ := -(n1960 b)
def i1961 : RationalInterval := ⟨(1421879535491219732469782980259 / 1000000000000000000000000000000 : ℚ), (710939790375325990426682963241 / 500000000000000000000000000000 : ℚ)⟩
theorem b1961 (b : ℝ) (hb : rootInterval.Contains b) : i1961.Contains (n1961 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b1960 b hb))
    (by norm_num [i1961, i1960, RationalInterval.neg]) (by norm_num [i1961, i1960, RationalInterval.neg])

def n1962 (b : ℝ) : ℝ := (n1958 b) + (n1961 b)
def i1962 : RationalInterval := ⟨(354715312759420598551404047727 / 62500000000000000000000000000 : ℚ), (2837722555130187509380139137291 / 500000000000000000000000000000 : ℚ)⟩
theorem b1962 (b : ℝ) (hb : rootInterval.Contains b) : i1962.Contains (n1962 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1958 b hb) (b1961 b hb))
    (by norm_num [i1962, i1958, i1961, RationalInterval.add]) (by norm_num [i1962, i1958, i1961, RationalInterval.add])

def n1963 (b : ℝ) : ℝ := (n1962 b) * (n1520 b)
def i1963 : RationalInterval := ⟨(451327426539435158656844499243 / 100000000000000000000000000000 : ℚ), (4513274370231870255682578768237 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1963 (b : ℝ) (hb : rootInterval.Contains b) : i1963.Contains (n1963 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1962 b hb) (b1520 b hb))
    (by norm_num [i1963, i1962, i1520, RationalInterval.mul]) (by norm_num [i1963, i1962, i1520, RationalInterval.mul])

def n1964 (b : ℝ) : ℝ := (n1962 b) * (n1521 b)
def i1964 : RationalInterval := ⟨(1307052730968248380383754853349 / 500000000000000000000000000000 : ℚ), (81690797606276936939703365679 / 31250000000000000000000000000 : ℚ)⟩
theorem b1964 (b : ℝ) (hb : rootInterval.Contains b) : i1964.Contains (n1964 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1962 b hb) (b1521 b hb))
    (by norm_num [i1964, i1962, i1521, RationalInterval.mul]) (by norm_num [i1964, i1962, i1521, RationalInterval.mul])

def n1965 (b : ℝ) : ℝ := (n1962 b) * (n1522 b)
def i1965 : RationalInterval := ⟨(1307052730968248380383754853349 / 500000000000000000000000000000 : ℚ), (81690797606276936939703365679 / 31250000000000000000000000000 : ℚ)⟩
theorem b1965 (b : ℝ) (hb : rootInterval.Contains b) : i1965.Contains (n1965 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1962 b hb) (b1522 b hb))
    (by norm_num [i1965, i1962, i1522, RationalInterval.mul]) (by norm_num [i1965, i1962, i1522, RationalInterval.mul])

def n1966 (b : ℝ) : ℝ := (n1962 b) * (n1523 b)
def i1966 : RationalInterval := ⟨(378524933578855831094124373471 / 250000000000000000000000000000 : ℚ), (1514099770345630432138828183627 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1966 (b : ℝ) (hb : rootInterval.Contains b) : i1966.Contains (n1966 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1962 b hb) (b1523 b hb))
    (by norm_num [i1966, i1962, i1523, RationalInterval.mul]) (by norm_num [i1966, i1962, i1523, RationalInterval.mul])

def n1967 (b : ℝ) : ℝ := (n1953 b) + (n1963 b)
def i1967 : RationalInterval := ⟨(838525264519512221722986411787 / 200000000000000000000000000000 : ℚ), (2096313218578060343136074803367 / 500000000000000000000000000000 : ℚ)⟩
theorem b1967 (b : ℝ) (hb : rootInterval.Contains b) : i1967.Contains (n1967 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1953 b hb) (b1963 b hb))
    (by norm_num [i1967, i1953, i1963, RationalInterval.add]) (by norm_num [i1967, i1953, i1963, RationalInterval.add])

def n1968 (b : ℝ) : ℝ := (n1954 b) + (n1964 b)
def i1968 : RationalInterval := ⟨(54589686435494054433534963499 / 100000000000000000000000000000 : ℚ), (545896949877984535899469899877 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1968 (b : ℝ) (hb : rootInterval.Contains b) : i1968.Contains (n1968 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1954 b hb) (b1964 b hb))
    (by norm_num [i1968, i1954, i1964, RationalInterval.add]) (by norm_num [i1968, i1954, i1964, RationalInterval.add])

def n1969 (b : ℝ) : ℝ := (n1955 b) + (n1965 b)
def i1969 : RationalInterval := ⟨(54589686435494054433534963499 / 100000000000000000000000000000 : ℚ), (545896949877984535899469899877 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1969 (b : ℝ) (hb : rootInterval.Contains b) : i1969.Contains (n1969 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1955 b hb) (b1965 b hb))
    (by norm_num [i1969, i1955, i1965, RationalInterval.add]) (by norm_num [i1969, i1955, i1965, RationalInterval.add])

def n1970 (b : ℝ) : ℝ := (n1956 b) + (n1966 b)
def i1970 : RationalInterval := ⟨(259703964570539824832901079483 / 1000000000000000000000000000000 : ℚ), (129852013024381819661910559549 / 500000000000000000000000000000 : ℚ)⟩
theorem b1970 (b : ℝ) (hb : rootInterval.Contains b) : i1970.Contains (n1970 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1956 b hb) (b1966 b hb))
    (by norm_num [i1970, i1956, i1966, RationalInterval.add]) (by norm_num [i1970, i1956, i1966, RationalInterval.add])

def n1971 (b : ℝ) : ℝ := (n1609 b) * (n1839 b)
def i1971 : RationalInterval := ⟨(-55759192332516800326778375403 / 200000000000000000000000000000 : ℚ), (-8712373567137360569688472171 / 31250000000000000000000000000 : ℚ)⟩
theorem b1971 (b : ℝ) (hb : rootInterval.Contains b) : i1971.Contains (n1971 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1609 b hb) (b1839 b hb))
    (by norm_num [i1971, i1609, i1839, RationalInterval.mul]) (by norm_num [i1971, i1609, i1839, RationalInterval.mul])

def n1972 (b : ℝ) : ℝ := (n1609 b) * (n1837 b)
def i1972 : RationalInterval := ⟨(-55759192332516800326778375403 / 200000000000000000000000000000 : ℚ), (-8712373567137360569688472171 / 31250000000000000000000000000 : ℚ)⟩
theorem b1972 (b : ℝ) (hb : rootInterval.Contains b) : i1972.Contains (n1972 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1609 b hb) (b1837 b hb))
    (by norm_num [i1972, i1609, i1837, RationalInterval.mul]) (by norm_num [i1972, i1609, i1837, RationalInterval.mul])

def n1973 (b : ℝ) : ℝ := (n1609 b) * (n1926 b)
def i1973 : RationalInterval := ⟨(-1614796716306377514025099351 / 5000000000000000000000000000 : ℚ), (-64591866893020570809783658023 / 200000000000000000000000000000 : ℚ)⟩
theorem b1973 (b : ℝ) (hb : rootInterval.Contains b) : i1973.Contains (n1973 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1609 b hb) (b1926 b hb))
    (by norm_num [i1973, i1609, i1926, RationalInterval.mul]) (by norm_num [i1973, i1609, i1926, RationalInterval.mul])

def n1974 (b : ℝ) : ℝ := (n1968 b) + (n1971 b)
def i1974 : RationalInterval := ⟨(10684036107694261708058310319 / 40000000000000000000000000000 : ℚ), (53420199145917799533887758081 / 200000000000000000000000000000 : ℚ)⟩
theorem b1974 (b : ℝ) (hb : rootInterval.Contains b) : i1974.Contains (n1974 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1968 b hb) (b1971 b hb))
    (by norm_num [i1974, i1968, i1971, RationalInterval.add]) (by norm_num [i1974, i1968, i1971, RationalInterval.add])

def n1975 (b : ℝ) : ℝ := (n1969 b) + (n1972 b)
def i1975 : RationalInterval := ⟨(10684036107694261708058310319 / 40000000000000000000000000000 : ℚ), (53420199145917799533887758081 / 200000000000000000000000000000 : ℚ)⟩
theorem b1975 (b : ℝ) (hb : rootInterval.Contains b) : i1975.Contains (n1975 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1969 b hb) (b1972 b hb))
    (by norm_num [i1975, i1969, i1972, RationalInterval.add]) (by norm_num [i1975, i1969, i1972, RationalInterval.add])

def n1976 (b : ℝ) : ℝ := (n1970 b) + (n1973 b)
def i1976 : RationalInterval := ⟨(-63255378690735677972118790717 / 1000000000000000000000000000000 : ℚ), (-63255308416339214725097171017 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1976 (b : ℝ) (hb : rootInterval.Contains b) : i1976.Contains (n1976 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1970 b hb) (b1973 b hb))
    (by norm_num [i1976, i1970, i1973, RationalInterval.add]) (by norm_num [i1976, i1970, i1973, RationalInterval.add])

def n1977 (b : ℝ) : ℝ := (n1481 b) * (n1333 b)
def i1977 : RationalInterval := ⟨(-39070768754626875349458783583 / 50000000000000000000000000000 : ℚ), (-390707608121621469371759309279 / 500000000000000000000000000000 : ℚ)⟩
theorem b1977 (b : ℝ) (hb : rootInterval.Contains b) : i1977.Contains (n1977 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1481 b hb) (b1333 b hb))
    (by norm_num [i1977, i1481, i1333, RationalInterval.mul]) (by norm_num [i1977, i1481, i1333, RationalInterval.mul])

def n1978 (b : ℝ) : ℝ := (n1624 b) * (n1350 b)
def i1978 : RationalInterval := ⟨(-98786879432794693105955362471 / 62500000000000000000000000000 : ℚ), (-1580589928868092744792187784087 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1978 (b : ℝ) (hb : rootInterval.Contains b) : i1978.Contains (n1978 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1624 b hb) (b1350 b hb))
    (by norm_num [i1978, i1624, i1350, RationalInterval.mul]) (by norm_num [i1978, i1624, i1350, RationalInterval.mul])

def n1979 (b : ℝ) : ℝ := (n1977 b) + (n1978 b)
def i1979 : RationalInterval := ⟨(-590501361504313149171115367799 / 250000000000000000000000000000 : ℚ), (-472401029022267136707141280529 / 200000000000000000000000000000 : ℚ)⟩
theorem b1979 (b : ℝ) (hb : rootInterval.Contains b) : i1979.Contains (n1979 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1977 b hb) (b1978 b hb))
    (by norm_num [i1979, i1977, i1978, RationalInterval.add]) (by norm_num [i1979, i1977, i1978, RationalInterval.add])

