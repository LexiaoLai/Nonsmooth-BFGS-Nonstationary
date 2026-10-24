import BFGS.Counterexample.Certificates.IntervalTrace18

/-! Generated arithmetic proofs. Each bound is checked by the Lean kernel. -/
namespace BFGS.Counterexample.Trace
noncomputable section
open BFGS RationalInterval
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false

def n1710 (b : ℝ) : ℝ := (n1709 b) * (n1597 b)
def i1710 : RationalInterval := ⟨(94664327556769677658307895322781 / 1000000000000000000000000000000 : ℚ), (94664330973316390232347717520523 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1710 (b : ℝ) (hb : rootInterval.Contains b) : i1710.Contains (n1710 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1709 b hb) (b1597 b hb))
    (by norm_num [i1710, i1709, i1597, RationalInterval.mul]) (by norm_num [i1710, i1709, i1597, RationalInterval.mul])

def n1711 (b : ℝ) : ℝ := -(n1710 b)
def i1711 : RationalInterval := ⟨(-94664330973316390232347717520523 / 1000000000000000000000000000000 : ℚ), (-94664327556769677658307895322781 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1711 (b : ℝ) (hb : rootInterval.Contains b) : i1711.Contains (n1711 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b1710 b hb))
    (by norm_num [i1711, i1710, RationalInterval.neg]) (by norm_num [i1711, i1710, RationalInterval.neg])

def n1712 (b : ℝ) : ℝ := (n1708 b) + (n1711 b)
def i1712 : RationalInterval := ⟨(-5565951230190913153986464145883 / 125000000000000000000000000000 : ℚ), (-11131901296563951190100177475699 / 250000000000000000000000000000 : ℚ)⟩
theorem b1712 (b : ℝ) (hb : rootInterval.Contains b) : i1712.Contains (n1712 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1708 b hb) (b1711 b hb))
    (by norm_num [i1712, i1708, i1711, RationalInterval.add]) (by norm_num [i1712, i1708, i1711, RationalInterval.add])

def n1713 (b : ℝ) : ℝ := (n1712 b) * (n1520 b)
def i1713 : RationalInterval := ⟨(-35409613935325294291225783357231 / 1000000000000000000000000000000 : ℚ), (-3540961007283000209679208431971 / 100000000000000000000000000000 : ℚ)⟩
theorem b1713 (b : ℝ) (hb : rootInterval.Contains b) : i1713.Contains (n1713 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1712 b hb) (b1520 b hb))
    (by norm_num [i1713, i1712, i1520, RationalInterval.mul]) (by norm_num [i1713, i1712, i1520, RationalInterval.mul])

def n1714 (b : ℝ) : ℝ := (n1712 b) * (n1521 b)
def i1714 : RationalInterval := ⟨(-410187636631851694961663277859 / 20000000000000000000000000000 : ℚ), (-2050937958859865454217264537907 / 100000000000000000000000000000 : ℚ)⟩
theorem b1714 (b : ℝ) (hb : rootInterval.Contains b) : i1714.Contains (n1714 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1712 b hb) (b1521 b hb))
    (by norm_num [i1714, i1712, i1521, RationalInterval.mul]) (by norm_num [i1714, i1712, i1521, RationalInterval.mul])

def n1715 (b : ℝ) : ℝ := (n1712 b) * (n1522 b)
def i1715 : RationalInterval := ⟨(-410187636631851694961663277859 / 20000000000000000000000000000 : ℚ), (-2050937958859865454217264537907 / 100000000000000000000000000000 : ℚ)⟩
theorem b1715 (b : ℝ) (hb : rootInterval.Contains b) : i1715.Contains (n1715 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1712 b hb) (b1522 b hb))
    (by norm_num [i1715, i1712, i1522, RationalInterval.mul]) (by norm_num [i1715, i1712, i1522, RationalInterval.mul])

def n1716 (b : ℝ) : ℝ := (n1712 b) * (n1523 b)
def i1716 : RationalInterval := ⟨(-11879111245955350719345112958269 / 1000000000000000000000000000000 : ℚ), (-11879109943432630694072441698087 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1716 (b : ℝ) (hb : rootInterval.Contains b) : i1716.Contains (n1716 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1712 b hb) (b1523 b hb))
    (by norm_num [i1716, i1712, i1523, RationalInterval.mul]) (by norm_num [i1716, i1712, i1523, RationalInterval.mul])

def n1717 (b : ℝ) : ℝ := (n1703 b) + (n1713 b)
def i1717 : RationalInterval := ⟨(-33814726850980306058901633791653 / 1000000000000000000000000000000 : ℚ), (-1352588874174326295669081889971 / 40000000000000000000000000000 : ℚ)⟩
theorem b1717 (b : ℝ) (hb : rootInterval.Contains b) : i1717.Contains (n1717 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1703 b hb) (b1713 b hb))
    (by norm_num [i1717, i1703, i1713, RationalInterval.add]) (by norm_num [i1717, i1703, i1713, RationalInterval.add])

def n1718 (b : ℝ) : ℝ := (n1704 b) + (n1714 b)
def i1718 : RationalInterval := ⟨(-19094933732084537368204495916071 / 1000000000000000000000000000000 : ℚ), (-19094930730162302790053114437827 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1718 (b : ℝ) (hb : rootInterval.Contains b) : i1718.Contains (n1718 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1704 b hb) (b1714 b hb))
    (by norm_num [i1718, i1704, i1714, RationalInterval.add]) (by norm_num [i1718, i1704, i1714, RationalInterval.add])

def n1719 (b : ℝ) : ℝ := (n1705 b) + (n1715 b)
def i1719 : RationalInterval := ⟨(-19094933732084537368204495916071 / 1000000000000000000000000000000 : ℚ), (-19094930730162302790053114437827 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1719 (b : ℝ) (hb : rootInterval.Contains b) : i1719.Contains (n1719 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1705 b hb) (b1715 b hb))
    (by norm_num [i1719, i1705, i1715, RationalInterval.add]) (by norm_num [i1719, i1705, i1715, RationalInterval.add])

def n1720 (b : ℝ) : ℝ := (n1706 b) + (n1716 b)
def i1720 : RationalInterval := ⟨(-10931748399440377066952722685233 / 1000000000000000000000000000000 : ℚ), (-2732936648643790548200097395597 / 250000000000000000000000000000 : ℚ)⟩
theorem b1720 (b : ℝ) (hb : rootInterval.Contains b) : i1720.Contains (n1720 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1706 b hb) (b1716 b hb))
    (by norm_num [i1720, i1706, i1716, RationalInterval.add]) (by norm_num [i1720, i1706, i1716, RationalInterval.add])

def n1721 (b : ℝ) : ℝ := (n1609 b) * (n1662 b)
def i1721 : RationalInterval := ⟨(811570176410533530660482874863 / 40000000000000000000000000000 : ℚ), (2028925502353706962602805495021 / 100000000000000000000000000000 : ℚ)⟩
theorem b1721 (b : ℝ) (hb : rootInterval.Contains b) : i1721.Contains (n1721 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1609 b hb) (b1662 b hb))
    (by norm_num [i1721, i1609, i1662, RationalInterval.mul]) (by norm_num [i1721, i1609, i1662, RationalInterval.mul])

def n1722 (b : ℝ) : ℝ := (n1609 b) * (n1663 b)
def i1722 : RationalInterval := ⟨(2607355512035395621936224321773 / 200000000000000000000000000000 : ℚ), (13036777953937607299666059551279 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1722 (b : ℝ) (hb : rootInterval.Contains b) : i1722.Contains (n1722 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1609 b hb) (b1663 b hb))
    (by norm_num [i1722, i1609, i1663, RationalInterval.mul]) (by norm_num [i1722, i1609, i1663, RationalInterval.mul])

def n1723 (b : ℝ) : ℝ := (n1609 b) * (n1664 b)
def i1723 : RationalInterval := ⟨(2607355512035395621936224321773 / 200000000000000000000000000000 : ℚ), (13036777953937607299666059551279 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1723 (b : ℝ) (hb : rootInterval.Contains b) : i1723.Contains (n1723 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1609 b hb) (b1664 b hb))
    (by norm_num [i1723, i1609, i1664, RationalInterval.mul]) (by norm_num [i1723, i1609, i1664, RationalInterval.mul])

def n1724 (b : ℝ) : ℝ := (n1609 b) * (n1665 b)
def i1724 : RationalInterval := ⟨(8295323071156315799301930378119 / 1000000000000000000000000000000 : ℚ), (2073830830493744752733828923657 / 250000000000000000000000000000 : ℚ)⟩
theorem b1724 (b : ℝ) (hb : rootInterval.Contains b) : i1724.Contains (n1724 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1609 b hb) (b1665 b hb))
    (by norm_num [i1724, i1609, i1665, RationalInterval.mul]) (by norm_num [i1724, i1609, i1665, RationalInterval.mul])

def n1725 (b : ℝ) : ℝ := (n1717 b) + (n1721 b)
def i1725 : RationalInterval := ⟨(-6762736220358483896194780960039 / 500000000000000000000000000000 : ℚ), (-2705093366164217553139798459813 / 200000000000000000000000000000 : ℚ)⟩
theorem b1725 (b : ℝ) (hb : rootInterval.Contains b) : i1725.Contains (n1725 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1717 b hb) (b1721 b hb))
    (by norm_num [i1725, i1717, i1721, RationalInterval.add]) (by norm_num [i1725, i1717, i1721, RationalInterval.add])

def n1726 (b : ℝ) : ℝ := (n1718 b) + (n1722 b)
def i1726 : RationalInterval := ⟨(-3029078085953779629261687153603 / 500000000000000000000000000000 : ℚ), (-1514538194056173872596763721637 / 250000000000000000000000000000 : ℚ)⟩
theorem b1726 (b : ℝ) (hb : rootInterval.Contains b) : i1726.Contains (n1726 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1718 b hb) (b1722 b hb))
    (by norm_num [i1726, i1718, i1722, RationalInterval.add]) (by norm_num [i1726, i1718, i1722, RationalInterval.add])

def n1727 (b : ℝ) : ℝ := (n1719 b) + (n1723 b)
def i1727 : RationalInterval := ⟨(-3029078085953779629261687153603 / 500000000000000000000000000000 : ℚ), (-1514538194056173872596763721637 / 250000000000000000000000000000 : ℚ)⟩
theorem b1727 (b : ℝ) (hb : rootInterval.Contains b) : i1727.Contains (n1727 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1719 b hb) (b1723 b hb))
    (by norm_num [i1727, i1719, i1723, RationalInterval.add]) (by norm_num [i1727, i1719, i1723, RationalInterval.add])

def n1728 (b : ℝ) : ℝ := (n1720 b) + (n1724 b)
def i1728 : RationalInterval := ⟨(-1318212664142030633825396153557 / 500000000000000000000000000000 : ℚ), (-32955290907502289773313423597 / 12500000000000000000000000000 : ℚ)⟩
theorem b1728 (b : ℝ) (hb : rootInterval.Contains b) : i1728.Contains (n1728 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1720 b hb) (b1724 b hb))
    (by norm_num [i1728, i1720, i1724, RationalInterval.add]) (by norm_num [i1728, i1720, i1724, RationalInterval.add])

def n1729 (b : ℝ) : ℝ := (n224 b) * (n56 b)
def i1729 : RationalInterval := ⟨(7858679884825133085843236049 / 40000000000000000000000000000 : ℚ), (39293399666974306635317766227 / 200000000000000000000000000000 : ℚ)⟩
theorem b1729 (b : ℝ) (hb : rootInterval.Contains b) : i1729.Contains (n1729 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b224 b hb) (b56 b hb))
    (by norm_num [i1729, i224, i56, RationalInterval.mul]) (by norm_num [i1729, i224, i56, RationalInterval.mul])

def n1730 (b : ℝ) : ℝ := (n226 b) * (n56 b)
def i1730 : RationalInterval := ⟨(49176271504343288767623647219 / 1000000000000000000000000000000 : ℚ), (6147034001438126477260932877 / 125000000000000000000000000000 : ℚ)⟩
theorem b1730 (b : ℝ) (hb : rootInterval.Contains b) : i1730.Contains (n1730 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b226 b hb) (b56 b hb))
    (by norm_num [i1730, i226, i56, RationalInterval.mul]) (by norm_num [i1730, i226, i56, RationalInterval.mul])

def n1731 (b : ℝ) : ℝ := (n56 b) * (n325 b)
def i1731 : RationalInterval := ⟨(-61726594222831618727000691267 / 1000000000000000000000000000000 : ℚ), (-61726593472857623038937652131 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1731 (b : ℝ) (hb : rootInterval.Contains b) : i1731.Contains (n1731 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b56 b hb) (b325 b hb))
    (by norm_num [i1731, i56, i325, RationalInterval.mul]) (by norm_num [i1731, i56, i325, RationalInterval.mul])

def n1732 (b : ℝ) : ℝ := (n310 b) * (n1729 b)
def i1732 : RationalInterval := ⟨(175200568210532823331280553123 / 1000000000000000000000000000000 : ℚ), (7008022787615355217455290393 / 40000000000000000000000000000 : ℚ)⟩
theorem b1732 (b : ℝ) (hb : rootInterval.Contains b) : i1732.Contains (n1732 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b310 b hb) (b1729 b hb))
    (by norm_num [i1732, i310, i1729, RationalInterval.mul]) (by norm_num [i1732, i310, i1729, RationalInterval.mul])

def n1733 (b : ℝ) : ℝ := (n311 b) * (n1730 b)
def i1733 : RationalInterval := ⟨(25399951050632195812203973667 / 1000000000000000000000000000000 : ℚ), (25399951377357668115933151679 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1733 (b : ℝ) (hb : rootInterval.Contains b) : i1733.Contains (n1733 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b311 b hb) (b1730 b hb))
    (by norm_num [i1733, i311, i1730, RationalInterval.mul]) (by norm_num [i1733, i311, i1730, RationalInterval.mul])

def n1734 (b : ℝ) : ℝ := (n1732 b) + (n1733 b)
def i1734 : RationalInterval := ⟨(20060051926116501914348452679 / 100000000000000000000000000000 : ℚ), (12537532566733846784519713219 / 62500000000000000000000000000 : ℚ)⟩
theorem b1734 (b : ℝ) (hb : rootInterval.Contains b) : i1734.Contains (n1734 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1732 b hb) (b1733 b hb))
    (by norm_num [i1734, i1732, i1733, RationalInterval.add]) (by norm_num [i1734, i1732, i1733, RationalInterval.add])

def n1735 (b : ℝ) : ℝ := (n1731 b) + (n1734 b)
def i1735 : RationalInterval := ⟨(138873925038333400416483835523 / 1000000000000000000000000000000 : ℚ), (138873927594883925513377759373 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1735 (b : ℝ) (hb : rootInterval.Contains b) : i1735.Contains (n1735 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1731 b hb) (b1734 b hb))
    (by norm_num [i1735, i1731, i1734, RationalInterval.add]) (by norm_num [i1735, i1731, i1734, RationalInterval.add])

def n1736 (b : ℝ) : ℝ := (n90 b) * (n1729 b)
def i1736 : RationalInterval := ⟨(175886219465174835803800646257 / 1000000000000000000000000000000 : ℚ), (87943110395735085318709677 / 500000000000000000000000000 : ℚ)⟩
theorem b1736 (b : ℝ) (hb : rootInterval.Contains b) : i1736.Contains (n1736 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b90 b hb) (b1729 b hb))
    (by norm_num [i1736, i90, i1729, RationalInterval.mul]) (by norm_num [i1736, i90, i1729, RationalInterval.mul])

def n1737 (b : ℝ) : ℝ := (n91 b) * (n1730 b)
def i1737 : RationalInterval := ⟨(12934703669927996508131908991 / 500000000000000000000000000000 : ℚ), (1293470383907511575905332761 / 50000000000000000000000000000 : ℚ)⟩
theorem b1737 (b : ℝ) (hb : rootInterval.Contains b) : i1737.Contains (n1737 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b91 b hb) (b1730 b hb))
    (by norm_num [i1737, i91, i1730, RationalInterval.mul]) (by norm_num [i1737, i91, i1730, RationalInterval.mul])

def n1738 (b : ℝ) : ℝ := (n1736 b) + (n1737 b)
def i1738 : RationalInterval := ⟨(201755626805030828820064464239 / 1000000000000000000000000000000 : ℚ), (10087781423481020107776300461 / 50000000000000000000000000000 : ℚ)⟩
theorem b1738 (b : ℝ) (hb : rootInterval.Contains b) : i1738.Contains (n1738 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1736 b hb) (b1737 b hb))
    (by norm_num [i1738, i1736, i1737, RationalInterval.add]) (by norm_num [i1738, i1736, i1737, RationalInterval.add])

def n1739 (b : ℝ) : ℝ := (n92 b) * (n1729 b)
def i1739 : RationalInterval := ⟨(51676190824724624821013224639 / 500000000000000000000000000000 : ℚ), (6459523902574662028257654681 / 62500000000000000000000000000 : ℚ)⟩
theorem b1739 (b : ℝ) (hb : rootInterval.Contains b) : i1739.Contains (n1739 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b92 b hb) (b1729 b hb))
    (by norm_num [i1739, i92, i1729, RationalInterval.mul]) (by norm_num [i1739, i92, i1729, RationalInterval.mul])

def n1740 (b : ℝ) : ℝ := (n93 b) * (n1730 b)
def i1740 : RationalInterval := ⟨(19734541901722122610278177001 / 1000000000000000000000000000000 : ℚ), (3946908430899574263520171717 / 200000000000000000000000000000 : ℚ)⟩
theorem b1740 (b : ℝ) (hb : rootInterval.Contains b) : i1740.Contains (n1740 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b93 b hb) (b1730 b hb))
    (by norm_num [i1740, i93, i1730, RationalInterval.mul]) (by norm_num [i1740, i93, i1730, RationalInterval.mul])

def n1741 (b : ℝ) : ℝ := (n1739 b) + (n1740 b)
def i1741 : RationalInterval := ⟨(123086923551171372252304626279 / 1000000000000000000000000000000 : ℚ), (123086924595692463769723333481 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1741 (b : ℝ) (hb : rootInterval.Contains b) : i1741.Contains (n1741 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1739 b hb) (b1740 b hb))
    (by norm_num [i1741, i1739, i1740, RationalInterval.add]) (by norm_num [i1741, i1739, i1740, RationalInterval.add])

def n1742 (b : ℝ) : ℝ := (n325 b) + (n1738 b)
def i1742 : RationalInterval := ⟨(142623729678778083579434574441 / 1000000000000000000000000000000 : ℚ), (142623732040553330317634025399 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1742 (b : ℝ) (hb : rootInterval.Contains b) : i1742.Contains (n1742 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b325 b hb) (b1738 b hb))
    (by norm_num [i1742, i325, i1738, RationalInterval.add]) (by norm_num [i1742, i325, i1738, RationalInterval.add])

def n1743 (b : ℝ) : ℝ := (n1729 b) * (n1501 b)
def i1743 : RationalInterval := ⟨(89083472663445942593881963521 / 1000000000000000000000000000000 : ℚ), (2783858553830989973211888589 / 31250000000000000000000000000 : ℚ)⟩
theorem b1743 (b : ℝ) (hb : rootInterval.Contains b) : i1743.Contains (n1743 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1729 b hb) (b1501 b hb))
    (by norm_num [i1743, i1729, i1501, RationalInterval.mul]) (by norm_num [i1743, i1729, i1501, RationalInterval.mul])

def n1744 (b : ℝ) : ℝ := (n1730 b) * (n1504 b)
def i1744 : RationalInterval := ⟨(17466181663744798644022280723 / 1000000000000000000000000000000 : ℚ), (4366545482518709156770929173 / 250000000000000000000000000000 : ℚ)⟩
theorem b1744 (b : ℝ) (hb : rootInterval.Contains b) : i1744.Contains (n1744 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1730 b hb) (b1504 b hb))
    (by norm_num [i1744, i1730, i1504, RationalInterval.mul]) (by norm_num [i1744, i1730, i1504, RationalInterval.mul])

def n1745 (b : ℝ) : ℝ := (n1743 b) + (n1744 b)
def i1745 : RationalInterval := ⟨(26637413581797685309476061061 / 250000000000000000000000000000 : ℚ), (5327482782633325788493207577 / 50000000000000000000000000000 : ℚ)⟩
theorem b1745 (b : ℝ) (hb : rootInterval.Contains b) : i1745.Contains (n1745 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1743 b hb) (b1744 b hb))
    (by norm_num [i1745, i1743, i1744, RationalInterval.add]) (by norm_num [i1745, i1743, i1744, RationalInterval.add])

def n1746 (b : ℝ) : ℝ := (n1745 b) * (n13 b)
def i1746 : RationalInterval := ⟨(26637413581797685309476061061 / 125000000000000000000000000000 : ℚ), (5327482782633325788493207577 / 25000000000000000000000000000 : ℚ)⟩
theorem b1746 (b : ℝ) (hb : rootInterval.Contains b) : i1746.Contains (n1746 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1745 b hb) (b13 b hb))
    (by norm_num [i1746, i1745, i13, RationalInterval.mul]) (by norm_num [i1746, i1745, i13, RationalInterval.mul])

def n1747 (b : ℝ) : ℝ := (n325 b) * (n325 b)
def i1747 : RationalInterval := ⟨(874145293824478780496016857 / 250000000000000000000000000000 : ℚ), (3496581257749737671012089399 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1747 (b : ℝ) (hb : rootInterval.Contains b) : i1747.Contains (n1747 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b325 b hb) (b325 b hb))
    (by norm_num [i1747, i325, i325, RationalInterval.mul]) (by norm_num [i1747, i325, i325, RationalInterval.mul])

def n1748 (b : ℝ) : ℝ := (n1746 b) + (n1747 b)
def i1748 : RationalInterval := ⟨(54148972457419849399448138979 / 250000000000000000000000000000 : ℚ), (216595892563082769210740392479 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1748 (b : ℝ) (hb : rootInterval.Contains b) : i1748.Contains (n1748 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1746 b hb) (b1747 b hb))
    (by norm_num [i1748, i1746, i1747, RationalInterval.add]) (by norm_num [i1748, i1746, i1747, RationalInterval.add])

def n1749 (b : ℝ) : ℝ := (n56 b) * (n310 b)
def i1749 : RationalInterval := ⟨(930885800169326740576944630047 / 1000000000000000000000000000000 : ℚ), (232721450653412367051471446651 / 250000000000000000000000000000 : ℚ)⟩
theorem b1749 (b : ℝ) (hb : rootInterval.Contains b) : i1749.Contains (n1749 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b56 b hb) (b310 b hb))
    (by norm_num [i1749, i56, i310, RationalInterval.mul]) (by norm_num [i1749, i56, i310, RationalInterval.mul])

def n1750 (b : ℝ) : ℝ := (n56 b) * (n311 b)
def i1750 : RationalInterval := ⟨(269586281662537047031989837787 / 500000000000000000000000000000 : ℚ), (539172564893892670092876089403 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1750 (b : ℝ) (hb : rootInterval.Contains b) : i1750.Contains (n1750 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b56 b hb) (b311 b hb))
    (by norm_num [i1750, i56, i311, RationalInterval.mul]) (by norm_num [i1750, i56, i311, RationalInterval.mul])

def n1751 (b : ℝ) : ℝ := (n310 b) * (n56 b)
def i1751 : RationalInterval := ⟨(930885800169326740576944630047 / 1000000000000000000000000000000 : ℚ), (232721450653412367051471446651 / 250000000000000000000000000000 : ℚ)⟩
theorem b1751 (b : ℝ) (hb : rootInterval.Contains b) : i1751.Contains (n1751 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b310 b hb) (b56 b hb))
    (by norm_num [i1751, i310, i56, RationalInterval.mul]) (by norm_num [i1751, i310, i56, RationalInterval.mul])

def n1752 (b : ℝ) : ℝ := (n311 b) * (n56 b)
def i1752 : RationalInterval := ⟨(269586281662537047031989837787 / 500000000000000000000000000000 : ℚ), (539172564893892670092876089403 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1752 (b : ℝ) (hb : rootInterval.Contains b) : i1752.Contains (n1752 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b311 b hb) (b56 b hb))
    (by norm_num [i1752, i311, i56, RationalInterval.mul]) (by norm_num [i1752, i311, i56, RationalInterval.mul])

def n1753 (b : ℝ) : ℝ := (n1749 b) + (n1751 b)
def i1753 : RationalInterval := ⟨(930885800169326740576944630047 / 500000000000000000000000000000 : ℚ), (232721450653412367051471446651 / 125000000000000000000000000000 : ℚ)⟩
theorem b1753 (b : ℝ) (hb : rootInterval.Contains b) : i1753.Contains (n1753 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1749 b hb) (b1751 b hb))
    (by norm_num [i1753, i1749, i1751, RationalInterval.add]) (by norm_num [i1753, i1749, i1751, RationalInterval.add])

def n1754 (b : ℝ) : ℝ := (n1742 b) * (n310 b)
def i1754 : RationalInterval := ⟨(127185526557853261056927682407 / 1000000000000000000000000000000 : ℚ), (63592764476105007307304682237 / 500000000000000000000000000000 : ℚ)⟩
theorem b1754 (b : ℝ) (hb : rootInterval.Contains b) : i1754.Contains (n1754 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1742 b hb) (b310 b hb))
    (by norm_num [i1754, i1742, i310, RationalInterval.mul]) (by norm_num [i1754, i1742, i310, RationalInterval.mul])

def n1755 (b : ℝ) : ℝ := (n1742 b) * (n311 b)
def i1755 : RationalInterval := ⟨(36833168128449993413365038539 / 500000000000000000000000000000 : ℚ), (73666337664632476783575732477 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1755 (b : ℝ) (hb : rootInterval.Contains b) : i1755.Contains (n1755 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1742 b hb) (b311 b hb))
    (by norm_num [i1755, i1742, i311, RationalInterval.mul]) (by norm_num [i1755, i1742, i311, RationalInterval.mul])

def n1756 (b : ℝ) : ℝ := (n1741 b) * (n310 b)
def i1756 : RationalInterval := ⟨(21952693593836582631186487991 / 200000000000000000000000000000 : ℚ), (109763469149388550406745692357 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1756 (b : ℝ) (hb : rootInterval.Contains b) : i1756.Contains (n1756 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1741 b hb) (b310 b hb))
    (by norm_num [i1756, i1741, i310, RationalInterval.mul]) (by norm_num [i1756, i1741, i310, RationalInterval.mul])

def n1757 (b : ℝ) : ℝ := (n1741 b) * (n311 b)
def i1757 : RationalInterval := ⟨(15893853567652712753331770587 / 250000000000000000000000000000 : ℚ), (31787707486118938938854927857 / 500000000000000000000000000000 : ℚ)⟩
theorem b1757 (b : ℝ) (hb : rootInterval.Contains b) : i1757.Contains (n1757 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1741 b hb) (b311 b hb))
    (by norm_num [i1757, i1741, i311, RationalInterval.mul]) (by norm_num [i1757, i1741, i311, RationalInterval.mul])

def n1758 (b : ℝ) : ℝ := (n1501 b) * (n56 b)
def i1758 : RationalInterval := ⟨(473323463383543916356247459839 / 1000000000000000000000000000000 : ℚ), (473323466255933310911706834179 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1758 (b : ℝ) (hb : rootInterval.Contains b) : i1758.Contains (n1758 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1501 b hb) (b56 b hb))
    (by norm_num [i1758, i1501, i56, RationalInterval.mul]) (by norm_num [i1758, i1501, i56, RationalInterval.mul])

def n1759 (b : ℝ) : ℝ := (n1504 b) * (n56 b)
def i1759 : RationalInterval := ⟨(185380001724615479571993442577 / 500000000000000000000000000000 : ℚ), (370760005412320649943942969947 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1759 (b : ℝ) (hb : rootInterval.Contains b) : i1759.Contains (n1759 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1504 b hb) (b56 b hb))
    (by norm_num [i1759, i1504, i56, RationalInterval.mul]) (by norm_num [i1759, i1504, i56, RationalInterval.mul])

def n1760 (b : ℝ) : ℝ := (n1754 b) + (n1758 b)
def i1760 : RationalInterval := ⟨(300254494970698588706587571123 / 500000000000000000000000000000 : ℚ), (600508995208143325526316198653 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1760 (b : ℝ) (hb : rootInterval.Contains b) : i1760.Contains (n1760 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1754 b hb) (b1758 b hb))
    (by norm_num [i1760, i1754, i1758, RationalInterval.add]) (by norm_num [i1760, i1754, i1758, RationalInterval.add])

def n1761 (b : ℝ) : ℝ := (n1756 b) + (n1759 b)
def i1761 : RationalInterval := ⟨(480523471418413872299919325109 / 1000000000000000000000000000000 : ℚ), (15016358580053412510959020697 / 31250000000000000000000000000 : ℚ)⟩
theorem b1761 (b : ℝ) (hb : rootInterval.Contains b) : i1761.Contains (n1761 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1756 b hb) (b1759 b hb))
    (by norm_num [i1761, i1756, i1759, RationalInterval.add]) (by norm_num [i1761, i1756, i1759, RationalInterval.add])

def n1762 (b : ℝ) : ℝ := (n56 b) * (n1501 b)
def i1762 : RationalInterval := ⟨(473323463383543916356247459839 / 1000000000000000000000000000000 : ℚ), (473323466255933310911706834179 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1762 (b : ℝ) (hb : rootInterval.Contains b) : i1762.Contains (n1762 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b56 b hb) (b1501 b hb))
    (by norm_num [i1762, i56, i1501, RationalInterval.mul]) (by norm_num [i1762, i56, i1501, RationalInterval.mul])

def n1763 (b : ℝ) : ℝ := (n56 b) * (n1504 b)
def i1763 : RationalInterval := ⟨(185380001724615479571993442577 / 500000000000000000000000000000 : ℚ), (370760005412320649943942969947 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1763 (b : ℝ) (hb : rootInterval.Contains b) : i1763.Contains (n1763 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b56 b hb) (b1504 b hb))
    (by norm_num [i1763, i56, i1504, RationalInterval.mul]) (by norm_num [i1763, i56, i1504, RationalInterval.mul])

def n1764 (b : ℝ) : ℝ := (n310 b) * (n1742 b)
def i1764 : RationalInterval := ⟨(127185526557853261056927682407 / 1000000000000000000000000000000 : ℚ), (63592764476105007307304682237 / 500000000000000000000000000000 : ℚ)⟩
theorem b1764 (b : ℝ) (hb : rootInterval.Contains b) : i1764.Contains (n1764 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b310 b hb) (b1742 b hb))
    (by norm_num [i1764, i310, i1742, RationalInterval.mul]) (by norm_num [i1764, i310, i1742, RationalInterval.mul])

def n1765 (b : ℝ) : ℝ := (n310 b) * (n1741 b)
def i1765 : RationalInterval := ⟨(21952693593836582631186487991 / 200000000000000000000000000000 : ℚ), (109763469149388550406745692357 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1765 (b : ℝ) (hb : rootInterval.Contains b) : i1765.Contains (n1765 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b310 b hb) (b1741 b hb))
    (by norm_num [i1765, i310, i1741, RationalInterval.mul]) (by norm_num [i1765, i310, i1741, RationalInterval.mul])

def n1766 (b : ℝ) : ℝ := (n311 b) * (n1742 b)
def i1766 : RationalInterval := ⟨(36833168128449993413365038539 / 500000000000000000000000000000 : ℚ), (73666337664632476783575732477 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1766 (b : ℝ) (hb : rootInterval.Contains b) : i1766.Contains (n1766 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b311 b hb) (b1742 b hb))
    (by norm_num [i1766, i311, i1742, RationalInterval.mul]) (by norm_num [i1766, i311, i1742, RationalInterval.mul])

def n1767 (b : ℝ) : ℝ := (n311 b) * (n1741 b)
def i1767 : RationalInterval := ⟨(15893853567652712753331770587 / 250000000000000000000000000000 : ℚ), (31787707486118938938854927857 / 500000000000000000000000000000 : ℚ)⟩
theorem b1767 (b : ℝ) (hb : rootInterval.Contains b) : i1767.Contains (n1767 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b311 b hb) (b1741 b hb))
    (by norm_num [i1767, i311, i1741, RationalInterval.mul]) (by norm_num [i1767, i311, i1741, RationalInterval.mul])

def n1768 (b : ℝ) : ℝ := (n1762 b) + (n1764 b)
def i1768 : RationalInterval := ⟨(300254494970698588706587571123 / 500000000000000000000000000000 : ℚ), (600508995208143325526316198653 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1768 (b : ℝ) (hb : rootInterval.Contains b) : i1768.Contains (n1768 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1762 b hb) (b1764 b hb))
    (by norm_num [i1768, i1762, i1764, RationalInterval.add]) (by norm_num [i1768, i1762, i1764, RationalInterval.add])

def n1769 (b : ℝ) : ℝ := (n1763 b) + (n1765 b)
def i1769 : RationalInterval := ⟨(480523471418413872299919325109 / 1000000000000000000000000000000 : ℚ), (15016358580053412510959020697 / 31250000000000000000000000000 : ℚ)⟩
theorem b1769 (b : ℝ) (hb : rootInterval.Contains b) : i1769.Contains (n1769 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1763 b hb) (b1765 b hb))
    (by norm_num [i1769, i1763, i1765, RationalInterval.add]) (by norm_num [i1769, i1763, i1765, RationalInterval.add])

def n1770 (b : ℝ) : ℝ := (n1760 b) + (n1768 b)
def i1770 : RationalInterval := ⟨(300254494970698588706587571123 / 250000000000000000000000000000 : ℚ), (600508995208143325526316198653 / 500000000000000000000000000000 : ℚ)⟩
theorem b1770 (b : ℝ) (hb : rootInterval.Contains b) : i1770.Contains (n1770 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1760 b hb) (b1768 b hb))
    (by norm_num [i1770, i1760, i1768, RationalInterval.add]) (by norm_num [i1770, i1760, i1768, RationalInterval.add])

def n1771 (b : ℝ) : ℝ := (n1755 b) + (n1769 b)
def i1771 : RationalInterval := ⟨(554189807675313859126649402187 / 1000000000000000000000000000000 : ℚ), (554189812226341677134264394781 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1771 (b : ℝ) (hb : rootInterval.Contains b) : i1771.Contains (n1771 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1755 b hb) (b1769 b hb))
    (by norm_num [i1771, i1755, i1769, RationalInterval.add]) (by norm_num [i1771, i1755, i1769, RationalInterval.add])

def n1772 (b : ℝ) : ℝ := (n1761 b) + (n1766 b)
def i1772 : RationalInterval := ⟨(554189807675313859126649402187 / 1000000000000000000000000000000 : ℚ), (554189812226341677134264394781 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1772 (b : ℝ) (hb : rootInterval.Contains b) : i1772.Contains (n1772 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1761 b hb) (b1766 b hb))
    (by norm_num [i1772, i1761, i1766, RationalInterval.add]) (by norm_num [i1772, i1761, i1766, RationalInterval.add])

def n1773 (b : ℝ) : ℝ := (n1757 b) + (n1767 b)
def i1773 : RationalInterval := ⟨(15893853567652712753331770587 / 125000000000000000000000000000 : ℚ), (31787707486118938938854927857 / 250000000000000000000000000000 : ℚ)⟩
theorem b1773 (b : ℝ) (hb : rootInterval.Contains b) : i1773.Contains (n1773 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1757 b hb) (b1767 b hb))
    (by norm_num [i1773, i1757, i1767, RationalInterval.add]) (by norm_num [i1773, i1757, i1767, RationalInterval.add])

def n1774 (b : ℝ) : ℝ := (n1575 b) * (n1770 b)
def i1774 : RationalInterval := ⟨(-2702290485990877472070475320723 / 1000000000000000000000000000000 : ℚ), (-2702290447132462529121304343309 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1774 (b : ℝ) (hb : rootInterval.Contains b) : i1774.Contains (n1774 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1575 b hb) (b1770 b hb))
    (by norm_num [i1774, i1575, i1770, RationalInterval.mul]) (by norm_num [i1774, i1575, i1770, RationalInterval.mul])

def n1775 (b : ℝ) : ℝ := (n1575 b) * (n1771 b)
def i1775 : RationalInterval := ⟨(-1246927080995043947685290063789 / 1000000000000000000000000000000 : ℚ), (-77932941485049842560180629141 / 62500000000000000000000000000 : ℚ)⟩
theorem b1775 (b : ℝ) (hb : rootInterval.Contains b) : i1775.Contains (n1775 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1575 b hb) (b1771 b hb))
    (by norm_num [i1775, i1575, i1771, RationalInterval.mul]) (by norm_num [i1775, i1575, i1771, RationalInterval.mul])

def n1776 (b : ℝ) : ℝ := (n1575 b) * (n1772 b)
def i1776 : RationalInterval := ⟨(-1246927080995043947685290063789 / 1000000000000000000000000000000 : ℚ), (-77932941485049842560180629141 / 62500000000000000000000000000 : ℚ)⟩
theorem b1776 (b : ℝ) (hb : rootInterval.Contains b) : i1776.Contains (n1776 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1575 b hb) (b1772 b hb))
    (by norm_num [i1776, i1575, i1772, RationalInterval.mul]) (by norm_num [i1776, i1575, i1772, RationalInterval.mul])

def n1777 (b : ℝ) : ℝ := (n1575 b) * (n1773 b)
def i1777 : RationalInterval := ⟨(-17880585510926943997048064309 / 62500000000000000000000000000 : ℚ), (-143044681706368942053746907801 / 500000000000000000000000000000 : ℚ)⟩
theorem b1777 (b : ℝ) (hb : rootInterval.Contains b) : i1777.Contains (n1777 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1575 b hb) (b1773 b hb))
    (by norm_num [i1777, i1575, i1773, RationalInterval.mul]) (by norm_num [i1777, i1575, i1773, RationalInterval.mul])

def n1778 (b : ℝ) : ℝ := (n1774 b) + (n15 b)
def i1778 : RationalInterval := ⟨(-1702290485990877472070475320723 / 1000000000000000000000000000000 : ℚ), (-1702290447132462529121304343309 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1778 (b : ℝ) (hb : rootInterval.Contains b) : i1778.Contains (n1778 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1774 b hb) (b15 b hb))
    (by norm_num [i1778, i1774, i15, RationalInterval.add]) (by norm_num [i1778, i1774, i15, RationalInterval.add])

def n1779 (b : ℝ) : ℝ := (n1735 b) * (n1581 b)
def i1779 : RationalInterval := ⟨(140609848310004105859663258567 / 200000000000000000000000000000 : ℚ), (351524631189918801181369561297 / 500000000000000000000000000000 : ℚ)⟩
theorem b1779 (b : ℝ) (hb : rootInterval.Contains b) : i1779.Contains (n1779 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1735 b hb) (b1581 b hb))
    (by norm_num [i1779, i1735, i1581, RationalInterval.mul]) (by norm_num [i1779, i1735, i1581, RationalInterval.mul])

def n1780 (b : ℝ) : ℝ := (n1779 b) * (n1516 b)
def i1780 : RationalInterval := ⟨(284275333873838357275239438133 / 500000000000000000000000000000 : ℚ), (113710137825378592073045072203 / 200000000000000000000000000000 : ℚ)⟩
theorem b1780 (b : ℝ) (hb : rootInterval.Contains b) : i1780.Contains (n1780 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1779 b hb) (b1516 b hb))
    (by norm_num [i1780, i1779, i1516, RationalInterval.mul]) (by norm_num [i1780, i1779, i1516, RationalInterval.mul])

def n1781 (b : ℝ) : ℝ := (n1779 b) * (n1517 b)
def i1781 : RationalInterval := ⟨(387329657797025097659808482647 / 1000000000000000000000000000000 : ℚ), (193664836118111912265727233581 / 500000000000000000000000000000 : ℚ)⟩
theorem b1781 (b : ℝ) (hb : rootInterval.Contains b) : i1781.Contains (n1781 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1779 b hb) (b1517 b hb))
    (by norm_num [i1781, i1779, i1517, RationalInterval.mul]) (by norm_num [i1781, i1779, i1517, RationalInterval.mul])

def n1782 (b : ℝ) : ℝ := (n1779 b) * (n1518 b)
def i1782 : RationalInterval := ⟨(387329657797025097659808482647 / 1000000000000000000000000000000 : ℚ), (193664836118111912265727233581 / 500000000000000000000000000000 : ℚ)⟩
theorem b1782 (b : ℝ) (hb : rootInterval.Contains b) : i1782.Contains (n1782 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1779 b hb) (b1518 b hb))
    (by norm_num [i1782, i1779, i1518, RationalInterval.mul]) (by norm_num [i1782, i1779, i1518, RationalInterval.mul])

def n1783 (b : ℝ) : ℝ := (n1779 b) * (n1519 b)
def i1783 : RationalInterval := ⟨(16121869963389237715548021753 / 62500000000000000000000000000 : ℚ), (64487482246887359771314547973 / 250000000000000000000000000000 : ℚ)⟩
theorem b1783 (b : ℝ) (hb : rootInterval.Contains b) : i1783.Contains (n1783 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1779 b hb) (b1519 b hb))
    (by norm_num [i1783, i1779, i1519, RationalInterval.mul]) (by norm_num [i1783, i1779, i1519, RationalInterval.mul])

def n1784 (b : ℝ) : ℝ := (n1778 b) + (n1780 b)
def i1784 : RationalInterval := ⟨(-1133739818243200757519996444457 / 1000000000000000000000000000000 : ℚ), (-566869879002784784378039491147 / 500000000000000000000000000000 : ℚ)⟩
theorem b1784 (b : ℝ) (hb : rootInterval.Contains b) : i1784.Contains (n1784 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1778 b hb) (b1780 b hb))
    (by norm_num [i1784, i1778, i1780, RationalInterval.add]) (by norm_num [i1784, i1778, i1780, RationalInterval.add])

def n1785 (b : ℝ) : ℝ := (n1775 b) + (n1781 b)
def i1785 : RationalInterval := ⟨(-429798711599009425012740790571 / 500000000000000000000000000000 : ℚ), (-429798695762286828215717799547 / 500000000000000000000000000000 : ℚ)⟩
theorem b1785 (b : ℝ) (hb : rootInterval.Contains b) : i1785.Contains (n1785 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1775 b hb) (b1781 b hb))
    (by norm_num [i1785, i1775, i1781, RationalInterval.add]) (by norm_num [i1785, i1775, i1781, RationalInterval.add])

def n1786 (b : ℝ) : ℝ := (n1776 b) + (n1782 b)
def i1786 : RationalInterval := ⟨(-429798711599009425012740790571 / 500000000000000000000000000000 : ℚ), (-429798695762286828215717799547 / 500000000000000000000000000000 : ℚ)⟩
theorem b1786 (b : ℝ) (hb : rootInterval.Contains b) : i1786.Contains (n1786 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1776 b hb) (b1782 b hb))
    (by norm_num [i1786, i1776, i1782, RationalInterval.add]) (by norm_num [i1786, i1776, i1782, RationalInterval.add])

def n1787 (b : ℝ) : ℝ := (n1777 b) + (n1783 b)
def i1787 : RationalInterval := ⟨(-439678886884426570375010639 / 15625000000000000000000000000 : ℚ), (-2813943442518844502223562371 / 100000000000000000000000000000 : ℚ)⟩
theorem b1787 (b : ℝ) (hb : rootInterval.Contains b) : i1787.Contains (n1787 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1777 b hb) (b1783 b hb))
    (by norm_num [i1787, i1777, i1783, RationalInterval.add]) (by norm_num [i1787, i1777, i1783, RationalInterval.add])

def n1788 (b : ℝ) : ℝ := (n1735 b) + (n1748 b)
def i1788 : RationalInterval := ⟨(355469814868012798014276391439 / 1000000000000000000000000000000 : ℚ), (88867455039491673681029537963 / 250000000000000000000000000000 : ℚ)⟩
theorem b1788 (b : ℝ) (hb : rootInterval.Contains b) : i1788.Contains (n1788 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1735 b hb) (b1748 b hb))
    (by norm_num [i1788, i1735, i1748, RationalInterval.add]) (by norm_num [i1788, i1735, i1748, RationalInterval.add])

def n1789 (b : ℝ) : ℝ := (n1788 b) * (n1581 b)
def i1789 : RationalInterval := ⟨(449891481910479464135084055757 / 250000000000000000000000000000 : ℚ), (89978298730552618833395691097 / 50000000000000000000000000000 : ℚ)⟩
theorem b1789 (b : ℝ) (hb : rootInterval.Contains b) : i1789.Contains (n1789 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1788 b hb) (b1581 b hb))
    (by norm_num [i1789, i1788, i1581, RationalInterval.mul]) (by norm_num [i1789, i1788, i1581, RationalInterval.mul])

def n1790 (b : ℝ) : ℝ := (n1594 b) * (n1735 b)
def i1790 : RationalInterval := ⟨(210953218920935604226287035337 / 1000000000000000000000000000000 : ℚ), (210953224188222151925058102053 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1790 (b : ℝ) (hb : rootInterval.Contains b) : i1790.Contains (n1790 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1594 b hb) (b1735 b hb))
    (by norm_num [i1790, i1594, i1735, RationalInterval.mul]) (by norm_num [i1790, i1594, i1735, RationalInterval.mul])

def n1791 (b : ℝ) : ℝ := (n1790 b) * (n1597 b)
def i1791 : RationalInterval := ⟨(150180561811700942314401887067 / 62500000000000000000000000000 : ℚ), (480577817884148486308775068859 / 200000000000000000000000000000 : ℚ)⟩
theorem b1791 (b : ℝ) (hb : rootInterval.Contains b) : i1791.Contains (n1791 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1790 b hb) (b1597 b hb))
    (by norm_num [i1791, i1790, i1597, RationalInterval.mul]) (by norm_num [i1791, i1790, i1597, RationalInterval.mul])

def n1792 (b : ℝ) : ℝ := -(n1791 b)
def i1792 : RationalInterval := ⟨(-480577817884148486308775068859 / 200000000000000000000000000000 : ℚ), (-150180561811700942314401887067 / 62500000000000000000000000000 : ℚ)⟩
theorem b1792 (b : ℝ) (hb : rootInterval.Contains b) : i1792.Contains (n1792 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b1791 b hb))
    (by norm_num [i1792, i1791, RationalInterval.neg]) (by norm_num [i1792, i1791, RationalInterval.neg])

def n1793 (b : ℝ) : ℝ := (n1789 b) + (n1792 b)
def i1793 : RationalInterval := ⟨(-603323161778824575003539121267 / 1000000000000000000000000000000 : ℚ), (-150830753594040675090629092783 / 250000000000000000000000000000 : ℚ)⟩
theorem b1793 (b : ℝ) (hb : rootInterval.Contains b) : i1793.Contains (n1793 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1789 b hb) (b1792 b hb))
    (by norm_num [i1793, i1789, i1792, RationalInterval.add]) (by norm_num [i1793, i1789, i1792, RationalInterval.add])

def n1794 (b : ℝ) : ℝ := (n1793 b) * (n1520 b)
def i1794 : RationalInterval := ⟨(-239889815699292581859212770733 / 500000000000000000000000000000 : ℚ), (-5997243900065647984646799059 / 12500000000000000000000000000 : ℚ)⟩
theorem b1794 (b : ℝ) (hb : rootInterval.Contains b) : i1794.Contains (n1794 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1793 b hb) (b1520 b hb))
    (by norm_num [i1794, i1793, i1520, RationalInterval.mul]) (by norm_num [i1794, i1793, i1520, RationalInterval.mul])

def n1795 (b : ℝ) : ℝ := (n1793 b) * (n1521 b)
def i1795 : RationalInterval := ⟨(-277890170543705863813027030103 / 1000000000000000000000000000000 : ℚ), (-277890101311751203523432938227 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1795 (b : ℝ) (hb : rootInterval.Contains b) : i1795.Contains (n1795 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1793 b hb) (b1521 b hb))
    (by norm_num [i1795, i1793, i1521, RationalInterval.mul]) (by norm_num [i1795, i1793, i1521, RationalInterval.mul])

def n1796 (b : ℝ) : ℝ := (n1793 b) * (n1522 b)
def i1796 : RationalInterval := ⟨(-277890170543705863813027030103 / 1000000000000000000000000000000 : ℚ), (-277890101311751203523432938227 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1796 (b : ℝ) (hb : rootInterval.Contains b) : i1796.Contains (n1796 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1793 b hb) (b1522 b hb))
    (by norm_num [i1796, i1793, i1522, RationalInterval.mul]) (by norm_num [i1796, i1793, i1522, RationalInterval.mul])

def n1797 (b : ℝ) : ℝ := (n1793 b) * (n1523 b)
def i1797 : RationalInterval := ⟨(-3219100680022643210835597717 / 20000000000000000000000000000 : ℚ), (-160954993856032014739192466629 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1797 (b : ℝ) (hb : rootInterval.Contains b) : i1797.Contains (n1797 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1793 b hb) (b1523 b hb))
    (by norm_num [i1797, i1793, i1523, RationalInterval.mul]) (by norm_num [i1797, i1793, i1523, RationalInterval.mul])

def n1798 (b : ℝ) : ℝ := (n1784 b) + (n1794 b)
def i1798 : RationalInterval := ⟨(-1613519449641785921238421985923 / 1000000000000000000000000000000 : ℚ), (-806759635005410703763911453507 / 500000000000000000000000000000 : ℚ)⟩
theorem b1798 (b : ℝ) (hb : rootInterval.Contains b) : i1798.Contains (n1798 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1784 b hb) (b1794 b hb))
    (by norm_num [i1798, i1784, i1794, RationalInterval.add]) (by norm_num [i1798, i1784, i1794, RationalInterval.add])

def n1799 (b : ℝ) : ℝ := (n1785 b) + (n1795 b)
def i1799 : RationalInterval := ⟨(-227497518748344942767701722249 / 200000000000000000000000000000 : ℚ), (-1137487492836324859954868537321 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1799 (b : ℝ) (hb : rootInterval.Contains b) : i1799.Contains (n1799 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1785 b hb) (b1795 b hb))
    (by norm_num [i1799, i1785, i1795, RationalInterval.add]) (by norm_num [i1799, i1785, i1795, RationalInterval.add])

