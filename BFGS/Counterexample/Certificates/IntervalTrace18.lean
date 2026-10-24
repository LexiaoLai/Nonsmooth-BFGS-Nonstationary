import BFGS.Counterexample.Certificates.IntervalTrace17

/-! Generated arithmetic proofs. Each bound is checked by the Lean kernel. -/
namespace BFGS.Counterexample.Trace
noncomputable section
open BFGS RationalInterval
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false

def n1620 (b : ℝ) : ℝ := (n1618 b) + (n1619 b)
def i1620 : RationalInterval := ⟨(-295862354500740236678169837221 / 100000000000000000000000000000 : ℚ), (-2958623514883275966853833901707 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1620 (b : ℝ) (hb : rootInterval.Contains b) : i1620.Contains (n1620 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1618 b hb) (b1619 b hb))
    (by norm_num [i1620, i1618, i1619, RationalInterval.add]) (by norm_num [i1620, i1618, i1619, RationalInterval.add])

def n1621 (b : ℝ) : ℝ := (n92 b) * (n211 b)
def i1621 : RationalInterval := ⟨(-8830007141058978831346073303 / 15625000000000000000000000000 : ℚ), (-113024090085613186176671939581 / 200000000000000000000000000000 : ℚ)⟩
theorem b1621 (b : ℝ) (hb : rootInterval.Contains b) : i1621.Contains (n1621 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b92 b hb) (b211 b hb))
    (by norm_num [i1621, i92, i211, RationalInterval.mul]) (by norm_num [i1621, i92, i211, RationalInterval.mul])

def n1622 (b : ℝ) : ℝ := (n93 b) * (n213 b)
def i1622 : RationalInterval := ⟨(-1523336587821766350853627859773 / 1000000000000000000000000000000 : ℚ), (-380834143432493343348824212773 / 250000000000000000000000000000 : ℚ)⟩
theorem b1622 (b : ℝ) (hb : rootInterval.Contains b) : i1622.Contains (n1622 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b93 b hb) (b213 b hb))
    (by norm_num [i1622, i93, i213, RationalInterval.mul]) (by norm_num [i1622, i93, i213, RationalInterval.mul])

def n1623 (b : ℝ) : ℝ := (n1621 b) + (n1622 b)
def i1623 : RationalInterval := ⟨(-417691408969908199211955310233 / 200000000000000000000000000000 : ℚ), (-2088457024158039304278656548997 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1623 (b : ℝ) (hb : rootInterval.Contains b) : i1623.Contains (n1623 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1621 b hb) (b1622 b hb))
    (by norm_num [i1623, i1621, i1622, RationalInterval.add]) (by norm_num [i1623, i1621, i1622, RationalInterval.add])

def n1624 (b : ℝ) : ℝ := -(n1620 b)
def i1624 : RationalInterval := ⟨(2958623514883275966853833901707 / 1000000000000000000000000000000 : ℚ), (295862354500740236678169837221 / 100000000000000000000000000000 : ℚ)⟩
theorem b1624 (b : ℝ) (hb : rootInterval.Contains b) : i1624.Contains (n1624 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b1620 b hb))
    (by norm_num [i1624, i1620, RationalInterval.neg]) (by norm_num [i1624, i1620, RationalInterval.neg])

def n1625 (b : ℝ) : ℝ := -(n1623 b)
def i1625 : RationalInterval := ⟨(2088457024158039304278656548997 / 1000000000000000000000000000000 : ℚ), (417691408969908199211955310233 / 200000000000000000000000000000 : ℚ)⟩
theorem b1625 (b : ℝ) (hb : rootInterval.Contains b) : i1625.Contains (n1625 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b1623 b hb))
    (by norm_num [i1625, i1623, RationalInterval.neg]) (by norm_num [i1625, i1623, RationalInterval.neg])

def n1626 (b : ℝ) : ℝ := (n1625 b) + (n15 b)
def i1626 : RationalInterval := ⟨(3088457024158039304278656548997 / 1000000000000000000000000000000 : ℚ), (617691408969908199211955310233 / 200000000000000000000000000000 : ℚ)⟩
theorem b1626 (b : ℝ) (hb : rootInterval.Contains b) : i1626.Contains (n1626 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1625 b hb) (b15 b hb))
    (by norm_num [i1626, i1625, i15, RationalInterval.add]) (by norm_num [i1626, i1625, i15, RationalInterval.add])

def n1627 (b : ℝ) : ℝ := (n224 b) * (n1624 b)
def i1627 : RationalInterval := ⟨(139209482203484630805559871659 / 250000000000000000000000000000 : ℚ), (556837937724800214820625610729 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1627 (b : ℝ) (hb : rootInterval.Contains b) : i1627.Contains (n1627 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b224 b hb) (b1624 b hb))
    (by norm_num [i1627, i224, i1624, RationalInterval.mul]) (by norm_num [i1627, i224, i1624, RationalInterval.mul])

def n1628 (b : ℝ) : ℝ := (n225 b) * (n1626 b)
def i1628 : RationalInterval := ⟨(145494527302753114563229668657 / 1000000000000000000000000000000 : ℚ), (18186816215712433425267316217 / 125000000000000000000000000000 : ℚ)⟩
theorem b1628 (b : ℝ) (hb : rootInterval.Contains b) : i1628.Contains (n1628 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b225 b hb) (b1626 b hb))
    (by norm_num [i1628, i225, i1626, RationalInterval.mul]) (by norm_num [i1628, i225, i1626, RationalInterval.mul])

def n1629 (b : ℝ) : ℝ := (n1627 b) + (n1628 b)
def i1629 : RationalInterval := ⟨(702332456116691637785469155293 / 1000000000000000000000000000000 : ℚ), (140466493490099936444552828093 / 200000000000000000000000000000 : ℚ)⟩
theorem b1629 (b : ℝ) (hb : rootInterval.Contains b) : i1629.Contains (n1629 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1627 b hb) (b1628 b hb))
    (by norm_num [i1629, i1627, i1628, RationalInterval.add]) (by norm_num [i1629, i1627, i1628, RationalInterval.add])

def n1630 (b : ℝ) : ℝ := (n226 b) * (n1624 b)
def i1630 : RationalInterval := ⟨(5575127338961151752272910667 / 40000000000000000000000000000 : ℚ), (6968909314022927309362013351 / 50000000000000000000000000000 : ℚ)⟩
theorem b1630 (b : ℝ) (hb : rootInterval.Contains b) : i1630.Contains (n1630 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b226 b hb) (b1624 b hb))
    (by norm_num [i1630, i226, i1624, RationalInterval.mul]) (by norm_num [i1630, i226, i1624, RationalInterval.mul])

def n1631 (b : ℝ) : ℝ := (n227 b) * (n1626 b)
def i1631 : RationalInterval := ⟨(36417711279229595061781891973 / 1000000000000000000000000000000 : ℚ), (36417712036205406970367259571 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1631 (b : ℝ) (hb : rootInterval.Contains b) : i1631.Contains (n1631 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b227 b hb) (b1626 b hb))
    (by norm_num [i1631, i227, i1626, RationalInterval.mul]) (by norm_num [i1631, i227, i1626, RationalInterval.mul])

def n1632 (b : ℝ) : ℝ := (n1630 b) + (n1631 b)
def i1632 : RationalInterval := ⟨(21974486844157298608575582331 / 125000000000000000000000000000 : ℚ), (175795898316663953157607526591 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1632 (b : ℝ) (hb : rootInterval.Contains b) : i1632.Contains (n1632 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1630 b hb) (b1631 b hb))
    (by norm_num [i1632, i1630, i1631, RationalInterval.add]) (by norm_num [i1632, i1630, i1631, RationalInterval.add])

def n1633 (b : ℝ) : ℝ := -(n211 b)
def i1633 : RationalInterval := ⟨(1074261822854187343377343754867 / 1000000000000000000000000000000 : ℚ), (134282729226210685066719959941 / 125000000000000000000000000000 : ℚ)⟩
theorem b1633 (b : ℝ) (hb : rootInterval.Contains b) : i1633.Contains (n1633 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b211 b hb))
    (by norm_num [i1633, i211, RationalInterval.neg]) (by norm_num [i1633, i211, RationalInterval.neg])

def n1634 (b : ℝ) : ℝ := -(n213 b)
def i1634 : RationalInterval := ⟨(3795984386934468359098160162079 / 1000000000000000000000000000000 : ℚ), (759196882515232061002779665111 / 200000000000000000000000000000 : ℚ)⟩
theorem b1634 (b : ℝ) (hb : rootInterval.Contains b) : i1634.Contains (n1634 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_neg (b213 b hb))
    (by norm_num [i1634, i213, RationalInterval.neg]) (by norm_num [i1634, i213, RationalInterval.neg])

def n1635 (b : ℝ) : ℝ := (n1629 b) + (n1633 b)
def i1635 : RationalInterval := ⟨(22207428487135987264535161377 / 12500000000000000000000000000 : ℚ), (1776594301260185162756523819993 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1635 (b : ℝ) (hb : rootInterval.Contains b) : i1635.Contains (n1635 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1629 b hb) (b1633 b hb))
    (by norm_num [i1635, i1629, i1633, RationalInterval.add]) (by norm_num [i1635, i1629, i1633, RationalInterval.add])

def n1636 (b : ℝ) : ℝ := (n1632 b) + (n1634 b)
def i1636 : RationalInterval := ⟨(3971780281687726747966764820727 / 1000000000000000000000000000000 : ℚ), (1985890155446412129085752926073 / 500000000000000000000000000000 : ℚ)⟩
theorem b1636 (b : ℝ) (hb : rootInterval.Contains b) : i1636.Contains (n1636 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1632 b hb) (b1634 b hb))
    (by norm_num [i1636, i1632, i1634, RationalInterval.add]) (by norm_num [i1636, i1632, i1634, RationalInterval.add])

def n1637 (b : ℝ) : ℝ := (n1624 b) * (n325 b)
def i1637 : RationalInterval := ⟨(-87474511549343462840420230673 / 500000000000000000000000000000 : ℚ), (-43737254813670063703249851431 / 250000000000000000000000000000 : ℚ)⟩
theorem b1637 (b : ℝ) (hb : rootInterval.Contains b) : i1637.Contains (n1637 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1624 b hb) (b325 b hb))
    (by norm_num [i1637, i1624, i325, RationalInterval.mul]) (by norm_num [i1637, i1624, i325, RationalInterval.mul])

def n1638 (b : ℝ) : ℝ := (n1625 b) * (n326 b)
def i1638 : RationalInterval := ⟨(1005143610456106726033875633147 / 500000000000000000000000000000 : ℚ), (1005143621393076554532274161471 / 500000000000000000000000000000 : ℚ)⟩
theorem b1638 (b : ℝ) (hb : rootInterval.Contains b) : i1638.Contains (n1638 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1625 b hb) (b326 b hb))
    (by norm_num [i1638, i1625, i326, RationalInterval.mul]) (by norm_num [i1638, i1625, i326, RationalInterval.mul])

def n1639 (b : ℝ) : ℝ := (n1637 b) + (n1638 b)
def i1639 : RationalInterval := ⟨(458834549453381631596727701237 / 250000000000000000000000000000 : ℚ), (917669111765736427125774458609 / 500000000000000000000000000000 : ℚ)⟩
theorem b1639 (b : ℝ) (hb : rootInterval.Contains b) : i1639.Contains (n1639 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1637 b hb) (b1638 b hb))
    (by norm_num [i1639, i1637, i1638, RationalInterval.add]) (by norm_num [i1639, i1637, i1638, RationalInterval.add])

def n1640 (b : ℝ) : ℝ := (n310 b) * (n1635 b)
def i1640 : RationalInterval := ⟨(316857621602644884156152856629 / 200000000000000000000000000000 : ℚ), (99018008217511462676809267267 / 62500000000000000000000000000 : ℚ)⟩
theorem b1640 (b : ℝ) (hb : rootInterval.Contains b) : i1640.Contains (n1640 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b310 b hb) (b1635 b hb))
    (by norm_num [i1640, i310, i1635, RationalInterval.mul]) (by norm_num [i1640, i310, i1635, RationalInterval.mul])

def n1641 (b : ℝ) : ℝ := (n311 b) * (n1636 b)
def i1641 : RationalInterval := ⟨(256432171585599830095822252791 / 125000000000000000000000000000 : ℚ), (82058295720035237519169192107 / 40000000000000000000000000000 : ℚ)⟩
theorem b1641 (b : ℝ) (hb : rootInterval.Contains b) : i1641.Contains (n1641 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b311 b hb) (b1636 b hb))
    (by norm_num [i1641, i311, i1636, RationalInterval.mul]) (by norm_num [i1641, i311, i1636, RationalInterval.mul])

def n1642 (b : ℝ) : ℝ := (n1640 b) + (n1641 b)
def i1642 : RationalInterval := ⟨(3635745480698023061547342305473 / 1000000000000000000000000000000 : ℚ), (3635745524481064340808178078947 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1642 (b : ℝ) (hb : rootInterval.Contains b) : i1642.Contains (n1642 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1640 b hb) (b1641 b hb))
    (by norm_num [i1642, i1640, i1641, RationalInterval.add]) (by norm_num [i1642, i1640, i1641, RationalInterval.add])

def n1643 (b : ℝ) : ℝ := (n1639 b) + (n1642 b)
def i1643 : RationalInterval := ⟨(5471083678511549587934253110421 / 1000000000000000000000000000000 : ℚ), (1094216749602507439011945399233 / 200000000000000000000000000000 : ℚ)⟩
theorem b1643 (b : ℝ) (hb : rootInterval.Contains b) : i1643.Contains (n1643 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1639 b hb) (b1642 b hb))
    (by norm_num [i1643, i1639, i1642, RationalInterval.add]) (by norm_num [i1643, i1639, i1642, RationalInterval.add])

def n1644 (b : ℝ) : ℝ := (n90 b) * (n1635 b)
def i1644 : RationalInterval := ⟨(99405515885381798268388423259 / 62500000000000000000000000000 : ℚ), (1590488276283975957990615165987 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1644 (b : ℝ) (hb : rootInterval.Contains b) : i1644.Contains (n1644 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b90 b hb) (b1635 b hb))
    (by norm_num [i1644, i90, i1635, RationalInterval.mul]) (by norm_num [i1644, i90, i1635, RationalInterval.mul])

def n1645 (b : ℝ) : ℝ := (n91 b) * (n1636 b)
def i1645 : RationalInterval := ⟨(2089373570387763721853174106669 / 1000000000000000000000000000000 : ℚ), (33429977464415675469578309 / 16000000000000000000000000 : ℚ)⟩
theorem b1645 (b : ℝ) (hb : rootInterval.Contains b) : i1645.Contains (n1645 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b91 b hb) (b1636 b hb))
    (by norm_num [i1645, i91, i1636, RationalInterval.mul]) (by norm_num [i1645, i91, i1636, RationalInterval.mul])

def n1646 (b : ℝ) : ℝ := (n1644 b) + (n1645 b)
def i1646 : RationalInterval := ⟨(3679861824553872494147388878813 / 1000000000000000000000000000000 : ℚ), (3679861867809955674839259478487 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1646 (b : ℝ) (hb : rootInterval.Contains b) : i1646.Contains (n1646 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1644 b hb) (b1645 b hb))
    (by norm_num [i1646, i1644, i1645, RationalInterval.add]) (by norm_num [i1646, i1644, i1645, RationalInterval.add])

def n1647 (b : ℝ) : ℝ := (n92 b) * (n1635 b)
def i1647 : RationalInterval := ⟨(7476685759845512650090502739 / 8000000000000000000000000000 : ℚ), (467292866544750125678990464231 / 500000000000000000000000000000 : ℚ)⟩
theorem b1647 (b : ℝ) (hb : rootInterval.Contains b) : i1647.Contains (n1647 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b92 b hb) (b1635 b hb))
    (by norm_num [i1647, i92, i1635, RationalInterval.mul]) (by norm_num [i1647, i92, i1635, RationalInterval.mul])

def n1648 (b : ℝ) : ℝ := (n93 b) * (n1636 b)
def i1648 : RationalInterval := ⟨(12751070708803523842032174549 / 8000000000000000000000000000 : ℚ), (398470963574574383227158873757 / 250000000000000000000000000000 : ℚ)⟩
theorem b1648 (b : ℝ) (hb : rootInterval.Contains b) : i1648.Contains (n1648 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b93 b hb) (b1636 b hb))
    (by norm_num [i1648, i93, i1636, RationalInterval.mul]) (by norm_num [i1648, i93, i1636, RationalInterval.mul])

def n1649 (b : ℝ) : ℝ := (n1647 b) + (n1648 b)
def i1649 : RationalInterval := ⟨(2528469558581129561515334661 / 1000000000000000000000000000 : ℚ), (252846958738779778426661642349 / 100000000000000000000000000000 : ℚ)⟩
theorem b1649 (b : ℝ) (hb : rootInterval.Contains b) : i1649.Contains (n1649 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1647 b hb) (b1648 b hb))
    (by norm_num [i1649, i1647, i1648, RationalInterval.add]) (by norm_num [i1649, i1647, i1648, RationalInterval.add])

def n1650 (b : ℝ) : ℝ := (n1635 b) * (n1501 b)
def i1650 : RationalInterval := ⟨(805556099519166915577275789791 / 1000000000000000000000000000000 : ℚ), (805556114224639494895386797367 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1650 (b : ℝ) (hb : rootInterval.Contains b) : i1650.Contains (n1650 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1635 b hb) (b1501 b hb))
    (by norm_num [i1650, i1635, i1501, RationalInterval.mul]) (by norm_num [i1650, i1635, i1501, RationalInterval.mul])

def n1651 (b : ℝ) : ℝ := (n1636 b) * (n1504 b)
def i1651 : RationalInterval := ⟨(1410677015688559197674476288101 / 1000000000000000000000000000000 : ℚ), (1410677033023434715227831224219 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1651 (b : ℝ) (hb : rootInterval.Contains b) : i1651.Contains (n1651 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1636 b hb) (b1504 b hb))
    (by norm_num [i1651, i1636, i1504, RationalInterval.mul]) (by norm_num [i1651, i1636, i1504, RationalInterval.mul])

def n1652 (b : ℝ) : ℝ := (n1650 b) + (n1651 b)
def i1652 : RationalInterval := ⟨(554058278801931528312938019473 / 250000000000000000000000000000 : ℚ), (1108116573624037105061609010793 / 500000000000000000000000000000 : ℚ)⟩
theorem b1652 (b : ℝ) (hb : rootInterval.Contains b) : i1652.Contains (n1652 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1650 b hb) (b1651 b hb))
    (by norm_num [i1652, i1650, i1651, RationalInterval.add]) (by norm_num [i1652, i1650, i1651, RationalInterval.add])

def n1653 (b : ℝ) : ℝ := (n1652 b) * (n13 b)
def i1653 : RationalInterval := ⟨(554058278801931528312938019473 / 125000000000000000000000000000 : ℚ), (1108116573624037105061609010793 / 250000000000000000000000000000 : ℚ)⟩
theorem b1653 (b : ℝ) (hb : rootInterval.Contains b) : i1653.Contains (n1653 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1652 b hb) (b13 b hb))
    (by norm_num [i1653, i1652, i13, RationalInterval.mul]) (by norm_num [i1653, i1652, i13, RationalInterval.mul])

def n1654 (b : ℝ) : ℝ := (n1624 b) * (n310 b)
def i1654 : RationalInterval := ⟨(131918471938147370640809262857 / 50000000000000000000000000000 : ℚ), (2638369471605430534353352727363 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1654 (b : ℝ) (hb : rootInterval.Contains b) : i1654.Contains (n1654 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1624 b hb) (b310 b hb))
    (by norm_num [i1654, i1624, i310, RationalInterval.mul]) (by norm_num [i1654, i1624, i310, RationalInterval.mul])

def n1655 (b : ℝ) : ℝ := (n1624 b) * (n311 b)
def i1655 : RationalInterval := ⟨(191019190140938636925251072333 / 125000000000000000000000000000 : ℚ), (764076770291901874812300297419 / 500000000000000000000000000000 : ℚ)⟩
theorem b1655 (b : ℝ) (hb : rootInterval.Contains b) : i1655.Contains (n1655 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1624 b hb) (b311 b hb))
    (by norm_num [i1655, i1624, i311, RationalInterval.mul]) (by norm_num [i1655, i1624, i311, RationalInterval.mul])

def n1656 (b : ℝ) : ℝ := (n1625 b) * (n310 b)
def i1656 : RationalInterval := ⟨(1862393494471285423333298255737 / 1000000000000000000000000000000 : ℚ), (1862393517143640623970824516681 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1656 (b : ℝ) (hb : rootInterval.Contains b) : i1656.Contains (n1656 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1625 b hb) (b310 b hb))
    (by norm_num [i1656, i1625, i310, RationalInterval.mul]) (by norm_num [i1656, i1625, i310, RationalInterval.mul])

def n1657 (b : ℝ) : ℝ := (n1625 b) * (n311 b)
def i1657 : RationalInterval := ⟨(134838166259407371992412504939 / 125000000000000000000000000000 : ℚ), (539352671756695041378588810087 / 500000000000000000000000000000 : ℚ)⟩
theorem b1657 (b : ℝ) (hb : rootInterval.Contains b) : i1657.Contains (n1657 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1625 b hb) (b311 b hb))
    (by norm_num [i1657, i1625, i311, RationalInterval.mul]) (by norm_num [i1657, i1625, i311, RationalInterval.mul])

def n1658 (b : ℝ) : ℝ := (n310 b) * (n1624 b)
def i1658 : RationalInterval := ⟨(131918471938147370640809262857 / 50000000000000000000000000000 : ℚ), (2638369471605430534353352727363 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1658 (b : ℝ) (hb : rootInterval.Contains b) : i1658.Contains (n1658 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b310 b hb) (b1624 b hb))
    (by norm_num [i1658, i310, i1624, RationalInterval.mul]) (by norm_num [i1658, i310, i1624, RationalInterval.mul])

def n1659 (b : ℝ) : ℝ := (n310 b) * (n1625 b)
def i1659 : RationalInterval := ⟨(1862393494471285423333298255737 / 1000000000000000000000000000000 : ℚ), (1862393517143640623970824516681 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1659 (b : ℝ) (hb : rootInterval.Contains b) : i1659.Contains (n1659 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b310 b hb) (b1625 b hb))
    (by norm_num [i1659, i310, i1625, RationalInterval.mul]) (by norm_num [i1659, i310, i1625, RationalInterval.mul])

def n1660 (b : ℝ) : ℝ := (n311 b) * (n1624 b)
def i1660 : RationalInterval := ⟨(191019190140938636925251072333 / 125000000000000000000000000000 : ℚ), (764076770291901874812300297419 / 500000000000000000000000000000 : ℚ)⟩
theorem b1660 (b : ℝ) (hb : rootInterval.Contains b) : i1660.Contains (n1660 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b311 b hb) (b1624 b hb))
    (by norm_num [i1660, i311, i1624, RationalInterval.mul]) (by norm_num [i1660, i311, i1624, RationalInterval.mul])

def n1661 (b : ℝ) : ℝ := (n311 b) * (n1625 b)
def i1661 : RationalInterval := ⟨(134838166259407371992412504939 / 125000000000000000000000000000 : ℚ), (539352671756695041378588810087 / 500000000000000000000000000000 : ℚ)⟩
theorem b1661 (b : ℝ) (hb : rootInterval.Contains b) : i1661.Contains (n1661 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b311 b hb) (b1625 b hb))
    (by norm_num [i1661, i311, i1625, RationalInterval.mul]) (by norm_num [i1661, i311, i1625, RationalInterval.mul])

def n1662 (b : ℝ) : ℝ := (n1654 b) + (n1658 b)
def i1662 : RationalInterval := ⟨(131918471938147370640809262857 / 25000000000000000000000000000 : ℚ), (2638369471605430534353352727363 / 500000000000000000000000000000 : ℚ)⟩
theorem b1662 (b : ℝ) (hb : rootInterval.Contains b) : i1662.Contains (n1662 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1654 b hb) (b1658 b hb))
    (by norm_num [i1662, i1654, i1658, RationalInterval.add]) (by norm_num [i1662, i1654, i1658, RationalInterval.add])

def n1663 (b : ℝ) : ℝ := (n1655 b) + (n1659 b)
def i1663 : RationalInterval := ⟨(3390547015598794518735306834401 / 1000000000000000000000000000000 : ℚ), (3390547057727444373595425111519 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1663 (b : ℝ) (hb : rootInterval.Contains b) : i1663.Contains (n1663 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1655 b hb) (b1659 b hb))
    (by norm_num [i1663, i1655, i1659, RationalInterval.add]) (by norm_num [i1663, i1655, i1659, RationalInterval.add])

def n1664 (b : ℝ) : ℝ := (n1656 b) + (n1660 b)
def i1664 : RationalInterval := ⟨(3390547015598794518735306834401 / 1000000000000000000000000000000 : ℚ), (3390547057727444373595425111519 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1664 (b : ℝ) (hb : rootInterval.Contains b) : i1664.Contains (n1664 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1656 b hb) (b1660 b hb))
    (by norm_num [i1664, i1656, i1660, RationalInterval.add]) (by norm_num [i1664, i1656, i1660, RationalInterval.add])

def n1665 (b : ℝ) : ℝ := (n1657 b) + (n1661 b)
def i1665 : RationalInterval := ⟨(134838166259407371992412504939 / 62500000000000000000000000000 : ℚ), (539352671756695041378588810087 / 250000000000000000000000000000 : ℚ)⟩
theorem b1665 (b : ℝ) (hb : rootInterval.Contains b) : i1665.Contains (n1665 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1657 b hb) (b1661 b hb))
    (by norm_num [i1665, i1657, i1661, RationalInterval.add]) (by norm_num [i1665, i1657, i1661, RationalInterval.add])

def n1666 (b : ℝ) : ℝ := (n1646 b) * (n310 b)
def i1666 : RationalInterval := ⟨(3281537825929309076567621087673 / 1000000000000000000000000000000 : ℚ), (3281537871939849742660545355631 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1666 (b : ℝ) (hb : rootInterval.Contains b) : i1666.Contains (n1666 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1646 b hb) (b310 b hb))
    (by norm_num [i1666, i1646, i310, RationalInterval.mul]) (by norm_num [i1666, i1646, i310, RationalInterval.mul])

def n1667 (b : ℝ) : ℝ := (n1646 b) * (n311 b)
def i1667 : RationalInterval := ⟨(1900679074632635469294334105297 / 1000000000000000000000000000000 : ℚ), (380135820364333877727640995539 / 200000000000000000000000000000 : ℚ)⟩
theorem b1667 (b : ℝ) (hb : rootInterval.Contains b) : i1667.Contains (n1667 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1646 b hb) (b311 b hb))
    (by norm_num [i1667, i1646, i311, RationalInterval.mul]) (by norm_num [i1667, i1646, i311, RationalInterval.mul])

def n1668 (b : ℝ) : ℝ := (n1649 b) * (n310 b)
def i1668 : RationalInterval := ⟨(90191087533029073136285216647 / 40000000000000000000000000000 : ℚ), (2254777219124055310433861385321 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1668 (b : ℝ) (hb : rootInterval.Contains b) : i1668.Contains (n1668 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1649 b hb) (b310 b hb))
    (by norm_num [i1668, i1649, i310, RationalInterval.mul]) (by norm_num [i1668, i1649, i310, RationalInterval.mul])

def n1669 (b : ℝ) : ℝ := (n1649 b) * (n311 b)
def i1669 : RationalInterval := ⟨(652987722089728353083059035857 / 500000000000000000000000000000 : ℚ), (1305975462388698476128516711821 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1669 (b : ℝ) (hb : rootInterval.Contains b) : i1669.Contains (n1669 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1649 b hb) (b311 b hb))
    (by norm_num [i1669, i1649, i311, RationalInterval.mul]) (by norm_num [i1669, i1649, i311, RationalInterval.mul])

def n1670 (b : ℝ) : ℝ := (n1501 b) * (n1624 b)
def i1670 : RationalInterval := ⟨(268304051949964216847533718037 / 200000000000000000000000000000 : ℚ), (167690035133452168625157994147 / 125000000000000000000000000000 : ℚ)⟩
theorem b1670 (b : ℝ) (hb : rootInterval.Contains b) : i1670.Contains (n1670 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1501 b hb) (b1624 b hb))
    (by norm_num [i1670, i1501, i1624, RationalInterval.mul]) (by norm_num [i1670, i1501, i1624, RationalInterval.mul])

def n1671 (b : ℝ) : ℝ := (n1501 b) * (n1625 b)
def i1671 : RationalInterval := ⟨(189392627715619613833943748407 / 200000000000000000000000000000 : ℚ), (23674078834159281322498394621 / 25000000000000000000000000000 : ℚ)⟩
theorem b1671 (b : ℝ) (hb : rootInterval.Contains b) : i1671.Contains (n1671 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1501 b hb) (b1625 b hb))
    (by norm_num [i1671, i1501, i1625, RationalInterval.mul]) (by norm_num [i1671, i1501, i1625, RationalInterval.mul])

def n1672 (b : ℝ) : ℝ := (n1504 b) * (n1624 b)
def i1672 : RationalInterval := ⟨(131353634092141387110287970539 / 125000000000000000000000000000 : ℚ), (210165817724501138510249614721 / 200000000000000000000000000000 : ℚ)⟩
theorem b1672 (b : ℝ) (hb : rootInterval.Contains b) : i1672.Contains (n1672 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1504 b hb) (b1624 b hb))
    (by norm_num [i1672, i1504, i1624, RationalInterval.mul]) (by norm_num [i1672, i1504, i1624, RationalInterval.mul])

def n1673 (b : ℝ) : ℝ := (n1504 b) * (n1625 b)
def i1673 : RationalInterval := ⟨(370883849720555397870579245181 / 500000000000000000000000000000 : ℚ), (741767710450977237969666834639 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1673 (b : ℝ) (hb : rootInterval.Contains b) : i1673.Contains (n1673 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1504 b hb) (b1625 b hb))
    (by norm_num [i1673, i1504, i1625, RationalInterval.mul]) (by norm_num [i1673, i1504, i1625, RationalInterval.mul])

def n1674 (b : ℝ) : ℝ := (n1666 b) + (n1670 b)
def i1674 : RationalInterval := ⟨(2311529042839565080402644838929 / 500000000000000000000000000000 : ℚ), (4623058153007467091661809308807 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1674 (b : ℝ) (hb : rootInterval.Contains b) : i1674.Contains (n1674 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1666 b hb) (b1670 b hb))
    (by norm_num [i1674, i1666, i1670, RationalInterval.add]) (by norm_num [i1674, i1666, i1670, RationalInterval.add])

def n1675 (b : ℝ) : ℝ := (n1667 b) + (n1671 b)
def i1675 : RationalInterval := ⟨(711910553302683384616013211833 / 250000000000000000000000000000 : ℚ), (569528451037608128307628152507 / 200000000000000000000000000000 : ℚ)⟩
theorem b1675 (b : ℝ) (hb : rootInterval.Contains b) : i1675.Contains (n1675 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1667 b hb) (b1671 b hb))
    (by norm_num [i1675, i1667, i1671, RationalInterval.add]) (by norm_num [i1675, i1667, i1671, RationalInterval.add])

def n1676 (b : ℝ) : ℝ := (n1668 b) + (n1672 b)
def i1676 : RationalInterval := ⟨(3305606261062857925289434180487 / 1000000000000000000000000000000 : ℚ), (1652803153873280501492554729463 / 500000000000000000000000000000 : ℚ)⟩
theorem b1676 (b : ℝ) (hb : rootInterval.Contains b) : i1676.Contains (n1676 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1668 b hb) (b1672 b hb))
    (by norm_num [i1676, i1668, i1672, RationalInterval.add]) (by norm_num [i1676, i1668, i1672, RationalInterval.add])

def n1677 (b : ℝ) : ℝ := (n1669 b) + (n1673 b)
def i1677 : RationalInterval := ⟨(511935785905141875476819140519 / 250000000000000000000000000000 : ℚ), (102387158641983785704909177323 / 50000000000000000000000000000 : ℚ)⟩
theorem b1677 (b : ℝ) (hb : rootInterval.Contains b) : i1677.Contains (n1677 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1669 b hb) (b1673 b hb))
    (by norm_num [i1677, i1669, i1673, RationalInterval.add]) (by norm_num [i1677, i1669, i1673, RationalInterval.add])

def n1678 (b : ℝ) : ℝ := (n1624 b) * (n1501 b)
def i1678 : RationalInterval := ⟨(268304051949964216847533718037 / 200000000000000000000000000000 : ℚ), (167690035133452168625157994147 / 125000000000000000000000000000 : ℚ)⟩
theorem b1678 (b : ℝ) (hb : rootInterval.Contains b) : i1678.Contains (n1678 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1624 b hb) (b1501 b hb))
    (by norm_num [i1678, i1624, i1501, RationalInterval.mul]) (by norm_num [i1678, i1624, i1501, RationalInterval.mul])

def n1679 (b : ℝ) : ℝ := (n1624 b) * (n1504 b)
def i1679 : RationalInterval := ⟨(131353634092141387110287970539 / 125000000000000000000000000000 : ℚ), (210165817724501138510249614721 / 200000000000000000000000000000 : ℚ)⟩
theorem b1679 (b : ℝ) (hb : rootInterval.Contains b) : i1679.Contains (n1679 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1624 b hb) (b1504 b hb))
    (by norm_num [i1679, i1624, i1504, RationalInterval.mul]) (by norm_num [i1679, i1624, i1504, RationalInterval.mul])

def n1680 (b : ℝ) : ℝ := (n1625 b) * (n1501 b)
def i1680 : RationalInterval := ⟨(189392627715619613833943748407 / 200000000000000000000000000000 : ℚ), (23674078834159281322498394621 / 25000000000000000000000000000 : ℚ)⟩
theorem b1680 (b : ℝ) (hb : rootInterval.Contains b) : i1680.Contains (n1680 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1625 b hb) (b1501 b hb))
    (by norm_num [i1680, i1625, i1501, RationalInterval.mul]) (by norm_num [i1680, i1625, i1501, RationalInterval.mul])

def n1681 (b : ℝ) : ℝ := (n1625 b) * (n1504 b)
def i1681 : RationalInterval := ⟨(370883849720555397870579245181 / 500000000000000000000000000000 : ℚ), (741767710450977237969666834639 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1681 (b : ℝ) (hb : rootInterval.Contains b) : i1681.Contains (n1681 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1625 b hb) (b1504 b hb))
    (by norm_num [i1681, i1625, i1504, RationalInterval.mul]) (by norm_num [i1681, i1625, i1504, RationalInterval.mul])

def n1682 (b : ℝ) : ℝ := (n310 b) * (n1646 b)
def i1682 : RationalInterval := ⟨(3281537825929309076567621087673 / 1000000000000000000000000000000 : ℚ), (3281537871939849742660545355631 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1682 (b : ℝ) (hb : rootInterval.Contains b) : i1682.Contains (n1682 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b310 b hb) (b1646 b hb))
    (by norm_num [i1682, i310, i1646, RationalInterval.mul]) (by norm_num [i1682, i310, i1646, RationalInterval.mul])

def n1683 (b : ℝ) : ℝ := (n310 b) * (n1649 b)
def i1683 : RationalInterval := ⟨(90191087533029073136285216647 / 40000000000000000000000000000 : ℚ), (2254777219124055310433861385321 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1683 (b : ℝ) (hb : rootInterval.Contains b) : i1683.Contains (n1683 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b310 b hb) (b1649 b hb))
    (by norm_num [i1683, i310, i1649, RationalInterval.mul]) (by norm_num [i1683, i310, i1649, RationalInterval.mul])

def n1684 (b : ℝ) : ℝ := (n311 b) * (n1646 b)
def i1684 : RationalInterval := ⟨(1900679074632635469294334105297 / 1000000000000000000000000000000 : ℚ), (380135820364333877727640995539 / 200000000000000000000000000000 : ℚ)⟩
theorem b1684 (b : ℝ) (hb : rootInterval.Contains b) : i1684.Contains (n1684 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b311 b hb) (b1646 b hb))
    (by norm_num [i1684, i311, i1646, RationalInterval.mul]) (by norm_num [i1684, i311, i1646, RationalInterval.mul])

def n1685 (b : ℝ) : ℝ := (n311 b) * (n1649 b)
def i1685 : RationalInterval := ⟨(652987722089728353083059035857 / 500000000000000000000000000000 : ℚ), (1305975462388698476128516711821 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1685 (b : ℝ) (hb : rootInterval.Contains b) : i1685.Contains (n1685 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b311 b hb) (b1649 b hb))
    (by norm_num [i1685, i311, i1649, RationalInterval.mul]) (by norm_num [i1685, i311, i1649, RationalInterval.mul])

def n1686 (b : ℝ) : ℝ := (n1678 b) + (n1682 b)
def i1686 : RationalInterval := ⟨(2311529042839565080402644838929 / 500000000000000000000000000000 : ℚ), (4623058153007467091661809308807 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1686 (b : ℝ) (hb : rootInterval.Contains b) : i1686.Contains (n1686 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1678 b hb) (b1682 b hb))
    (by norm_num [i1686, i1678, i1682, RationalInterval.add]) (by norm_num [i1686, i1678, i1682, RationalInterval.add])

def n1687 (b : ℝ) : ℝ := (n1679 b) + (n1683 b)
def i1687 : RationalInterval := ⟨(3305606261062857925289434180487 / 1000000000000000000000000000000 : ℚ), (1652803153873280501492554729463 / 500000000000000000000000000000 : ℚ)⟩
theorem b1687 (b : ℝ) (hb : rootInterval.Contains b) : i1687.Contains (n1687 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1679 b hb) (b1683 b hb))
    (by norm_num [i1687, i1679, i1683, RationalInterval.add]) (by norm_num [i1687, i1679, i1683, RationalInterval.add])

def n1688 (b : ℝ) : ℝ := (n1680 b) + (n1684 b)
def i1688 : RationalInterval := ⟨(711910553302683384616013211833 / 250000000000000000000000000000 : ℚ), (569528451037608128307628152507 / 200000000000000000000000000000 : ℚ)⟩
theorem b1688 (b : ℝ) (hb : rootInterval.Contains b) : i1688.Contains (n1688 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1680 b hb) (b1684 b hb))
    (by norm_num [i1688, i1680, i1684, RationalInterval.add]) (by norm_num [i1688, i1680, i1684, RationalInterval.add])

def n1689 (b : ℝ) : ℝ := (n1681 b) + (n1685 b)
def i1689 : RationalInterval := ⟨(511935785905141875476819140519 / 250000000000000000000000000000 : ℚ), (102387158641983785704909177323 / 50000000000000000000000000000 : ℚ)⟩
theorem b1689 (b : ℝ) (hb : rootInterval.Contains b) : i1689.Contains (n1689 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1681 b hb) (b1685 b hb))
    (by norm_num [i1689, i1681, i1685, RationalInterval.add]) (by norm_num [i1689, i1681, i1685, RationalInterval.add])

def n1690 (b : ℝ) : ℝ := (n1674 b) + (n1686 b)
def i1690 : RationalInterval := ⟨(2311529042839565080402644838929 / 250000000000000000000000000000 : ℚ), (4623058153007467091661809308807 / 500000000000000000000000000000 : ℚ)⟩
theorem b1690 (b : ℝ) (hb : rootInterval.Contains b) : i1690.Contains (n1690 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1674 b hb) (b1686 b hb))
    (by norm_num [i1690, i1674, i1686, RationalInterval.add]) (by norm_num [i1690, i1674, i1686, RationalInterval.add])

def n1691 (b : ℝ) : ℝ := (n1675 b) + (n1687 b)
def i1691 : RationalInterval := ⟨(6153248474273591463753487027819 / 1000000000000000000000000000000 : ℚ), (6153248562934601644523250221461 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1691 (b : ℝ) (hb : rootInterval.Contains b) : i1691.Contains (n1691 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1675 b hb) (b1687 b hb))
    (by norm_num [i1691, i1675, i1687, RationalInterval.add]) (by norm_num [i1691, i1675, i1687, RationalInterval.add])

def n1692 (b : ℝ) : ℝ := (n1676 b) + (n1688 b)
def i1692 : RationalInterval := ⟨(6153248474273591463753487027819 / 1000000000000000000000000000000 : ℚ), (6153248562934601644523250221461 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1692 (b : ℝ) (hb : rootInterval.Contains b) : i1692.Contains (n1692 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1676 b hb) (b1688 b hb))
    (by norm_num [i1692, i1676, i1688, RationalInterval.add]) (by norm_num [i1692, i1676, i1688, RationalInterval.add])

def n1693 (b : ℝ) : ℝ := (n1677 b) + (n1689 b)
def i1693 : RationalInterval := ⟨(511935785905141875476819140519 / 125000000000000000000000000000 : ℚ), (102387158641983785704909177323 / 25000000000000000000000000000 : ℚ)⟩
theorem b1693 (b : ℝ) (hb : rootInterval.Contains b) : i1693.Contains (n1693 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1677 b hb) (b1689 b hb))
    (by norm_num [i1693, i1677, i1689, RationalInterval.add]) (by norm_num [i1693, i1677, i1689, RationalInterval.add])

def n1694 (b : ℝ) : ℝ := (n1575 b) * (n1690 b)
def i1694 : RationalInterval := ⟨(-10401880873345179848822975428471 / 500000000000000000000000000000 : ℚ), (-10401880663508769486784301365037 / 500000000000000000000000000000 : ℚ)⟩
theorem b1694 (b : ℝ) (hb : rootInterval.Contains b) : i1694.Contains (n1694 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1575 b hb) (b1690 b hb))
    (by norm_num [i1694, i1575, i1690, RationalInterval.mul]) (by norm_num [i1694, i1575, i1690, RationalInterval.mul])

def n1695 (b : ℝ) : ℝ := (n1575 b) * (n1691 b)
def i1695 : RationalInterval := ⟨(-13844809305305912846613008757799 / 1000000000000000000000000000000 : ℚ), (-346120225703961070311103137853 / 25000000000000000000000000000 : ℚ)⟩
theorem b1695 (b : ℝ) (hb : rootInterval.Contains b) : i1695.Contains (n1695 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1575 b hb) (b1691 b hb))
    (by norm_num [i1695, i1575, i1691, RationalInterval.mul]) (by norm_num [i1695, i1575, i1691, RationalInterval.mul])

def n1696 (b : ℝ) : ℝ := (n1575 b) * (n1692 b)
def i1696 : RationalInterval := ⟨(-13844809305305912846613008757799 / 1000000000000000000000000000000 : ℚ), (-346120225703961070311103137853 / 25000000000000000000000000000 : ℚ)⟩
theorem b1696 (b : ℝ) (hb : rootInterval.Contains b) : i1696.Contains (n1696 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1575 b hb) (b1692 b hb))
    (by norm_num [i1696, i1575, i1692, RationalInterval.mul]) (by norm_num [i1696, i1575, i1692, RationalInterval.mul])

def n1697 (b : ℝ) : ℝ := (n1575 b) * (n1693 b)
def i1697 : RationalInterval := ⟨(-4607422151769283950276469571913 / 500000000000000000000000000000 : ℚ), (-4607422060181708240594684452619 / 500000000000000000000000000000 : ℚ)⟩
theorem b1697 (b : ℝ) (hb : rootInterval.Contains b) : i1697.Contains (n1697 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1575 b hb) (b1693 b hb))
    (by norm_num [i1697, i1575, i1693, RationalInterval.mul]) (by norm_num [i1697, i1575, i1693, RationalInterval.mul])

def n1698 (b : ℝ) : ℝ := (n1643 b) * (n1581 b)
def i1698 : RationalInterval := ⟨(27697360966592592956590357857621 / 1000000000000000000000000000000 : ℚ), (3462170203646124627286467472393 / 125000000000000000000000000000 : ℚ)⟩
theorem b1698 (b : ℝ) (hb : rootInterval.Contains b) : i1698.Contains (n1698 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1643 b hb) (b1581 b hb))
    (by norm_num [i1698, i1643, i1581, RationalInterval.mul]) (by norm_num [i1698, i1643, i1581, RationalInterval.mul])

def n1699 (b : ℝ) : ℝ := (n1698 b) * (n1516 b)
def i1699 : RationalInterval := ⟨(559966220775883698249252510563 / 25000000000000000000000000000 : ℚ), (22398649545489383678633639800509 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1699 (b : ℝ) (hb : rootInterval.Contains b) : i1699.Contains (n1699 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1698 b hb) (b1516 b hb))
    (by norm_num [i1699, i1698, i1516, RationalInterval.mul]) (by norm_num [i1699, i1698, i1516, RationalInterval.mul])

def n1700 (b : ℝ) : ℝ := (n1698 b) * (n1517 b)
def i1700 : RationalInterval := ⟨(7629628702406980113245838367339 / 500000000000000000000000000000 : ℚ), (15259257886594794564563656455363 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1700 (b : ℝ) (hb : rootInterval.Contains b) : i1700.Contains (n1700 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1698 b hb) (b1517 b hb))
    (by norm_num [i1700, i1698, i1517, RationalInterval.mul]) (by norm_num [i1700, i1698, i1517, RationalInterval.mul])

def n1701 (b : ℝ) : ℝ := (n1698 b) * (n1518 b)
def i1701 : RationalInterval := ⟨(7629628702406980113245838367339 / 500000000000000000000000000000 : ℚ), (15259257886594794564563656455363 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1701 (b : ℝ) (hb : rootInterval.Contains b) : i1701.Contains (n1701 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1698 b hb) (b1518 b hb))
    (by norm_num [i1701, i1698, i1518, RationalInterval.mul]) (by norm_num [i1701, i1698, i1518, RationalInterval.mul])

def n1702 (b : ℝ) : ℝ := (n1698 b) * (n1519 b)
def i1702 : RationalInterval := ⟨(5081103575026770776472664708431 / 500000000000000000000000000000 : ℚ), (10162207469220884982461421020937 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1702 (b : ℝ) (hb : rootInterval.Contains b) : i1702.Contains (n1702 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1698 b hb) (b1519 b hb))
    (by norm_num [i1702, i1698, i1519, RationalInterval.mul]) (by norm_num [i1702, i1698, i1519, RationalInterval.mul])

def n1703 (b : ℝ) : ℝ := (n1694 b) + (n1699 b)
def i1703 : RationalInterval := ⟨(797443542172494116162074782789 / 500000000000000000000000000000 : ℚ), (318977643694368941013007414087 / 200000000000000000000000000000 : ℚ)⟩
theorem b1703 (b : ℝ) (hb : rootInterval.Contains b) : i1703.Contains (n1703 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1694 b hb) (b1699 b hb))
    (by norm_num [i1703, i1694, i1699, RationalInterval.add]) (by norm_num [i1703, i1694, i1699, RationalInterval.add])

def n1704 (b : ℝ) : ℝ := (n1695 b) + (n1700 b)
def i1704 : RationalInterval := ⟨(1414448099508047379878667976879 / 1000000000000000000000000000000 : ℚ), (1414448858436351752119530941243 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1704 (b : ℝ) (hb : rootInterval.Contains b) : i1704.Contains (n1704 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1695 b hb) (b1700 b hb))
    (by norm_num [i1704, i1695, i1700, RationalInterval.add]) (by norm_num [i1704, i1695, i1700, RationalInterval.add])

def n1705 (b : ℝ) : ℝ := (n1696 b) + (n1701 b)
def i1705 : RationalInterval := ⟨(1414448099508047379878667976879 / 1000000000000000000000000000000 : ℚ), (1414448858436351752119530941243 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1705 (b : ℝ) (hb : rootInterval.Contains b) : i1705.Contains (n1705 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1696 b hb) (b1701 b hb))
    (by norm_num [i1705, i1696, i1701, RationalInterval.add]) (by norm_num [i1705, i1696, i1701, RationalInterval.add])

def n1706 (b : ℝ) : ℝ := (n1697 b) + (n1702 b)
def i1706 : RationalInterval := ⟨(236840711628743413098097568259 / 250000000000000000000000000000 : ℚ), (947363348857468501272052115699 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1706 (b : ℝ) (hb : rootInterval.Contains b) : i1706.Contains (n1706 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1697 b hb) (b1702 b hb))
    (by norm_num [i1706, i1697, i1702, RationalInterval.add]) (by norm_num [i1706, i1697, i1702, RationalInterval.add])

def n1707 (b : ℝ) : ℝ := (n1643 b) + (n1653 b)
def i1707 : RationalInterval := ⟨(1980709981785400362887551453241 / 200000000000000000000000000000 : ℚ), (9903550042508685615306163039337 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1707 (b : ℝ) (hb : rootInterval.Contains b) : i1707.Contains (n1707 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_add (b1643 b hb) (b1653 b hb))
    (by norm_num [i1707, i1643, i1653, RationalInterval.add]) (by norm_num [i1707, i1643, i1653, RationalInterval.add])

def n1708 (b : ℝ) : ℝ := (n1707 b) * (n1581 b)
def i1708 : RationalInterval := ⟨(50136721131789085000456004353459 / 1000000000000000000000000000000 : ℚ), (10027344474102774579581437083997 / 200000000000000000000000000000 : ℚ)⟩
theorem b1708 (b : ℝ) (hb : rootInterval.Contains b) : i1708.Contains (n1708 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1707 b hb) (b1581 b hb))
    (by norm_num [i1708, i1707, i1581, RationalInterval.mul]) (by norm_num [i1708, i1707, i1581, RationalInterval.mul])

def n1709 (b : ℝ) : ℝ := (n1594 b) * (n1643 b)
def i1709 : RationalInterval := ⟨(4155361464181365649529002753219 / 500000000000000000000000000000 : ℚ), (8310723088453543158011165223383 / 1000000000000000000000000000000 : ℚ)⟩
theorem b1709 (b : ℝ) (hb : rootInterval.Contains b) : i1709.Contains (n1709 b) := by
  exact RationalInterval.contains_widen (RationalInterval.contains_mul (b1594 b hb) (b1643 b hb))
    (by norm_num [i1709, i1594, i1643, RationalInterval.mul]) (by norm_num [i1709, i1594, i1643, RationalInterval.mul])

