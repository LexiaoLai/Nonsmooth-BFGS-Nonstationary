#!/usr/bin/env python3
"""Package generated interval enclosures as the manuscript's scalar/matrix bounds."""
from pathlib import Path
from fractions import Fraction as F
import json
from generate_lean import OUT,qstr
import verify as v
m=json.loads((OUT/'trace_metadata.json').read_text());named=m['named']

def ref(k):return f'n{named[k]}'
def bound(k):return f'b{named[k]}'
def interval(k):return f'i{named[k]}'
def theorem(label,k,kind,q):
 n=named[k];q=qstr(q)
 relation={'lower':f'({q} : ℝ) < n{n} b','upper':f'n{n} b < ({q} : ℝ)',
   'le':f'n{n} b ≤ ({q} : ℝ)','ge':f'({q} : ℝ) ≤ n{n} b',
   'abs':f'|n{n} b| ≤ ({q} : ℝ)'}[kind]
 helper={'lower':'lower','upper':'upper','le':'upper_le','ge':'lower_le','abs':'absolute'}[kind]
 return [f'theorem {label} (b : ℝ) (hb : rootInterval.Contains b) :',
         f'    {relation} := by',
         f'  have h := {helper}_of_contains (a := ({q} : ℚ)) (b{n} b hb) (by norm_num [i{n}])',
         '  norm_num at h', '  exact h', '']
lines=[f'import {m["modules"][-1]}','import BFGS.Counterexample.Root','',
 '/-! Scalar enclosures and the explicit 0.78 row-sum bound. -/',
 'namespace BFGS.Counterexample.Trace','noncomputable section','open BFGS RationalInterval',
 'set_option maxHeartbeats 0','set_option maxRecDepth 100000','',
 'attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.vecHead Matrix.vecTail',
 'private theorem fin4_succ_two : (Fin.succ (2 : Fin 3) : Fin 4) = 3 := rfl',
 'attribute [local simp] fin4_succ_two','',
 'theorem root_mem_interval : rootInterval.Contains root := by',
 '  convert root_mem_narrow using 1; norm_num [rootInterval, RationalInterval.Contains]','',
 'private theorem lower_of_contains {I : RationalInterval} {x : ℝ} {a : ℚ}',
 '    (h : I.Contains x) (ha : a < I.lo) : (a : ℝ) < x :=',
 '  lt_of_lt_of_le (by exact_mod_cast ha) h.1','',
 'private theorem upper_of_contains {I : RationalInterval} {x : ℝ} {a : ℚ}',
 '    (h : I.Contains x) (ha : I.hi < a) : x < (a : ℝ) :=',
 '  lt_of_le_of_lt h.2 (by exact_mod_cast ha)','',
 'private theorem upper_le_of_contains {I : RationalInterval} {x : ℝ} {a : ℚ}',
 '    (h : I.Contains x) (ha : I.hi ≤ a) : x ≤ (a : ℝ) :=',
 '  le_trans h.2 (by exact_mod_cast ha)','',
 'private theorem lower_le_of_contains {I : RationalInterval} {x : ℝ} {a : ℚ}',
 '    (h : I.Contains x) (ha : a ≤ I.lo) : (a : ℝ) ≤ x :=',
 '  le_trans (by exact_mod_cast ha) h.1','',
 'private theorem absolute_of_contains {I : RationalInterval} {x : ℝ} {a : ℚ}',
 '    (h : I.Contains x) (ha : -a ≤ I.lo ∧ I.hi ≤ a) : |x| ≤ (a : ℝ) := by',
 '  apply abs_le.mpr',
 '  exact ⟨le_trans (by exact_mod_cast ha.1) h.1, le_trans h.2 (by exact_mod_cast ha.2)⟩','']
for i in range(5):
 lines+=theorem(f'norm_positive_{i}',f'normSquared_{i}','lower',0)
 lines+=theorem(f'norm_bound_{i}',f'normSquared_{i}','upper',8)
for i in range(4):
 lines+=theorem(f'coordinate_sign_{i}',f'coordinate_{i}','lower' if i<2 else 'upper',0)
 lines+=theorem(f'slope_lower_{i}',f'node_{i}_d','lower',F(1,50))
 lines+=theorem(f'slope_upper_{i}',f'node_{i}_d','le',1)
 lines+=theorem(f'curvature_positive_{i}',f'curvature_{i}','lower',0)
 lines+=theorem(f'armijo_positive_{i}',f'armijo_{i}','lower',F(1,50))
 lines+=theorem(f'wolfe_positive_{i}',f'wolfe_{i}','lower',0)
 lines+=theorem(f'second_data_bound_{i}',f'node_{i}_k','abs',5)
for sign,s in [('+','plus'),('-','minus')]:
 for j in range(3):
  lines+=theorem(f'gap_positive_{s}_{j}',f'gap_{sign}_{j}','lower',1)
  lines+=theorem(f'secant_lower_{s}_{j}',f'secant_{sign}_{j}','lower',F(1,2))
  lines+=theorem(f'secant_upper_{s}_{j}',f'secant_{sign}_{j}','upper',2)
 for j in range(5):
  for k,kind in [('L','ge'),('R','le'),('remaining','lower')]:
   lines+=theorem(f'bridge_{s}_{j}_{k}',f'bridge_{sign}_{j}_{k}',kind,0)
def ceiling_milli(q):
    q=F(q)
    return F(-((-q.numerator*1000)//q.denominator),1000)
UB=[[ceiling_milli(max(abs(F(q)) for q in m['bounds'][f'conjugatedTransverse_{i}_{j}']))
     for j in range(4)] for i in range(4)]
row_bounds=list(map(sum,UB))
computed_rows=v.stability_certificate(v.IV(v.ROOT_LO,v.ROOT_HI))['rows']
assert row_bounds == computed_rows, (row_bounds,computed_rows)
assert max(row_bounds) <= v.STABILITY_NORM_BOUND == F(78,100)
row_numerators=','.join(str(int(1000*q)) for q in row_bounds)
def matrix(rows):return '!!['+';\n  '.join(', '.join(r) for r in rows)+']'
lines += ['def conjugatedTransverse (b : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=',
 '  '+matrix([[ref(f'conjugatedTransverse_{i}_{j}')+' b' for j in range(4)] for i in range(4)]),'',
 'def entryBound : Matrix (Fin 4) (Fin 4) ℝ :=',
 '  '+matrix([[qstr(q) for q in row] for row in UB]),'']
for i in range(4):
 for j in range(4):lines+=theorem(f'entry_abs_{i}_{j}',f'conjugatedTransverse_{i}_{j}','abs',UB[i][j])
lines+=['theorem conjugated_entry_bound (b : ℝ) (hb : rootInterval.Contains b)',
  '    (i j : Fin 4) : |conjugatedTransverse b i j| ≤ entryBound i j := by',
  '  fin_cases i <;> fin_cases j']
for i in range(4):
 for j in range(4):lines+=[f'  · exact entry_abs_{i}_{j} b hb']
lines+=['','theorem conjugated_row_bound (b : ℝ) (hb : rootInterval.Contains b) (i : Fin 4) :',
 f'    ∑ j, |conjugatedTransverse b i j| ≤ (![{row_numerators}] : Fin 4 → ℝ) i / 1000 := by',
 '  have h0 := conjugated_entry_bound b hb i 0',
 '  have h1 := conjugated_entry_bound b hb i 1',
 '  have h2 := conjugated_entry_bound b hb i 2',
 '  have h3 := conjugated_entry_bound b hb i 3',
 '  fin_cases i <;> norm_num [entryBound, Fin.sum_univ_succ] at * <;> linarith','',
 'theorem conjugated_rows_le (b : ℝ) (hb : rootInterval.Contains b) (i : Fin 4) :',
 '    ∑ j, |conjugatedTransverse b i j| ≤ (78 / 100 : ℝ) := by',
 '  have h := conjugated_row_bound b hb i',
 '  fin_cases i <;> norm_num at h ⊢ <;> linarith','',
 'theorem conjugated_mulVec_bound (b : ℝ) (hb : rootInterval.Contains b) (v : Fin 4 → ℝ) :',
 '    ‖(conjugatedTransverse b).mulVec v‖ ≤ (78 / 100 : ℝ) * ‖v‖ := by',
 '  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (by norm_num) (norm_nonneg v))).2',
 '  intro i',
 '  rw [Real.norm_eq_abs]',
 '  change |∑ j, conjugatedTransverse b i j * v j| ≤ _',
 '  calc',
 '    _ ≤ ∑ j, |conjugatedTransverse b i j * v j| := Finset.abs_sum_le_sum_abs _ _',
 '    _ ≤ ∑ j, |conjugatedTransverse b i j| * ‖v‖ := by',
 '      apply Finset.sum_le_sum',
 '      intro j _',
 '      rw [abs_mul]',
 '      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)',
 '      simpa only [Real.norm_eq_abs] using norm_le_pi_norm v j',
 '    _ = (∑ j, |conjugatedTransverse b i j|) * ‖v‖ := (Finset.sum_mul _ _ _).symm',
 '    _ ≤ (78 / 100 : ℝ) * ‖v‖ :=',
 '      mul_le_mul_of_nonneg_right (conjugated_rows_le b hb i) (norm_nonneg v)','',
 'theorem root_conjugated_mulVec_bound (v : Fin 4 → ℝ) :',
 '    ‖(conjugatedTransverse root).mulVec v‖ ≤ (78 / 100 : ℝ) * ‖v‖ :=',
 '  conjugated_mulVec_bound root root_mem_interval v','',
 'end','end BFGS.Counterexample.Trace']
(OUT/'IntervalBounds.lean').write_text('\n'.join(lines)+'\n')
print('Generated IntervalBounds.lean')
