import CoarseProductData1
import CoarseProductSequential

set_option autoImplicit false
set_option maxRecDepth 16000
set_option maxHeartbeats 5000000
namespace OpenMathResearch.LongCycleExcedances
open Finset

private theorem linear_ledger_1 :
    coarseL1 = coarseLinearArray ⟨1, by decide⟩ := by
  decide +kernel

private theorem rec1_0 : checkSequentialBlock coarseL1 coarseQ1 0 24 = true := by
  decide +kernel
private theorem rec1_24 : checkSequentialBlock coarseL1 coarseQ1 24 24 = true := by
  decide +kernel
private theorem rec1_48 : checkSequentialBlock coarseL1 coarseQ1 48 24 = true := by
  decide +kernel
private theorem rec1_72 : checkSequentialBlock coarseL1 coarseQ1 72 24 = true := by
  decide +kernel
private theorem rec1_96 : checkSequentialBlock coarseL1 coarseQ1 96 24 = true := by
  decide +kernel
private theorem rec1_120 : checkSequentialBlock coarseL1 coarseQ1 120 24 = true := by
  decide +kernel
private theorem rec1_144 : checkSequentialBlock coarseL1 coarseQ1 144 24 = true := by
  decide +kernel
private theorem rec1_168 : checkSequentialBlock coarseL1 coarseQ1 168 24 = true := by
  decide +kernel
private theorem rec1_192 : checkSequentialBlock coarseL1 coarseQ1 192 24 = true := by
  decide +kernel
private theorem rec1_216 : checkSequentialBlock coarseL1 coarseQ1 216 24 = true := by
  decide +kernel

theorem coarse_ledger_recurrence_1 : ∀ m < 240,
    ∑ ij ∈ antidiagonal m,
      (ij.1+1)*coarseLinear ⟨1, by decide⟩ (ij.1+1)*coarseQ1[ij.2]! ≤
      (m+1)*coarseQ1[m+1]!*coarseScale := by
  intro m hm
  have hL : m+2 ≤ coarseL1.size := by change m+2 ≤ 241; omega
  have hQ : m+1 ≤ coarseQ1.size := by change m+1 ≤ 241; omega
  have hsum :
      (∑ ij ∈ antidiagonal m,
        (ij.1+1)*coarseLinear ⟨1, by decide⟩ (ij.1+1)*coarseQ1[ij.2]!) =
      ∑ ij ∈ antidiagonal m, (ij.1+1)*coarseL1[ij.1+1]!*coarseQ1[ij.2]! := by
    apply sum_congr rfl
    intro ij hij
    have e := mem_antidiagonal.mp hij
    rw [linear_ledger_1, coarseLinearArray_get _ (by omega : ij.1+1 < 241)]
  rw [hsum]

  by_cases h0 : m < 24
  · exact recurrence_of_sequential_check rec1_0 (by omega) (by omega) hL hQ
  by_cases h24 : m < 48
  · exact recurrence_of_sequential_check rec1_24 (by omega) (by omega) hL hQ
  by_cases h48 : m < 72
  · exact recurrence_of_sequential_check rec1_48 (by omega) (by omega) hL hQ
  by_cases h72 : m < 96
  · exact recurrence_of_sequential_check rec1_72 (by omega) (by omega) hL hQ
  by_cases h96 : m < 120
  · exact recurrence_of_sequential_check rec1_96 (by omega) (by omega) hL hQ
  by_cases h120 : m < 144
  · exact recurrence_of_sequential_check rec1_120 (by omega) (by omega) hL hQ
  by_cases h144 : m < 168
  · exact recurrence_of_sequential_check rec1_144 (by omega) (by omega) hL hQ
  by_cases h168 : m < 192
  · exact recurrence_of_sequential_check rec1_168 (by omega) (by omega) hL hQ
  by_cases h192 : m < 216
  · exact recurrence_of_sequential_check rec1_192 (by omega) (by omega) hL hQ
  exact recurrence_of_sequential_check rec1_216 (by omega) (by omega) hL hQ

#print axioms coarse_ledger_recurrence_1
end OpenMathResearch.LongCycleExcedances
