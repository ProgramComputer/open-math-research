import CoarseProductData5
import CoarseProductSequential

set_option autoImplicit false
set_option maxRecDepth 16000
set_option maxHeartbeats 5000000
namespace OpenMathResearch.LongCycleExcedances
open Finset

private theorem linear_ledger_5 :
    coarseL5 = coarseLinearArray ⟨5, by decide⟩ := by
  decide +kernel

private theorem rec5_0 : checkSequentialBlock coarseL5 coarseQ5 0 24 = true := by
  decide +kernel
private theorem rec5_24 : checkSequentialBlock coarseL5 coarseQ5 24 24 = true := by
  decide +kernel
private theorem rec5_48 : checkSequentialBlock coarseL5 coarseQ5 48 24 = true := by
  decide +kernel
private theorem rec5_72 : checkSequentialBlock coarseL5 coarseQ5 72 24 = true := by
  decide +kernel
private theorem rec5_96 : checkSequentialBlock coarseL5 coarseQ5 96 24 = true := by
  decide +kernel
private theorem rec5_120 : checkSequentialBlock coarseL5 coarseQ5 120 24 = true := by
  decide +kernel
private theorem rec5_144 : checkSequentialBlock coarseL5 coarseQ5 144 24 = true := by
  decide +kernel
private theorem rec5_168 : checkSequentialBlock coarseL5 coarseQ5 168 24 = true := by
  decide +kernel
private theorem rec5_192 : checkSequentialBlock coarseL5 coarseQ5 192 24 = true := by
  decide +kernel
private theorem rec5_216 : checkSequentialBlock coarseL5 coarseQ5 216 24 = true := by
  decide +kernel

theorem coarse_ledger_recurrence_5 : ∀ m < 240,
    ∑ ij ∈ antidiagonal m,
      (ij.1+1)*coarseLinear ⟨5, by decide⟩ (ij.1+1)*coarseQ5[ij.2]! ≤
      (m+1)*coarseQ5[m+1]!*coarseScale := by
  intro m hm
  have hL : m+2 ≤ coarseL5.size := by change m+2 ≤ 241; omega
  have hQ : m+1 ≤ coarseQ5.size := by change m+1 ≤ 241; omega
  have hsum :
      (∑ ij ∈ antidiagonal m,
        (ij.1+1)*coarseLinear ⟨5, by decide⟩ (ij.1+1)*coarseQ5[ij.2]!) =
      ∑ ij ∈ antidiagonal m, (ij.1+1)*coarseL5[ij.1+1]!*coarseQ5[ij.2]! := by
    apply sum_congr rfl
    intro ij hij
    have e := mem_antidiagonal.mp hij
    rw [linear_ledger_5, coarseLinearArray_get _ (by omega : ij.1+1 < 241)]
  rw [hsum]

  by_cases h0 : m < 24
  · exact recurrence_of_sequential_check rec5_0 (by omega) (by omega) hL hQ
  by_cases h24 : m < 48
  · exact recurrence_of_sequential_check rec5_24 (by omega) (by omega) hL hQ
  by_cases h48 : m < 72
  · exact recurrence_of_sequential_check rec5_48 (by omega) (by omega) hL hQ
  by_cases h72 : m < 96
  · exact recurrence_of_sequential_check rec5_72 (by omega) (by omega) hL hQ
  by_cases h96 : m < 120
  · exact recurrence_of_sequential_check rec5_96 (by omega) (by omega) hL hQ
  by_cases h120 : m < 144
  · exact recurrence_of_sequential_check rec5_120 (by omega) (by omega) hL hQ
  by_cases h144 : m < 168
  · exact recurrence_of_sequential_check rec5_144 (by omega) (by omega) hL hQ
  by_cases h168 : m < 192
  · exact recurrence_of_sequential_check rec5_168 (by omega) (by omega) hL hQ
  by_cases h192 : m < 216
  · exact recurrence_of_sequential_check rec5_192 (by omega) (by omega) hL hQ
  exact recurrence_of_sequential_check rec5_216 (by omega) (by omega) hL hQ

#print axioms coarse_ledger_recurrence_5
end OpenMathResearch.LongCycleExcedances
