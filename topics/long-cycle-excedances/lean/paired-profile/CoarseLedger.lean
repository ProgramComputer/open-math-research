import CoarseProductProof0
import CoarseProductProof1
import CoarseProductProof2
import CoarseProductProof3
import CoarseProductProof4
import CoarseProductProof5
import CoarseProductProof6
import CoarseProductProof7
import CoarseProductProof8

set_option autoImplicit false
set_option maxRecDepth 12000
namespace OpenMathResearch.LongCycleExcedances
open Finset

def coarseQLedger (slab : Fin 9) : Array ℕ :=
  (![coarseQ0, coarseQ1, coarseQ2, coarseQ3, coarseQ4, coarseQ5, coarseQ6, coarseQ7, coarseQ8] : Fin 9 → Array ℕ) slab

theorem coarseQLedger_zero (slab : Fin 9) : (coarseQLedger slab)[0]! = coarseScale := by
  fin_cases slab <;> rfl

theorem coarseQLedger_recurrence (slab : Fin 9) : ∀ m < 240,
    ∑ ij ∈ antidiagonal m,
      (ij.1+1)*coarseLinear slab (ij.1+1)*(coarseQLedger slab)[ij.2]! ≤
      (m+1)*(coarseQLedger slab)[m+1]!*coarseScale := by
  fin_cases slab
  · exact coarse_ledger_recurrence_0
  · exact coarse_ledger_recurrence_1
  · exact coarse_ledger_recurrence_2
  · exact coarse_ledger_recurrence_3
  · exact coarse_ledger_recurrence_4
  · exact coarse_ledger_recurrence_5
  · exact coarse_ledger_recurrence_6
  · exact coarse_ledger_recurrence_7
  · exact coarse_ledger_recurrence_8

#print axioms coarseQLedger_zero
#print axioms coarseQLedger_recurrence
end OpenMathResearch.LongCycleExcedances
