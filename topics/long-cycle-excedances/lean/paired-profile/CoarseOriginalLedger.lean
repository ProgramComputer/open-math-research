import CoarseLedger
import CoarseStarCertificate
import CoarseSlabDominance
import RoundedQDominated

set_option autoImplicit false
namespace OpenMathResearch.LongCycleExcedances
open Finset

def coarseOriginalLedger (slab : Fin 9) (b : ℕ) : ℕ :=
  coarseLift * (coarseQLedger slab)[b]!

theorem coarseOriginalLedger_zero (slab : Fin 9) : coarseOriginalLedger slab 0 = linearScale := by
  rw [coarseOriginalLedger, coarseQLedger_zero, coarseScale_lift]

theorem coarseOriginalLedger_recurrence (slab : Fin 9) (m : ℕ) (hm : m < 240) :
    ∑ ij ∈ antidiagonal m,
      (ij.1+1)*linearSlabTable slab (ij.1+1)*coarseOriginalLedger slab ij.2 ≤
      (m+1)*coarseOriginalLedger slab (m+1)*linearScale := by
  refine le_trans ?_ (lift_coarse_recurrence (coarseQLedger_recurrence slab m hm))
  apply sum_le_sum
  intro ij _
  exact Nat.mul_le_mul_right _
    (Nat.mul_le_mul_left _ (coarse_slab_dominates slab (ij.1+1) (coarseStar_bound slab)))

theorem roundedQ_le_coarseOriginalLedger (slab : Fin 9) (b : ℕ) (hb : b ≤ 240) :
    roundedQ linearScale (linearSlabTable slab) b ≤ coarseOriginalLedger slab b :=
  roundedQ_le_recurrence (by decide) _ _ (coarseOriginalLedger_zero slab)
    (coarseOriginalLedger_recurrence slab) b hb

#print axioms roundedQ_le_coarseOriginalLedger
#print axioms coarseOriginalLedger_zero
#print axioms coarseOriginalLedger_recurrence
end OpenMathResearch.LongCycleExcedances
