import CoarseCertifiedBudget
import RepositoryFourErrorDeterminant

set_option autoImplicit false
namespace RepositoryQuotientAudit
open Real OpenMathResearch.LongCycleExcedances

/-- A strictly positive lower bound for the adjacent determinant of the original
normalized permutation enumerators throughout the nine bounded-aspect intervals. -/
theorem original_bounded_aspect_determinant (slab : Fin 9) {j n : ℕ}
    (hn : 10000 ≤ n) (hlo : cutoffSlabLower slab*(j+2) ≤ n)
    (hhi : n ≤ linearSlabX slab*(j+2)) {θ : ℝ} (hS : 0 < sin θ)
    (hC : 0 ≤ cos θ) (hU : 6/5 ≤ (n:ℝ)*sin θ^2) :
    93581/10^6 < scaledOriginalDeterminant (j+2) n θ :=
  original_determinant_margin slab hn hlo hhi hS hC hU (coarseOriginalLedger slab)
    (coarseOriginalLedger_zero slab) (coarseOriginalLedger_recurrence slab) (coarse_four_budget slab)

#print axioms original_bounded_aspect_determinant
end RepositoryQuotientAudit
