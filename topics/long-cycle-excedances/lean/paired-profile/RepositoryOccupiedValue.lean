import OccupiedTuple
import RepositoryPairedProductLimit

set_option autoImplicit false
noncomputable section
namespace RepositoryQuotientAudit
open Finset Filter LongCycleBounds OpenMathResearch.LongCycleExcedances

/-- The scaled literal original row is the absolutely convergent full
lattice sum over distinguished occupied configurations. -/
theorem original_scaled_occupied_value {k N : ℕ} (hk : 3 ≤ k) (hN : 0 < N)
    (x : ℝ) (hx : 0 ≤ x) {R : ℝ} (hR : 0 < R) :
    (R:ℂ)^N*(Band.normalizedEnumerator N k x:ℂ)/(N.factorial:ℂ) =
      ∑' i, occupiedCoeff (occupiedDistinct k (x/R) (Real.pi/R))
        (occupiedPrimitive k (x/R) (Real.pi/R)) N i :=
  actual_occupiedCoeff_eq_of_product_limit hk hN (x/R) (ne_of_gt (by positivity))
    (tendsto_original_scaled_finite_paired_products (by omega) x hx hR N)

#print axioms original_scaled_occupied_value
end RepositoryQuotientAudit
