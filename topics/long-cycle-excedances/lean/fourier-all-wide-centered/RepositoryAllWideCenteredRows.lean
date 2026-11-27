import RepositoryFourierPairedRows
import RepositorySmallBoundary
import RepositorySmallMinorSums

set_option autoImplicit false
noncomputable section
namespace RepositoryQuotientAudit
open OpenMathResearch.LongCycleExcedances Real LongCycles

/-- Centered phase estimates on the original rows for all cutoffs above seven
in the large-size, large-aspect range. -/
theorem original_all_wide_centered_rows {n k : ℕ} (hn : 10000≤n) (hk : 8≤k) {s : ℝ} (hs : 0 ≤ s)
    (hx : 48 ≤ (n:ℝ)/k) :
    let p := fourierRowPole s 0
    let r := ‖p‖
    let S := π/r
    let C := s/r
    let T := contourNumerator k s
    let U := ‖T p‖
    let a := T p/(U:ℂ)*((r:ℂ)/p)^(n+1)
    let Y := fun q : ℕ => r^(q+1)/(2*U) *
      ((enumerator q k).eval (-Real.exp (-s))/((1+Real.exp (-s))^(q+1)*q.factorial))
    1 ≤ (n:ℝ)*S^2 →
    |Y n-a.re| < 37/300 ∧ |Y (n+1)-C*Y n-S*a.im| < (29/100)*S ∧
      ((enumerator n k).eval (-Real.exp (-s))=0 →
        99/100 < |a.im| ∧ 0<(enumerator (n+1) k).eval (-Real.exp (-s))*a.im) := by
  by_cases hlarge : 100≤k
  · exact original_wide_centered_rows hlarge hs hx
  apply centered_rows_from_original_fourier_bounds (by omega) hs hx
  · exact original_small_normalized_fourier_errors hn hk (by omega) hs
  · exact fun hR I => original_small_cutoff_minor_sums hn hk (by omega) hs hR I

#print axioms original_all_wide_centered_rows
end RepositoryQuotientAudit
