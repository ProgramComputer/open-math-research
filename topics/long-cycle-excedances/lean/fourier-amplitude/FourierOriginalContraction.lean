import FourierOriginalLogSeries
import NumeratorSmallHeightPoints
import RepositoryHighHeightNumerator

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real RepositoryQuotientAudit

/-- The two rays use the same cutoff logarithm and principal analytic branch
throughout the entire height range. -/
theorem original_numerator_contraction_all_heights {k : ℕ} (hk : 100 ≤ k)
    {s : ℝ} (hs : 0 ≤ s) (w : ℂ) :
    let p := (s:ℂ)+(π:ℂ)*Complex.I
    let r := ‖p‖
    let G := numeratorLog k (fun j => (cutoffLogCoefficient k (-Real.exp (-s)) j : ℂ))
    r ≤ ‖w‖ → ‖w‖ ≤ (1+1/(k:ℝ))*r →
    ‖G w-diskLogisticLog s ((((1-1/(k:ℝ))*r/‖w‖:ℝ):ℂ)*w)‖ +
    ‖G p-diskLogisticLog s (((1-1/(k:ℝ):ℝ):ℂ)*p)‖ ≤ (2997:ℝ)/100 := by
  intro p r G h1 h2
  by_cases h : s ≤ 4*Real.sqrt (k:ℝ)
  · exact original_small_height_numerator_at_points hk hs h (diskLogisticLog s)
      (fun _ hz => original_log_series_hasSum hs hz) w h1 h2
  · exact ((original_high_height_numerator_contraction k hk s (lt_of_not_ge h) w h1 h2).le).trans
      (by norm_num)

#print axioms original_numerator_contraction_all_heights
end OpenMathResearch.LongCycleExcedances
