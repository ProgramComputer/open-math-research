import FourierNumeratorSeries
import FourierRealAxis

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances

/-- The original normalized all-degree pole coefficients sum to the analytic
logarithm at every point in the open unit disk. -/
theorem original_log_series_hasSum {s : ℝ} (hs : 0 ≤ s) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun j : ℕ => numeratorLogSeries s j * z^j)
      (diskLogisticLog s ((numeratorRadius s : ℂ) * z)) :=
  numerator_series_hasSum_disk_log hs (rowPole_summable s 0)
    (fourier_squared_poles_real_axis s) hz

#print axioms original_log_series_hasSum
end OpenMathResearch.LongCycleExcedances
