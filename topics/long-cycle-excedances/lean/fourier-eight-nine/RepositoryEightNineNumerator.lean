import EightNineHigh
import SmallCutoffLowPoints
import FourierOriginalLogSeries
import RepositoryLogTiltDiscrete

set_option autoImplicit false
noncomputable section
namespace RepositoryQuotientAudit
open Finset Real OpenMathResearch.LongCycleExcedances

/-- Original numerator contraction at cutoffs eight and nine on the selected radial band. -/
theorem original_eight_nine_contraction {k : ℕ} (hk : 8 ≤ k) (hku : k < 10)
    {s : ℝ} (hs : 0 ≤ s) (w : ℂ) :
    let w₁ : ℂ := (s:ℂ)+(π:ℂ)*Complex.I
    let r := ‖w₁‖
    r ≤ ‖w‖ → ‖w‖ ≤ (1+1/(k:ℝ))*r →
    let w' := (((1-1/(k:ℝ))*r/‖w‖:ℝ):ℂ)*w
    let w₁' := ((1-1/(k:ℝ):ℝ):ℂ)*w₁
    let G := numeratorLog k
      (fun j => (cutoffLogCoefficient k (-Real.exp (-s)) j : ℂ))
    ‖G w-diskLogisticLog s w'‖ + ‖G w₁-diskLogisticLog s w₁'‖ < 65 := by
  by_cases hlow : s ≤ 8*Real.sqrt (k:ℝ)
  · exact original_low_band_at_points (by omega) hs 65
      (low_band_eight_budget hs hk hlow) (diskLogisticLog s)
      (fun _ hz => original_log_series_hasSum hs hz) w
  · let g (j : ℕ) := (cutoffLogCoefficient k (-Real.exp (-s)) j : ℂ)
    have hhigh : 8*Real.sqrt (k:ℝ) < s := lt_of_not_ge hlow
    have hspos : 0 < s := (show 0 ≤ 8*Real.sqrt (k:ℝ) by positivity).trans_lt hhigh
    apply high_band_eight_original_shape k hk hku s hhigh w g
    intro i hi
    have hik : i+1 < k := by have := mem_range.mp hi; omega
    simpa only [Nat.add_sub_cancel] using
      cutoffLogCoefficient_hasSum (by omega : 1 ≤ i+1) hik hspos

#print axioms original_eight_nine_contraction
end RepositoryQuotientAudit
