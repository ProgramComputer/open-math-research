import FourierDiskLog
import FourierDiskRemainder
import FourierCutoffLogSlope

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Complex Real Filter Metric
open scoped Topology

theorem disk_finite_fourier_log_tendsto {s r : ℝ} (hs : 0 ≤ s) (hr2 : r^2=s^2+π^2)
    (hp : ∀ i, r ≤ ‖fourierRowPole s i‖)
    (hS : Summable (fun i => 1/‖fourierRowPole s i‖^2))
    (hreal : ∀ x : ℝ, x < s → inverseSquarePoleSum (fourierRowPole s) (x:ℂ) =
      -Complex.exp ((x:ℂ)-s)/(1+Complex.exp ((x:ℂ)-s))^2) (b : ℕ → ℂ)
    (hb1 : b 1 = Complex.exp (-(s:ℂ))/(1+Complex.exp (-(s:ℂ))))
    (hb : ∀ j, b (j+2)*((j+2:ℕ):ℂ) = -(∑' i, (1:ℂ)/fourierRowPole s i^(j+2)))
    {w : ℂ} (hw : ‖w‖ < r) :
    Tendsto (fun m => finiteFourierLog m b w) atTop (𝓝 (diskLogisticLog s w)) := by
  let P := fourierRowPole s
  let ρ := ‖w‖
  let q := ρ/r
  let C := (ρ/(1-q))*(∑' i, 1/‖P i‖^2)
  have hr : 0 < r := (norm_nonneg _).trans_lt hw
  have hq0 : 0 ≤ q := div_nonneg (norm_nonneg _) hr.le
  have hq1 : q < 1 := (div_lt_one hr).mpr hw
  have hest (m : ℕ) : ‖finiteFourierLog m b w-diskLogisticLog s w‖ ≤ (q^m*C)*ρ := by
    let F := fun z : ℂ => finiteFourierLog m b z-diskLogisticLog s z
    let g := fun z : ℂ => ∑' i, z^(m+1)/(P i^(m+1)*(P i-z))
    let B := closedBall (0:ℂ) ρ
    have hg (z : ℂ) (hz : z ∈ B) : HasDerivAt F (g z) z := by
      have hz' : ‖z‖ ≤ ρ := by simpa only [B,mem_closedBall,dist_zero_right] using hz
      have havoid : z ∉ Set.range P := by
        rintro ⟨i,rfl⟩
        exact (not_lt_of_ge (hp i)) (hz'.trans_lt hw)
      have hd := (finiteFourierLog_deriv m b z).sub (diskLogisticLog_deriv hs hr2 (hz'.trans_lt hw))
      exact hd.congr_deriv (finiteFourierSlope_remainder s m b hreal hb1 (fun j _ => hb j) havoid)
    have hbound (z : ℂ) (hz : z ∈ B) : ‖g z‖ ≤ q^m*C := by
      have hz' : ‖z‖ ≤ ρ := by simpa only [B,mem_closedBall,dist_zero_right] using hz
      simpa only [g,C,q,P,mul_assoc] using disk_geometric_remainder_bound P
        (norm_nonneg _) hw hp hS m hz'
    have hz0 : (0:ℂ) ∈ B := by simp [B,ρ]
    have hzw : w ∈ B := by simp [B,ρ]
    have he := (convex_closedBall (0:ℂ) ρ).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun z hz => (hg z hz).hasDerivWithinAt) hbound hz0 hzw
    have hF0 : F 0 = 0 := by simp [F,finiteFourierLog,diskLogisticLog]
    simpa only [hF0,sub_zero,F,ρ] using he
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) hest
  have h := ((tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const C).mul_const ρ
  simpa only [zero_mul] using h

#print axioms disk_finite_fourier_log_tendsto
end OpenMathResearch.LongCycleExcedances
