import LowBandContraction
import NumeratorLogSeries

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open scoped Real

private theorem low_height_scale_at {s b U K : ℝ} {k : ℕ}
    (hs : 0 ≤ s) (hb : 0 ≤ b) (hu : 0 ≤ U) (hK : 0 < K) (hk : K ≤ k)
    (hsh : s ≤ b*Real.sqrt k)
    (hfixed : b^2 ≤ (U^2-1/K)*(3.14:ℝ)^2)
    (hpos : 0 ≤ U^2-1/K) :
    1/((π/numeratorRadius s)*Real.sqrt k) ≤ U := by
  have hkr : (0:ℝ) < k := hK.trans_le hk
  have hks : 0 < Real.sqrt (k:ℝ) := Real.sqrt_pos.2 hkr
  have hpi : 0 < π := Real.pi_pos
  have hp : (3.14:ℝ)^2 ≤ π^2 :=
    pow_le_pow_left₀ (by norm_num) Real.pi_gt_d2.le 2
  have hx : b^2 ≤ (U^2-1/K)*π^2 := hfixed.trans (mul_le_mul_of_nonneg_left hp hpos)
  have hss : s^2 ≤ b^2*(k:ℝ) := by
    have h := pow_le_pow_left₀ hs hsh 2
    rwa [mul_pow, Real.sq_sqrt hkr.le] at h
  have hpk : π^2 ≤ (k:ℝ)*π^2/K := by
    apply (le_div_iff₀ hK).2
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right hk (sq_nonneg π)
  have hy := mul_le_mul_of_nonneg_right hx hkr.le
  have he : (U^2-1/K)*π^2*(k:ℝ)=U^2*π^2*k-k*π^2/K := by ring
  rw [he] at hy
  have hh : s^2+π^2 ≤ U^2*π^2*(k:ℝ) := by linarith only [hss,hpk,hy]
  have hr : numeratorRadius s/(π*Real.sqrt (k:ℝ)) ≤ U := by
    apply (div_le_iff₀ (mul_pos hpi hks)).mpr
    unfold numeratorRadius
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    simpa only [mul_pow, Real.sq_sqrt hkr.le, mul_assoc] using hh
  have heq : 1/((π/numeratorRadius s)*Real.sqrt k) =
      numeratorRadius s/(π*Real.sqrt k) := by
    field_simp [Real.pi_ne_zero, (numeratorRadius_pos s).ne', hks.ne']
  rwa [heq]

open private numerator_linear_bound from NumeratorLogSeries in
theorem original_low_band_series {s : ℝ} (hs : 0 ≤ s) {k : ℕ} (hk : 8 ≤ k) {R : ℝ}
    (hR : 1 ≤ R) (hRu : R ≤ 1+1/(k:ℝ)) {ξ η : ℂ}
    (hξ : ‖ξ‖ = 1) (hη : ‖η‖ = 1) :
    let c := numeratorLogSeries s
    let ρ : ℂ := ((1-1/(k:ℝ):ℝ):ℂ)
    let U := 1/((π/numeratorRadius s)*Real.sqrt k)
    ‖numeratorTaylor k c ((R:ℂ)*ξ) - (∑' j, c j * (ρ*ξ)^j)‖ +
      ‖numeratorTaylor k c η - (∑' j, c j * (ρ*η)^j)‖ ≤
      12/(k:ℝ)+(5/2+1)*(2+9*U/2)+2*(3/8)*(2+9*U/4) := by
  have hS : 0 < π/numeratorRadius s := div_pos Real.pi_pos (numeratorRadius_pos s)
  have h := low_band_contraction hk (numeratorLogSeries s) hS hR hRu hξ hη
    (numerator_linear_bound hs) (fun _ hj => numerator_log_series_envelope s hj)
  dsimp only
  convert h using 1 <;> ring

theorem low_band_fifty_budget {s : ℝ} (hs : 0 ≤ s) {k : ℕ}
    (hk : 50 ≤ k) (hsh : s ≤ 4*Real.sqrt k) :
    let U := 1/((π/numeratorRadius s)*Real.sqrt k)
    12/(k:ℝ)+(5/2+1)*(2+9*U/2)+2*(3/8)*(2+9*U/4) < 32 := by
  have hkR : (50:ℝ) ≤ k := by exact_mod_cast hk
  have hU := low_height_scale_at hs (b := 4) (U := 13/10) (K := 50)
    (by norm_num) (by norm_num) (by norm_num) hkR hsh (by norm_num) (by norm_num)
  have hd := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 12)
    (by norm_num : (0:ℝ)<50) hkR
  dsimp only
  linarith only [hU,hd]

theorem low_band_ten_budget {s : ℝ} (hs : 0 ≤ s) {k : ℕ}
    (hk : 10 ≤ k) (hsh : s ≤ 8*Real.sqrt k) :
    let U := 1/((π/numeratorRadius s)*Real.sqrt k)
    12/(k:ℝ)+(5/2+1)*(2+9*U/2)+2*(3/8)*(2+9*U/4) < 60 := by
  have hkR : (10:ℝ) ≤ k := by exact_mod_cast hk
  have hU := low_height_scale_at hs (b := 8) (U := 13/5) (K := 10)
    (by norm_num) (by norm_num) (by norm_num) hkR hsh (by norm_num) (by norm_num)
  have hd := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 12)
    (by norm_num : (0:ℝ)<10) hkR
  dsimp only
  linarith only [hU,hd]

theorem low_band_eight_budget {s : ℝ} (hs : 0 ≤ s) {k : ℕ}
    (hk : 8 ≤ k) (hsh : s ≤ 8*Real.sqrt k) :
    let U := 1/((π/numeratorRadius s)*Real.sqrt k)
    12/(k:ℝ)+(5/2+1)*(2+9*U/2)+2*(3/8)*(2+9*U/4) < 65 := by
  have hkR : (8:ℝ) ≤ k := by exact_mod_cast hk
  have hU := low_height_scale_at hs (b := 8) (U := 13/5) (K := 8)
    (by norm_num) (by norm_num) (by norm_num) hkR hsh (by norm_num) (by norm_num)
  have hd := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 12)
    (by norm_num : (0:ℝ)<8) hkR
  dsimp only
  linarith only [hU,hd]

#print axioms low_band_eight_budget
#print axioms original_low_band_series
#print axioms low_band_fifty_budget
#print axioms low_band_ten_budget
end OpenMathResearch.LongCycleExcedances
