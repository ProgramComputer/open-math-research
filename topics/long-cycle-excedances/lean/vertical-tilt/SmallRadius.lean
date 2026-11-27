import MinorPoleRadius
import Mathlib.Analysis.Real.Pi.Bounds

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real

/-- In the bounded logarithmic range the enlarged disk stops short of even
the first nonprincipal odd pole. -/
theorem small_log_radius_excludes {k : ℕ} (hk : 7 ≤ k) {x r W p : ℝ} (hx : 0 ≤ x)
    (hscale : x ≤ 10*√(k:ℝ)) (hW : 0 ≤ W) (hp : 3 ≤ p)
    (hr2 : r^2=x^2+π^2) (hW2 : W^2=x^2+(p*π)^2) :
    r*(1+1/(50*(k:ℝ))) < W := by
  have hk' : (7:ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0:ℝ)<k := by linarith
  have hx2 := pow_le_pow_left₀ hx hscale 2
  rw [mul_pow,Real.sq_sqrt hkpos.le] at hx2
  have hpi2 : π^2 ≤ 10 := (pow_le_pow_left₀ pi_pos.le pi_lt_d2.le 2).trans (by norm_num)
  have hrmax : r^2 ≤ 102*(k:ℝ) := by linarith
  let y := 1/(50*(k:ℝ))
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hy1 : y ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  have hy2 : y^2 ≤ y := by nlinarith only [mul_nonneg (sub_nonneg.mpr hy1) hy]
  have hinc : r^2*((1+y)^2-1) ≤ 306/50 := by
    have hpoly : (1+y)^2-1 ≤ 3*y := by linarith only [hy2,show (1+y)^2-1 = 2*y+y^2 by ring]
    have h := mul_le_mul (a := r^2) (b := 102*(k:ℝ)) hrmax hpoly
      (by nlinarith only [hy, sq_nonneg y]) (by positivity)
    have he : 102*(k:ℝ)*(3*y) = 306/50 := by dsimp [y]; field_simp; ring
    exact h.trans he.le
  have hpp : 9 ≤ p^2 := (by norm_num : (9:ℝ) ≤ 3^2).trans (pow_le_pow_left₀ (by norm_num) hp 2)
  have hπ : 9 < π^2 := by nlinarith only [mul_pos (sub_pos.mpr pi_gt_three) (by linarith only [pi_gt_three] : 0 < π+3)]
  apply lt_of_not_ge
  intro hb
  have h := pow_le_pow_left₀ hW hb 2
  change W^2 ≤ (r*(1+y))^2 at h
  rw [mul_pow,hW2,mul_pow] at h
  nlinarith only [hinc,h,hr2,mul_le_mul_of_nonneg_right hpp (sq_nonneg π),hπ]

#print axioms small_log_radius_excludes
end OpenMathResearch.LongCycleExcedances
