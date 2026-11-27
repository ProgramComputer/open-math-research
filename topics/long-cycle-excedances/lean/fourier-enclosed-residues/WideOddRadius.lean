import WideOddMass

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real

/-- Enclosure on the inflated circle and middle-angle scaling imply a
Gaussian majorant in the odd pole label for the normalized radius. -/
theorem wide_enclosed_radius_decay {r W p S : ℝ} {n : ℕ}
    (hr : 0 < r) (hW : 0 < W) (hp : 1 ≤ p)
    (hgeom : (W/r)^2 = 1+(p^2-1)*S^2)
    (henc : (W/r)^2 ≤ 51/50) (hmiddle : 1 ≤ (n:ℝ)*S^2) :
    (r/W)^n ≤ exp (-(49/100)*(p^2-1)) := by
  let z := (p^2-1)*S^2
  have hp2 : 0 ≤ p^2-1 := by nlinarith [sq_nonneg (p-1)]
  have hz : 0 ≤ z := mul_nonneg hp2 (sq_nonneg _)
  have hz1 : 1+z ≤ 50/49 := by
    rw [←hgeom]
    exact henc.trans (by norm_num)
  have hpos : 0 < 1+z := by linarith
  have hlog : z/(1+z) ≤ log (1+z) := by
    have h := log_le_sub_one_of_pos (inv_pos.mpr hpos)
    rw [log_inv] at h
    have hrw : z/(1+z) = 1-(1+z)⁻¹ := by field_simp
    rw [hrw]
    linarith only [h]
  have hs : (49/50)*z ≤ log (1+z) := by
    apply le_trans _ hlog
    apply (le_div_iff₀ hpos).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hz1 hz]
  have hpwr := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg (α := ℝ) n)
  have hz2 : p^2-1 ≤ (n:ℝ)*z := by
    dsimp only [z]; nlinarith only [mul_le_mul_of_nonneg_left hmiddle hp2]
  have hlogr : log (1+z) = -(2*log (r/W)) := by
    rw [←hgeom,log_pow,log_div hW.ne' hr.ne',log_div hr.ne' hW.ne']
    push_cast; ring
  rw [hlogr] at hpwr
  apply (log_le_log_iff (pow_pos (div_pos hr hW) _) (exp_pos _)).mp
  rw [log_pow, log_exp]
  linarith only [hpwr,hz2]

#print axioms wide_enclosed_radius_decay
end OpenMathResearch.LongCycleExcedances
