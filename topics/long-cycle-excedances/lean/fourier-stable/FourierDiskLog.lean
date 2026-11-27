import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Complex Real

/-- The ratio defining the numerator logarithm has a single-valued analytic
logarithm on the entire disk up to the two nearest poles. -/
def diskLogisticLog (s : ℝ) (w : ℂ) : ℂ :=
  Complex.log (1+Complex.exp (w-s)) - Complex.log (1+Complex.exp (-(s:ℂ)))

private theorem disk_denom_slit {s r : ℝ} (hs : 0 ≤ s) (hr2 : r^2=s^2+π^2)
    {w : ℂ} (hw : ‖w‖ < r) : 1+Complex.exp (w-s) ∈ Complex.slitPlane := by
  have he : (w-s).re = w.re-s := by simp
  have hi : (w-s).im = w.im := by simp
  by_cases h : w.re < s
  · left
    have hn : ‖Complex.exp (w-s)‖ < 1 := by
      rw [Complex.norm_exp,he,Real.exp_lt_one_iff]
      linarith
    have hl := Complex.abs_re_le_norm (Complex.exp (w-s))
    rw [Complex.add_re,Complex.one_re]
    linarith [(abs_lt.mp (hl.trans_lt hn)).1]
  · have hsq : w.re^2+w.im^2 < s^2+π^2 := by
      have hn := sq_lt_sq' (by linarith [norm_nonneg w] : -r < ‖w‖) hw
      rw [Complex.sq_norm,Complex.normSq_apply,hr2] at hn
      nlinarith
    have hre : s^2 ≤ w.re^2 := sq_le_sq' (by linarith) (le_of_not_gt h)
    have him : |w.im| < π := (sq_lt_sq.mp (by linarith : w.im^2 < π^2)).trans_eq (abs_of_pos Real.pi_pos)
    rcases lt_trichotomy w.im 0 with hn | hz | hp
    · right
      rw [Complex.add_im,Complex.one_im,zero_add,Complex.exp_im,hi]
      exact mul_ne_zero (Real.exp_pos _).ne' (Real.sin_neg_of_neg_of_neg_pi_lt hn (abs_lt.mp him).1).ne
    · left
      rw [Complex.add_re,Complex.one_re,Complex.exp_re,hi,hz,Real.cos_zero,mul_one]
      positivity
    · right
      rw [Complex.add_im,Complex.one_im,zero_add,Complex.exp_im,hi]
      exact mul_ne_zero (Real.exp_pos _).ne' (Real.sin_pos_of_pos_of_lt_pi hp (abs_lt.mp him).2).ne'

theorem diskLogisticLog_deriv {s r : ℝ} (hs : 0 ≤ s) (hr2 : r^2=s^2+π^2)
    {w : ℂ} (hw : ‖w‖ < r) :
    HasDerivAt (diskLogisticLog s) (Complex.exp (w-s)/(1+Complex.exp (w-s))) w := by
  have he : HasDerivAt (fun z : ℂ => Complex.exp (z-s)) (Complex.exp (w-s)) w := by
    simpa using ((hasDerivAt_id w).sub_const (s:ℂ)).cexp
  have hd := (Complex.hasDerivAt_log (disk_denom_slit hs hr2 hw)).comp w
    ((hasDerivAt_const w (1:ℂ)).add he)
  apply (hd.sub_const _).congr_deriv
  simp [div_eq_mul_inv,mul_comm]

theorem diskLogisticLog_normalized {s r : ℝ} (hs : 0 ≤ s) (hr2 : r^2=s^2+π^2)
    {w : ℂ} (hw : ‖w‖ < r) :
    Complex.exp (diskLogisticLog s w) = (1+Complex.exp (w-s))/(1+Complex.exp (-(s:ℂ))) := by
  have hr : 0 < r := (norm_nonneg w).trans_lt hw
  have hz := Complex.slitPlane_ne_zero (disk_denom_slit (w:=0) hs hr2 (by simpa using hr))
  rw [zero_sub] at hz
  rw [diskLogisticLog,Complex.exp_sub,Complex.exp_log (Complex.slitPlane_ne_zero (disk_denom_slit hs hr2 hw)),
    Complex.exp_log hz]

#print axioms diskLogisticLog_deriv
#print axioms diskLogisticLog_normalized
end OpenMathResearch.LongCycleExcedances
