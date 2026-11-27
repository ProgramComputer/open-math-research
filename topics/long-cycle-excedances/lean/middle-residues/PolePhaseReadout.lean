import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real

theorem logarithmic_principal_unit (x : ℝ) :
    let w := (x:ℂ)+(π:ℂ)*Complex.I
    let θ := π/2-arctan (x/π)
    (‖w‖:ℂ)/w = Complex.exp (-(θ:ℂ)*Complex.I) := by
  let w := (x:ℂ)+(π:ℂ)*Complex.I
  let r := ‖w‖
  let θ := π/2-arctan (x/π)
  have hpre : w.re = x := by simp [w,Complex.add_re,Complex.mul_I_re]
  have hpim : w.im = π := by simp [w,Complex.add_im,Complex.mul_I_im]
  have hr : 0 < r := pi_pos.trans_le ((le_abs_self _).trans (hpim ▸ Complex.abs_im_le_norm w))
  have hr2 : r^2 = x^2+π^2 := by rw [Complex.sq_norm,Complex.normSq_apply,hpre,hpim];ring
  have hsq : √(1+(x/π)^2)=r/π := by
    rw [sqrt_eq_iff_eq_sq (by positivity) (div_nonneg hr.le pi_pos.le)]
    field_simp [pi_ne_zero] <;> nlinarith only [hr2]
  have hc : cos θ=x/r := by
    rw [show θ=π/2-arctan (x/π) by rfl,cos_pi_div_two_sub,sin_arctan,hsq]
    field_simp [hr.ne',pi_ne_zero]
  have hs : sin θ=π/r := by
    rw [show θ=π/2-arctan (x/π) by rfl,sin_pi_div_two_sub,cos_arctan,hsq,one_div,inv_div]
  have hnorm : w.normSq = r^2 := (Complex.sq_norm w).symm
  change (r:ℂ)/w = Complex.exp (-(θ:ℂ)*Complex.I)
  rw [←Complex.ofReal_neg,Complex.exp_mul_I,←Complex.ofReal_cos,←Complex.ofReal_sin,cos_neg,sin_neg,hc,hs]
  apply Complex.ext
  · rw [Complex.div_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,zero_div,add_zero,hpre,hnorm]
    simp only [Complex.add_re,Complex.mul_I_re,Complex.ofReal_re,Complex.ofReal_im,neg_zero,add_zero]
    field_simp [hr.ne'] <;> ring
  · rw [Complex.div_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,zero_div,zero_sub,hpim,hnorm]
    simp only [Complex.add_im,Complex.mul_I_im,Complex.ofReal_re,Complex.ofReal_im,zero_add]
    field_simp [hr.ne'] <;> ring

#print axioms logarithmic_principal_unit
end OpenMathResearch.LongCycleExcedances
