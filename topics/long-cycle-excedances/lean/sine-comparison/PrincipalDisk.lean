import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real

/-- A disk lower bound retains real/imaginary correlation in the complex
exponential and uses only two scalar Taylor inequalities. -/
theorem principal_disk_exp_re {η : ℝ} {Z : ℂ} (he : η ≤ 81/100)
    (hz : ‖Z‖ ≤ η) : exp (-η) ≤ (Complex.exp Z).re := by
  have he0 := (norm_nonneg Z).trans hz
  have hsq := pow_le_pow_left₀ (norm_nonneg Z) hz 2
  rw [Complex.sq_norm,Complex.normSq_apply] at hsq
  let h := Z.re+η
  have hab := Complex.abs_re_le_norm Z
  have hh : 0 ≤ h := by dsimp only [h]; linarith only [neg_abs_le Z.re,hab,hz]
  have hy : Z.im^2 ≤ h*(2*η-h) := by dsimp only [h]; nlinarith only [hsq]
  have cap : (1+h)*(2*η-h) ≤ 2 := by
    have e : (η+1/2)^2 ≤ (81/100+1/2:ℝ)^2 := by
      apply pow_le_pow_left₀ <;> linarith
    calc
      _ = (η+1/2)^2-(h-(η-1/2))^2 := by ring
      _ ≤ (η+1/2)^2 := sub_le_self _ (sq_nonneg _)
      _ ≤ 2 := e.trans (by norm_num)
  have hp : 0 ≤ 1+h := by linarith
  have hbound := mul_le_mul_of_nonneg_left hy hp
  have hηsq : η^2 ≤ (81/100:ℝ)^2 := pow_le_pow_left₀ he0 he 2
  have hcos : 0 < 1-Z.im^2/2 := by nlinarith only [hηsq,hsq,sq_nonneg Z.re]
  have htwo : (1+h)*Z.im^2 ≤ 2*h := by
    refine hbound.trans ?_
    calc
      _ = ((1+h)*(2*η-h))*h := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right cap hh
  have hprod : 1 ≤ (1+h)*(1-Z.im^2/2) := by
    calc
      _ = 1+h-(2*h)/2 := by ring
      _ ≤ 1+h-((1+h)*Z.im^2)/2 := sub_le_sub_left (div_le_div_of_nonneg_right htwo (by norm_num)) _
      _ = _ := by ring
  have hexp : 1+h ≤ exp h := by linarith only [add_one_le_exp h]
  have hcos' : 1-Z.im^2/2 ≤ cos Z.im := one_sub_sq_div_two_le_cos
  have hb := hprod.trans (mul_le_mul hexp hcos' hcos.le (exp_pos h).le)
  rw [Complex.exp_re]
  calc
    exp (-η) ≤ exp (-η)*(exp h*cos Z.im) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hb (exp_pos (-η)).le
    _ = _ := by rw [←mul_assoc,←exp_add]; dsimp only [h]; ring_nf

/-- Pointwise denominator bound under the logarithmic integral. It also
applies to the conjugate principal pole on the boundary of the unit disk. -/
theorem principal_radial_denominator {v : ℂ} {t : ℝ} (hv : ‖v‖ ≤ 1)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) : t*‖1-v‖ ≤ ‖1-(t:ℂ)*v‖ := by
  have hx : 0 ≤ 1-v.re := by
    have hh := (le_abs_self v.re).trans ((Complex.abs_re_le_norm v).trans hv)
    linarith
  have hid : (1-t*v.re)^2+t^2*v.im^2 - t^2*((1-v.re)^2+v.im^2) =
      (1-t)^2+2*(t*(1-t))*(1-v.re) := by ring
  have hgeom := mul_nonneg (mul_nonneg ht (sub_nonneg.mpr ht1)) hx
  have hsq : (t*‖1-v‖)^2 ≤ ‖1-(t:ℂ)*v‖^2 := by
    rw [mul_pow,Complex.sq_norm,Complex.sq_norm]
    simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im,Complex.one_re,
      Complex.one_im,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,sub_zero,add_zero,zero_sub,neg_mul_neg]
    nlinarith only [hid,hgeom,sq_nonneg (1-t)]
  nlinarith only [hsq,mul_nonneg ht (norm_nonneg (1-v)),norm_nonneg (1-(t:ℂ)*v),
    sq_nonneg (t*‖1-v‖ - ‖1-(t:ℂ)*v‖)]

#print axioms principal_disk_exp_re
#print axioms principal_radial_denominator
end OpenMathResearch.LongCycleExcedances
