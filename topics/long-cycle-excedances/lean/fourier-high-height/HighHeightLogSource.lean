import HighHeightContraction
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset

def frequencyWeight (s : ℝ) (a : ℕ) : ℂ :=
  -(((-Real.exp (-s):ℝ):ℂ)^(a+1))/((a+1:ℕ):ℂ)

def logFrequency (s : ℝ) (z : ℂ) (a : ℕ) : ℂ :=
  frequencyWeight s a * (Complex.exp (((a+1:ℕ):ℂ)*z)-1)

def localLogRatio (s : ℝ) (z : ℂ) : ℂ :=
  Complex.log (1+Complex.exp (z-(s:ℂ))) - Complex.log (1+Complex.exp (-(s:ℂ)))

private theorem shifted_neg_log {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun a : ℕ => -(z^(a+1))/((a+1:ℕ):ℂ)) (Complex.log (1-z)) := by
  have h := Complex.hasSum_taylorSeries_neg_log hz
  have h' : HasSum (fun a : ℕ => z^(a+1)/((a+1:ℕ):ℂ)) (-Complex.log (1-z)) := by
    apply (hasSum_nat_add_iff (f:=fun n : ℕ => z^n/(n:ℂ)) 1).mpr
    simpa using h
  simpa only [neg_div, neg_neg] using h'.neg

theorem log_frequency_hasSum {s : ℝ} (hs : 0 < s) {z : ℂ} (hz : ‖z‖ < s) :
    HasSum (logFrequency s z) (localLogRatio s z) := by
  have hre : z.re < s := (Complex.re_le_norm z).trans_lt hz
  have hZ : ‖-Complex.exp (z-(s:ℂ))‖ < 1 := by
    rw [norm_neg, Complex.norm_exp, Real.exp_lt_one_iff]
    simp only [Complex.sub_re,Complex.ofReal_re]
    linarith
  have h0 : ‖-Complex.exp (-(s:ℂ))‖ < 1 := by
    rw [norm_neg, Complex.norm_exp, Real.exp_lt_one_iff]
    simp only [Complex.neg_re,Complex.ofReal_re]
    linarith
  convert (shifted_neg_log hZ).sub (shifted_neg_log h0) using 1
  · funext a
    have he : -Complex.exp (z-(s:ℂ)) = (-Complex.exp (-(s:ℂ)))*Complex.exp z := by
      rw [sub_eq_add_neg,Complex.exp_add]
      ring
    simp only [logFrequency,frequencyWeight,he,mul_pow,Complex.exp_nat_mul,←Complex.ofReal_neg,
      ←Complex.ofReal_exp]
    ring
  · simp only [localLogRatio,sub_neg_eq_add]

theorem norm_frequency_weight (s : ℝ) (a : ℕ) :
    ‖frequencyWeight s a‖ = Real.exp (-((a+1:ℕ):ℝ)*s)/((a+1:ℕ):ℝ) := by
  unfold frequencyWeight
  rw [norm_div,norm_neg,norm_pow,Complex.norm_real,norm_neg,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),
    ←Real.exp_nat_mul]
  simp only [Complex.norm_natCast]
  congr 2
  ring

#print axioms log_frequency_hasSum
#print axioms norm_frequency_weight
end OpenMathResearch.LongCycleExcedances
