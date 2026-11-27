import PrincipalDisk
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real Set MeasureTheory

/-- Radial integral on the closed disk minus one. Written with k=j+2,
so the denominator expected in the uniform pole bound is j+1. -/
def principalLogIntegral (j : ℕ) (v : ℂ) : ℂ :=
  ∫ t in (0:ℝ)..1, v^(j+2)*(t:ℂ)^(j+1)/(1-(t:ℂ)*v)

theorem principal_log_integral_bound (j : ℕ) {v : ℂ} (hv : ‖v‖ ≤ 1) (hv1 : v ≠ 1) :
    ‖principalLogIntegral j v‖ ≤ ‖v‖^(j+2)/(((j:ℝ)+1)*‖1-v‖) := by
  have hden : 0 < ‖1-v‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hv1))
  have hne (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : (1-(t:ℂ)*v) ≠ 0 := by
    rcases eq_or_lt_of_le ht.1 with h|h
    · simp [←h]
    · exact norm_pos_iff.mp ((mul_pos h hden).trans_le (principal_radial_denominator hv ht.1 ht.2))
  let f (t : ℝ) : ℂ := v^(j+2)*(t:ℂ)^(j+1)/(1-(t:ℂ)*v)
  let g (t : ℝ) := (‖v‖^(j+2)/‖1-v‖)*t^j
  have hc : ContinuousOn f (Icc (0:ℝ) 1) :=
    (continuous_const.mul (Complex.continuous_ofReal.pow _)).continuousOn.div
      (continuous_const.sub (Complex.continuous_ofReal.mul continuous_const)).continuousOn hne
  have hg : Continuous g := continuous_const.mul (continuous_id.pow _)
  have hpoint (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) : ‖f t‖ ≤ g t := by
    let r := ‖1-(t:ℂ)*v‖
    have hr : t*‖1-v‖ ≤ r := principal_radial_denominator hv ht.1.le ht.2.le
    rw [show ‖f t‖=‖v‖^(j+2)*t^(j+1)/r by
      simp only [f,r,norm_div,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg ht.1.le]]
    calc
      _ ≤ ‖v‖^(j+2)*t^(j+1)/(t*‖1-v‖) :=
        div_le_div_of_nonneg_left (mul_nonneg (pow_nonneg (norm_nonneg v) _) (pow_nonneg ht.1.le _)) (mul_pos ht.1 hden) hr
      _ = _ := by dsimp only [g]; rw [pow_succ t]; field_simp [ht.1.ne',hden.ne'] <;> ring
  have hi : IntervalIntegrable (fun t => ‖f t‖) volume 0 1 :=
    (by simpa only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using hc.norm :
      ContinuousOn (fun t => ‖f t‖) (uIcc (0:ℝ) 1)).intervalIntegrable
  calc
    ‖principalLogIntegral j v‖ ≤ ∫ t in (0:ℝ)..1, ‖f t‖ :=
      intervalIntegral.norm_integral_le_integral_norm (f:=f) (by norm_num : (0:ℝ) ≤ 1)
    _ ≤ ∫ t in (0:ℝ)..1, g t :=
      intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num) hi (hg.intervalIntegrable ..) hpoint
    _ = _ := by
      dsimp only [g]
      rw [intervalIntegral.integral_const_mul,integral_pow]
      simp only [one_pow,zero_pow (Nat.succ_ne_zero j),sub_zero]
      have hjpos : 0 < (j:ℝ)+1 := by positivity
      field_simp [hden.ne',hjpos.ne'] <;> ring <;> simp

#print axioms principal_log_integral_bound
end OpenMathResearch.LongCycleExcedances
