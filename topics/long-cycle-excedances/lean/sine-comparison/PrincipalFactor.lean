import PrincipalIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Complex.RealDeriv

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Set MeasureTheory

private def logPrefix (m : ℕ) (w : ℂ) : ℂ :=
  ∑ i ∈ Finset.range m, w^(i+1)/((i:ℂ)+1)

private theorem radial_slit {v : ℂ} (hv : ‖v‖ ≤ 1) (hv1 : v ≠ 1)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) : 1-(t:ℂ)*v ∈ Complex.slitPlane := by
  have hre : v.re < 1 := by
    have hle := (le_abs_self v.re).trans ((Complex.abs_re_le_norm v).trans hv)
    apply lt_of_le_of_ne hle
    intro h
    have hsq : ‖v‖^2 ≤ 1^2 := pow_le_pow_left₀ (norm_nonneg v) hv 2
    rw [Complex.sq_norm,Complex.normSq_apply,h] at hsq
    exact hv1 (Complex.ext (by simpa using h) (by simp; nlinarith))
  apply Complex.mem_slitPlane_iff.mpr
  left
  simp only [Complex.sub_re,Complex.one_re,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero]
  rcases eq_or_lt_of_le ht with h|h
  · simp [←h]
  · nlinarith only [mul_lt_mul_of_pos_left hre h,ht1]

private theorem radial_primitive_deriv (m : ℕ) (z v : ℂ)
    (hz : 1-z*v ∈ Complex.slitPlane) :
    HasDerivAt (fun u : ℂ => -Complex.log (1-u*v) - logPrefix m (u*v))
      (v^(m+1)*z^m/(1-z*v)) z := by
  have ha : HasDerivAt (fun u : ℂ => 1-u*v) (-v) z := by
    simpa using (hasDerivAt_const z (1:ℂ)).sub ((hasDerivAt_id z).mul_const v)
  induction m with
  | zero =>
    simpa [logPrefix,div_eq_mul_inv,mul_comm] using
      ((Complex.hasDerivAt_log hz).comp z ha).neg
  | succ m ih =>
    have hc : (m:ℂ)+1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero m)
    have hb : HasDerivAt (fun u : ℂ => (u*v)^(m+1)/((m:ℂ)+1))
        ((z*v)^m*v) z := by
      convert ((((hasDerivAt_id z).mul_const v).pow (m+1)).div_const ((m:ℂ)+1)) using 1
      push_cast
      simp only [Nat.add_sub_cancel,one_mul]
      field_simp
      ring
    convert ih.sub hb using 1
    · funext u
      simp only [logPrefix,Finset.sum_range_succ]
      ring
    · field_simp [Complex.slitPlane_ne_zero hz]
      simp only [pow_succ,mul_pow]
      ring

/-- Evaluate the radial logarithm, including the conjugate-pole endpoint. -/
theorem principal_log_integral_eq (j : ℕ) {v : ℂ} (hv : ‖v‖ ≤ 1) (hv1 : v ≠ 1) :
    principalLogIntegral j v =
    -Complex.log (1-v) - ∑ i ∈ Finset.range (j+1), v^(i+1)/((i:ℂ)+1) := by
  let f (t : ℝ) : ℂ := v^(j+2)*(t:ℂ)^(j+1)/(1-(t:ℂ)*v)
  have hc : ContinuousOn f (uIcc (0:ℝ) 1) := by
    rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact (continuous_const.mul (Complex.continuous_ofReal.pow _)).continuousOn.div
      (continuous_const.sub (Complex.continuous_ofReal.mul continuous_const)).continuousOn
      (fun t ht => Complex.slitPlane_ne_zero (radial_slit hv hv1 ht.1 ht.2))
  have hd (t : ℝ) (ht : t ∈ uIcc (0:ℝ) 1) := by
    rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
    exact (radial_primitive_deriv (j+1) (t:ℂ) v (radial_slit hv hv1 ht.1 ht.2)).comp_ofReal
  have HI := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable
  simpa [principalLogIntegral,f,logPrefix] using HI

theorem principal_exp_integral_eq_factor (j : ℕ) {v : ℂ} (hv : ‖v‖ ≤ 1) (hv1 : v ≠ 1) :
    Complex.exp (principalLogIntegral j v) =
      Complex.exp (-(∑ i ∈ Finset.range (j+1), v^(i+1)/((i:ℂ)+1)))/(1-v) := by
  rw [principal_log_integral_eq j hv hv1,sub_eq_add_neg,Complex.exp_add,
    Complex.exp_neg,Complex.exp_log (sub_ne_zero.mpr hv1.symm)]
  rw [div_eq_mul_inv,mul_comm]

/-- The evaluated numerator in one Lagrange factor of the pole product. -/
theorem principal_lagrange_factor_eq_exp (j : ℕ) {a b : ℂ}
    (hb : b ≠ 0) (hab : a ≠ b) (hunit : ‖a/b‖ ≤ 1) :
    1 + b/(b-a) * (Complex.exp (-(∑ i ∈ Finset.range (j+1),
        (a/b)^(i+1)/((i:ℂ)+1))) - (1-a/b)) =
      Complex.exp (principalLogIntegral j (a/b)) := by
  have hne : a/b ≠ 1 := by
    intro h
    apply hab
    simpa using (div_eq_iff hb).mp h
  rw [principal_exp_integral_eq_factor j hunit hne]
  generalize Complex.exp _ = c
  field_simp [hb,sub_ne_zero.mpr hab.symm,sub_ne_zero.mpr hne.symm]
  ring

#print axioms principal_lagrange_factor_eq_exp
#print axioms principal_log_integral_eq
#print axioms principal_exp_integral_eq_factor
end OpenMathResearch.LongCycleExcedances
