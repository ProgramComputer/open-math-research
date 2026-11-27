import FourierDiskConvergence
import NumeratorLogDefinitions

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Complex Real Finset Filter
open scoped Topology

private theorem normalized_radius_pos (s : ℝ) : 0 < numeratorRadius s := Real.sqrt_pos.mpr (by positivity)

private theorem normalized_pole_radius_le (s : ℝ) (l : ℤ) :
    numeratorRadius s ≤ ‖fourierRowPole s l‖ := by
  have ha : 1 ≤ |2*(l:ℝ)+1| := by
    rcases le_or_gt 0 l with h | h
    · apply le_abs.mpr (Or.inl ?_)
      have : 0 ≤ (l:ℝ) := by exact_mod_cast h
      linarith
    · apply le_abs.mpr (Or.inr ?_)
      have : (l:ℝ) ≤ -1 := by exact_mod_cast (show l ≤ -1 by omega)
      linarith
  have hrad := Real.sq_sqrt (by positivity : 0 ≤ s^2+π^2)
  have he : ‖fourierRowPole s l‖^2 = s^2+((2*(l:ℝ)+1)*π)^2 := by
    rw [Complex.sq_norm]
    simp [fourierRowPole,Complex.normSq_apply,Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,pow_two]
  have h1 : 1 ≤ (2*(l:ℝ)+1)^2 := by nlinarith [sq_abs (2*(l:ℝ)+1),sq_nonneg (|2*(l:ℝ)+1|-1)]
  have h2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg π)
  rw [mul_pow] at he
  dsimp [numeratorRadius]
  nlinarith [norm_nonneg (fourierRowPole s l)]

private theorem numerator_series_summable (s : ℝ)
    (hS : Summable (fun i => 1/‖fourierRowPole s i‖^2))
    {z : ℂ} (hz : ‖z‖ < 1) : Summable (fun j => numeratorLogSeries s j*z^j) := by
  let r := numeratorRadius s
  let Z := fun i => (r:ℂ)/numeratorPole s i
  have hr := normalized_radius_pos s
  have hs : Summable (fun i => ‖Z i‖^2) := by
    have he (i) : ‖Z i‖^2 = r^2*(1/‖fourierRowPole s i‖^2) := by
      dsimp only [Z]
      rw [norm_div,div_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr,mul_one_div]
      rfl
    simpa only [he] using hS.mul_left (r^2)
  let M := ∑' i, ‖Z i‖^2
  apply Summable.of_norm_bounded_eventually _ ((summable_geometric_of_lt_one (norm_nonneg z) hz).mul_left M)
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_ge_atTop 2] with j hj
  have hd (i) : ‖Z i^j‖ ≤ ‖Z i‖^2 := by
    have h1 : ‖Z i‖ ≤ 1 := by
      dsimp only [Z]
      rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]
      exact (div_le_one (hr.trans_le (normalized_pole_radius_le s i))).mpr (normalized_pole_radius_le s i)
    rw [norm_pow]
    exact pow_le_pow_of_le_one (norm_nonneg _) h1 hj
  have hsm := Summable.of_nonneg_of_le (fun i => norm_nonneg _) hd hs
  have hb : ‖∑' i, Z i^j‖ ≤ M := (norm_tsum_le_tsum_norm hsm).trans (hsm.tsum_le_tsum hd hs)
  have hc : ‖numeratorLogSeries s j‖ ≤ M := by
    rw [numeratorLogSeries,if_neg (by omega),if_neg (by omega),norm_div,norm_neg,Complex.norm_natCast]
    exact (div_le_self (norm_nonneg _) (by exact_mod_cast (show 1 ≤ j by omega))).trans hb
  rw [norm_mul,norm_pow]
  exact mul_le_mul_of_nonneg_right hc (by positivity)

theorem numerator_series_hasSum_disk_log {s : ℝ} (hs : 0 ≤ s)
    (hS : Summable (fun i => 1/‖fourierRowPole s i‖^2))
    (hreal : ∀ x : ℝ, x < s → inverseSquarePoleSum (fourierRowPole s) (x:ℂ) =
      -Complex.exp ((x:ℂ)-s)/(1+Complex.exp ((x:ℂ)-s))^2)
    {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun j : ℕ => numeratorLogSeries s j*z^j) (diskLogisticLog s ((numeratorRadius s:ℂ)*z)) := by
  let r := numeratorRadius s
  let b := fun j : ℕ => numeratorLogSeries s j/(r:ℂ)^j
  have hr := normalized_radius_pos s
  have hrc : (r:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hb1 : b 1 = Complex.exp (-(s:ℂ))/(1+Complex.exp (-(s:ℂ))) := by
    have hden : (1:ℂ)+Complex.exp (s:ℂ) ≠ 0 := by
      rw [←Complex.ofReal_exp,←Complex.ofReal_one,←Complex.ofReal_add]
      exact Complex.ofReal_ne_zero.mpr (by positivity)
    dsimp [b,numeratorLogSeries]
    rw [Complex.exp_neg,←Complex.ofReal_exp]
    push_cast
    field_simp [hrc,Complex.exp_ne_zero,hden]
    rw [add_comm (Complex.exp (s:ℂ)) 1]
    field_simp [hrc,hden]
    rfl
  have hb (j : ℕ) : b (j+2)*((j+2:ℕ):ℂ) = -(∑' i, (1:ℂ)/fourierRowPole s i^(j+2)) := by
    have hJ : ((j+2:ℕ):ℂ) ≠ 0 := by exact_mod_cast (show j+2 ≠ 0 by omega)
    have he : (∑' i, ((r:ℂ)/numeratorPole s i)^(j+2)) =
        (r:ℂ)^(j+2)*(∑' i, (1:ℂ)/fourierRowPole s i^(j+2)) := by
      rw [←tsum_mul_left]
      apply tsum_congr
      intro i
      rw [div_pow,mul_one_div]
      rfl
    change numeratorLogSeries s (j+2)/(r:ℂ)^(j+2)*_ = _
    rw [numeratorLogSeries,if_neg (by omega),if_neg (by omega),he]
    push_cast at hJ
    field_simp [hrc,hJ]
    ring
  have hz' : ‖(r:ℂ)*z‖ < r := by rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]; nlinarith
  have ht := disk_finite_fourier_log_tendsto hs (Real.sq_sqrt (by positivity : 0 ≤ s^2+π^2))
    (normalized_pole_radius_le s) hS hreal b hb1 hb hz'
  apply (numerator_series_summable s hS hz).hasSum_iff_tendsto_nat.mpr
  apply (tendsto_add_atTop_iff_nat 2).mp
  convert ht using 1
  funext m
  rw [show m+2=m+1+1 by omega,sum_range_succ']
  have hz0 : numeratorLogSeries s 0 = 0 := by simp [numeratorLogSeries]
  simp only [hz0,pow_zero,zero_mul,add_zero]
  unfold finiteFourierLog
  apply sum_congr rfl
  intro j _
  change numeratorLogSeries s (j+1)*z^(j+1) = b (j+1)*((r:ℂ)*z)^(j+1)
  rw [mul_pow]
  dsimp only [b]
  field_simp [hrc]
  ring

#print axioms numerator_series_hasSum_disk_log
end OpenMathResearch.LongCycleExcedances
