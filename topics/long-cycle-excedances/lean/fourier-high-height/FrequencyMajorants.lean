import FrequencyPrefix
import Mathlib.Algebra.Order.Ring.Abs

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset

private theorem complex_exp_tail (k : ℕ) (hk : 0 < k) (z : ℂ) :
    HasSum (fun j : ℕ => z^(j+k)/((j+k).factorial:ℂ))
      (Complex.exp z-1-expWithoutConstantPrefix k z) := by
  apply (hasSum_nat_add_iff (f := fun j : ℕ => z^j/(j.factorial:ℂ)) k).mpr
  have h := NormedSpace.expSeries_div_hasSum_exp z
  rw [←Complex.exp_eq_exp_ℂ] at h
  have he : (∑ j ∈ range k, z^j/(j.factorial:ℂ)) = expWithoutConstantPrefix k z+1 := by
    have hk' : k-1+1=k := by omega
    nth_rw 1 [←hk']
    rw [sum_range_succ']
    simp [expWithoutConstantPrefix]
  rw [he]
  convert h using 1
  ring

theorem prefix_tail_frequency_majorant (k : ℕ) (hk : 0 < k) (s : ℝ) (z : ℂ) (a : ℕ) :
    ‖logFrequency s z a-prefixFrequency k s z a‖ ≤ highHeightTail k s ‖z‖ a := by
  let A : ℕ := a+1
  let w := (A:ℂ)*z
  have hterm (j : ℕ) : ‖w^(j+k)/((j+k).factorial:ℂ)‖ =
      ((A:ℝ)*‖z‖)^(j+k)/((j+k).factorial:ℝ) := by
    simp [w,norm_div,norm_pow,norm_mul]
  have H := (complex_exp_tail k hk w)
  have hnorm : Summable (fun j : ℕ => ‖w^(j+k)/((j+k).factorial:ℂ)‖) := by
    simp_rw [hterm]
    exact (NormedSpace.expSeries_div_hasSum_exp ((A:ℝ)*‖z‖)).summable.comp_injective
      (add_left_injective k)
  have h := norm_tsum_le_tsum_norm hnorm
  rw [H.tsum_eq] at h
  simp_rw [hterm] at h
  unfold logFrequency prefixFrequency highHeightTail
  rw [←mul_sub,norm_mul,norm_frequency_weight]
  exact mul_le_mul_of_nonneg_left h (by positivity)

private theorem real_pow_diff_le {x y : ℝ} (hy : 0 ≤ y) (hxy : y ≤ x) (j : ℕ) :
    |x^(j+1)-y^(j+1)| ≤ (x-y)*(j+1:ℕ)*x^j := by
  have hx := hy.trans hxy
  simpa only [abs_of_nonneg hx,abs_of_nonneg hy,max_eq_left hxy,Nat.add_sub_cancel,
    abs_of_nonneg (sub_nonneg.mpr hxy)] using
    (abs_pow_sub_pow_le (a:=x) (b:=y) (n:=j+1))

theorem radial_prefix_frequency_majorant (k : ℕ) (s R t : ℝ) {u : ℂ} (hu : ‖u‖=1)
    (ht : 0 ≤ t) (htr : t ≤ R) (a : ℕ) :
    ‖prefixFrequency k s ((R:ℂ)*u) a-prefixFrequency k s ((t:ℂ)*u) a‖ ≤
      (R-t)*radialFrequency k s R a := by
  let A : ℕ := a+1
  have hA : (0:ℝ)<A := by dsimp [A]; positivity
  have hR := ht.trans htr
  have hA0 : (A:ℝ)≠0 := hA.ne'
  have hpow (j : ℕ) :
      ‖((A:ℂ)*((R:ℂ)*u))^(j+1)/((j+1).factorial:ℂ)
          -((A:ℂ)*((t:ℂ)*u))^(j+1)/((j+1).factorial:ℂ)‖ ≤
      (A:ℝ)*(R-t)*(((A:ℝ)*R)^j/(j.factorial:ℝ)) := by
    have heq : ((A:ℂ)*((R:ℂ)*u))^(j+1) - ((A:ℂ)*((t:ℂ)*u))^(j+1) =
        (((((A:ℝ)*R)^(j+1)-((A:ℝ)*t)^(j+1)):ℝ):ℂ)*u^(j+1) := by
      push_cast
      rw [←mul_assoc, ←mul_assoc]
      simp only [mul_pow, sub_mul]
    rw [←sub_div, heq, norm_div,norm_mul,norm_pow,hu,one_pow,mul_one,Complex.norm_real,
      Real.norm_eq_abs,Complex.norm_natCast]
    have h := real_pow_diff_le (mul_nonneg hA.le ht) (mul_le_mul_of_nonneg_left htr hA.le) j
    apply (div_le_div_of_nonneg_right h (by positivity)).trans_eq
    rw [Nat.factorial_succ]
    push_cast
    have hj : (j.factorial:ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
    have hsucc : (j:ℝ)+1 ≠ 0 := by positivity
    field_simp [hj, hsucc]
    ring
  unfold prefixFrequency radialFrequency expWithoutConstantPrefix
  rw [←mul_sub, ←sum_sub_distrib, norm_mul, norm_frequency_weight]
  apply (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)).trans
  have hs : (∑ j ∈ range (k-1),
    ‖((A:ℂ)*((R:ℂ)*u))^(j+1)/((j+1).factorial:ℂ) -
      ((A:ℂ)*((t:ℂ)*u))^(j+1)/((j+1).factorial:ℂ)‖) ≤
      (A:ℝ)*(R-t)*(∑ j ∈ range (k-1), ((A:ℝ)*R)^j/(j.factorial:ℝ)) := by
    rw [mul_sum]
    exact sum_le_sum (fun j _ => hpow j)
  apply (mul_le_mul_of_nonneg_left hs (by positivity)).trans_eq
  change (Real.exp (-(A:ℝ)*s)/(A:ℝ))*((A:ℝ)*(R-t)*
    (∑ j ∈ range (k-1), ((A:ℝ)*R)^j/(j.factorial:ℝ))) = _
  dsimp [A]
  field_simp
  ring

#print axioms prefix_tail_frequency_majorant
#print axioms radial_prefix_frequency_majorant
end OpenMathResearch.LongCycleExcedances
