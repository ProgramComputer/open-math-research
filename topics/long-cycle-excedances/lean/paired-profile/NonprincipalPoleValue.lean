import PrincipalRowKernel
import CenteredBinGeometry

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real CycleProbability

/-- Exact adjacent sine multiplier before taking an absolute value. -/
theorem angular_pole_sine_difference (v θ : ℝ) (q : ℤ) :
    pairedPoleDenom (cos θ) (sin θ) q*(sin (v+θ):ℂ)-(sin v:ℂ) =
      (sin θ:ℂ)*((cos (v+θ):ℂ)+Complex.I*(primitiveOddNumber q:ℂ)*(sin (v+θ):ℂ)) := by
  have hdiff := Real.sin_sub (v+θ) θ
  rw [add_sub_cancel_right] at hdiff
  have hre : cos θ*sin (v+θ)-sin v=sin θ*cos (v+θ) := by linarith
  have hc := congrArg Complex.ofReal hre
  simp only [Complex.ofReal_sub,Complex.ofReal_mul] at hc
  unfold pairedPoleDenom primitiveOddNumber
  push_cast at hc ⊢
  linear_combination hc

theorem angular_pole_sine_norm (v θ : ℝ) (hS : 0 < sin θ) (q : ℤ) :
    ‖pairedPoleDenom (cos θ) (sin θ) q*(sin (v+θ):ℂ)-(sin v:ℂ)‖ ≤
        sin θ*|primitiveOddNumber q| := by
  rw [angular_pole_sine_difference,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hS]
  apply mul_le_mul_of_nonneg_left _ hS.le
  let a := primitiveOddNumber q
  let x := v+θ
  have ha := primitive_odd_abs_ge_one q
  have ha2 : 1 ≤ a^2 := by simpa [a] using pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) ha 2
  have hsq : ‖(cos x:ℂ)+Complex.I*(a:ℂ)*(sin x:ℂ)‖^2 ≤ |a|^2 := by
    rw [Complex.sq_norm,Complex.normSq_apply,sq_abs]
    simp only [Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,
      Complex.ofReal_im,Complex.I_re,Complex.I_im,zero_mul,one_mul,mul_zero,add_zero,sub_zero,
      zero_add]
    have hid := sin_sq_add_cos_sq x
    nlinarith only [mul_nonneg (sub_nonneg.mpr ha2) (sq_nonneg (cos x)),
      congrArg (fun t:ℝ => a^2*t) hid]
  exact (sq_le_sq₀ (norm_nonneg _) (abs_nonneg _)).mp hsq

def valueBinFraction (lower upper b : ℕ) : ℝ := max (1/(upper:ℝ)) (1-(b:ℝ)/(4*lower))
def valueBinWeight (lower b : ℕ) : ℝ := if b+8 ≤ 4*lower then 4/7 else 1

private theorem value_fraction {k n lower upper b t : ℕ} (hk : 0 < k) (hl : 0 < lower)
    (hX : n ≤ upper*k) (hlo : lower*k ≤ n) (ht : 4*t ≤ k*b) (hrow : k ≤ n-t) :
    valueBinFraction lower upper b ≤ ((n+1-t:ℕ):ℝ)/n := by
  have hn : 0 < n := (Nat.mul_pos hl hk).trans_le hlo
  have hu : 0 < upper := by
    by_contra! h
    rw [show upper=0 by omega,Nat.zero_mul] at hX
    omega
  have ht' : t ≤ n := by omega
  have hs : (n+1-t:ℕ)=n-t+1 := by omega
  have hnr : 0 < (n:ℝ) := by exact_mod_cast hn
  have hur : 0 < (upper:ℝ) := by exact_mod_cast hu
  have hlr : 0 < (lower:ℝ) := by exact_mod_cast hl
  have hXr : (n:ℝ) ≤ upper*k := by exact_mod_cast hX
  have hlor : (lower:ℝ)*k ≤ n := by exact_mod_cast hlo
  have htr : 4*(t:ℝ) ≤ k*b := by exact_mod_cast ht
  have hkr : (k:ℝ) ≤ n-t := by
    have hh : (k:ℝ) ≤ (n-t:ℕ) := by exact_mod_cast hrow
    rwa [Nat.cast_sub ht'] at hh
  rw [valueBinFraction,max_le_iff,hs,Nat.cast_add,Nat.cast_one,Nat.cast_sub ht']
  constructor
  · apply (div_le_div_iff₀ hur hnr).mpr
    nlinarith only [hXr,mul_nonneg hur.le (sub_nonneg.mpr hkr),hur]
  · have hx : 4*(lower:ℝ)*t ≤ n*b := by
      nlinarith only [mul_nonneg hlr.le (sub_nonneg.mpr htr),
        mul_nonneg (Nat.cast_nonneg b : (0:ℝ) ≤ b) (sub_nonneg.mpr hlor)]
    apply (le_div_iff₀ hnr).mpr
    have hh : ((b:ℝ)/(4*lower))*n ≥ t := by
      rw [div_mul_eq_mul_div,ge_iff_le,le_div_iff₀ (by positivity)]
      nlinarith only [hx]
    linarith

theorem value_kernel_on_bin {k n lower upper b t : ℕ} (hk : 192 ≤ k) (hl : 0 < lower)
    (hX : n ≤ upper*k) (hlo : lower*k ≤ n) (ht : 4*t ≤ k*b) (hrow : k ≤ n-t)
    {θ : ℝ} (hS : 0 < sin θ) (hangle : 6/5 ≤ (n:ℝ)*sin θ^2) (q:ℤ) :
    ‖(pairedPoleDenom (cos θ) (sin θ) q)⁻¹‖^(n+1-t) ≤
      ((1+valueBinFraction lower upper b*(6/5)/192*(primitiveOddNumber q^2-1))^96)⁻¹ := by
  have hn : 0 < n := (Nat.mul_pos hl (by omega : 0 < k)).trans_le hlo
  exact primitive_angular_bernoulli_kernel hn (by omega : 192 ≤ n+1-t) q hS
    (le_trans (by positivity) (le_max_left _ _)) (value_fraction (by omega) hl hX hlo ht hrow)
    (by norm_num) hangle

theorem value_probability_on_bin {k n lower b t : ℕ} {d : ℕ→ℝ} (hd : Spec k d)
    (hk : 100 ≤ k) (hlo : lower*k ≤ n) (ht : 4*t ≤ k*b) (hrow : k ≤ n-t) :
    (k:ℝ)*|cutoffWeight k d (n-t)| ≤ valueBinWeight lower b := by
  have hp := lower_half hd (by omega) (n-t) hrow
  have hk' : 0 < (k:ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hpos : 0 ≤ d (n-t) := by nlinarith
  rw [cutoffWeight,if_pos hrow,abs_of_nonneg hpos,valueBinWeight]
  split
  next hb =>
    apply upper47 hd hk
    have h4 := Nat.mul_le_mul_left 4 hlo
    have hk4 := Nat.mul_le_mul_left k hb
    have : t+2*k ≤ n := by nlinarith
    omega
  next =>
    have h := (hd.reciprocal_bounds (by omega) hrow).2
    simpa only [mul_comm] using (le_div_iff₀ hk').mp h

#print axioms angular_pole_sine_difference
#print axioms angular_pole_sine_norm
#print axioms value_kernel_on_bin
#print axioms value_probability_on_bin
end OpenMathResearch.LongCycleExcedances
