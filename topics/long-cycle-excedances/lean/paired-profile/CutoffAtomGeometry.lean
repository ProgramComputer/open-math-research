import NonprincipalValueCost

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset Real

theorem atom_bin_interval {n k lower upper b t : ℕ} (hk : 5 < k) (hl : 0 < lower)
    (hlo : lower*k ≤ n) (hhi : n ≤ upper*k) (he : t+k=n+1)
    (ht₁ : 4*t ≤ k*b) (ht₂ : k*b ≤ 5*t) :
    4*(lower-1) < b ∧ b+5 ≤ 5*upper := by
  have hl' : (lower-1).succ=lower := by omega
  have hh : (lower-1)*k+k=lower*k := by rw [←Nat.succ_mul,hl']
  constructor
  · apply Nat.lt_of_mul_lt_mul_left (a:=k)
    calc
      k*(4*(lower-1)) = 4*((lower-1)*k) := by ring
      _ < 4*t := by omega
      _ ≤ k*b := ht₁
  · apply Nat.le_of_lt_succ
    apply Nat.lt_of_mul_lt_mul_left (a:=k)
    calc
      k*(b+5) ≤ 5*(n+1) := by nlinarith only [he,ht₂]
      _ < k*(5*upper).succ := by rw [Nat.mul_succ]; nlinarith only [hhi,hk]

theorem atom_kernel_on_bin {n k lower upper b t : ℕ} (hk : 192 ≤ k) (hl : 0 < lower)
    (hlo : lower*k ≤ n) (hhi : n ≤ upper*k) (he : t+k=n+1) (ht : 4*t ≤ k*b)
    {θ : ℝ} (hS : 0 < sin θ) (hU : 6/5 ≤ (n:ℝ)*sin θ^2) (a : ℤ) :
    ‖(pairedPoleDenom (cos θ) (sin θ) a)⁻¹‖^k ≤ valueKernel lower upper b a := by
  have hn : 0 < n := (Nat.mul_pos hl (by omega : 0 < k)).trans_le hlo
  have hX : 0 < upper := by
    by_contra! hh
    simp [show upper=0 by omega] at hhi
    omega
  have hlr : 0 < (lower:ℝ) := by exact_mod_cast hl
  have hr : 0 < (n:ℝ) := by exact_mod_cast hn
  have hxr : 0 < (upper:ℝ) := by exact_mod_cast hX
  have lower_bound : (lower:ℝ)*k ≤ n := by exact_mod_cast hlo
  have upper_bound : (n:ℝ) ≤ upper*k := by exact_mod_cast hhi
  have htr : 4*(t:ℝ) ≤ k*b := by exact_mod_cast ht
  have hrow : (t:ℝ)+k=n+1 := by exact_mod_cast he
  have hfrac : valueBinFraction lower upper b ≤ (k:ℝ)/n := by
    rw [valueBinFraction,max_le_iff]
    constructor
    · apply (div_le_div_iff₀ hxr hr).mpr
      linarith only [upper_bound]
    · have hx : (4*(lower:ℝ))*t ≤ (n:ℝ)*b := by
        nlinarith only [mul_nonneg hlr.le (sub_nonneg.mpr htr),
          mul_nonneg (Nat.cast_nonneg b : (0:ℝ) ≤ b) (sub_nonneg.mpr lower_bound)]
      have hratio : (t:ℝ) ≤ (b/(4*(lower:ℝ)))*(n:ℝ) := by
        rw [div_mul_eq_mul_div,le_div_iff₀ (by positivity)]
        nlinarith only [hx]
      apply (le_div_iff₀ hr).mpr
      nlinarith only [hrow,hratio]
  apply primitive_angular_bernoulli_kernel hn hk a hS _ hfrac (by norm_num) hU
  exact le_trans (by positivity) (le_max_left ..)

theorem atom_angle_scale {k n upper : ℕ} (hk : 0 < k) (hhi : n ≤ upper*k)
    {S A₀ U : ℝ} (hS : 0 < S) (hA : 0 ≤ A₀) (hU : 0 < U) (hUs : U ≤ (n:ℝ)*S^2) :
    (A₀/((k:ℝ)*S))/S ≤ A₀*upper/U := by
  have hkr : 0 < (k:ℝ) := by exact_mod_cast hk
  have hh : (n:ℝ) ≤ upper*k := by exact_mod_cast hhi
  have hprod := mul_le_mul_of_nonneg_right hh (sq_nonneg S)
  rw [div_div,div_le_div_iff₀ (by positivity) hU]
  nlinarith only [mul_le_mul_of_nonneg_left (hUs.trans hprod) hA]

#print axioms atom_bin_interval
#print axioms atom_kernel_on_bin
#print axioms atom_angle_scale
end OpenMathResearch.LongCycleExcedances
