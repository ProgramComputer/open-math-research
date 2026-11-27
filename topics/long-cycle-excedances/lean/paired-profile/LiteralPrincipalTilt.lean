import PrincipalRowKernel
import TiltedNumeratorMass
import BinCostTail

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset Polynomial Real CycleProbability

theorem occupied_primitive_below {k t : ℕ} {d : ℕ→ℝ} (hd : Spec k d) (hk : 0 < k) (ht : t < k)
    (C S : ℝ) (a q : ℤ) : PowerSeries.coeff (R := ℂ) t (occupiedPrimitive k C S a q)=0 := by
  have he := coeff_cutoffCycleNumerator_eq_of_spec (s:=t) hd hk
  unfold cutoffCycleNumerator at he
  rw [numeratorDiff_below d ht] at he
  simp only [Complex.ofReal_zero] at he
  rw [occupiedPrimitive,PowerSeries.coeff_C_mul,PowerSeries.coeff_rescale,he,mul_zero,mul_zero]

theorem principal_primitive_norm_majorant {k s : ℕ} {d : ℕ→ℝ} (hd : Spec k d)
    (hk : 0 < k) (hs : k ≤ s) {θ : ℝ} (hS : 0 < sin θ) {q : ℤ} (hq : q≠0) :
    ‖PowerSeries.coeff (R := ℂ) s (occupiedPrimitive k (cos θ) (sin θ) 0 q)‖ ≤
      principalRowKernel k θ q*((k:ℝ)*|numeratorDiff k d s|) := by
  let z := (pairedPoleDenom (cos θ) (sin θ) q)⁻¹
  have hr : ‖z‖ ≤ 1 := by
    have he := principal_pole_ratio_norm_le (cos θ) hS.ne' q
    rw [div_eq_mul_inv,norm_mul,principal_angular_unit,one_mul] at he
    exact he
  have hpow := pow_le_pow_of_le_one (norm_nonneg z) hr (show k-1 ≤ s-1 by omega)
  have hgap : ‖pairedPoleDenom (cos θ) (sin θ) q - pairedPoleDenom (cos θ) (sin θ) 0‖ =
      2*|(q:ℝ)| *sin θ := by
    rw [pairedPoleDenom_sub]
    simp only [Int.cast_zero,sub_zero,norm_mul,Complex.norm_I,one_mul,Complex.norm_intCast,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos hS]
    norm_num
  have hb := coeff_cutoffCycleNumerator_eq_of_spec (s:=s) hd hk
  unfold cutoffCycleNumerator at hb
  rw [literalPrimitive_norm_formula hk hs (cos θ) hS.ne',norm_mul,norm_div,norm_pow,hgap,hb,
    Complex.norm_real,Real.norm_eq_abs]
  have hq' : 0 < |(q:ℝ)| := abs_pos.mpr (by exact_mod_cast hq)
  have hk' : 0 < (k:ℝ) := by exact_mod_cast hk
  calc
    _ ≤ ‖z‖^(k-1)/(2*|(q:ℝ)| *sin θ)*|numeratorDiff k d s| := by
      exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hpow (by positivity)) (abs_nonneg _)
    _ = _ := by
      unfold principalRowKernel
      rw [show 2*|(q:ℝ)| *((k:ℝ)*sin θ)=(2*|(q:ℝ)| *sin θ)*(k:ℝ) by ring]
      have cancel (x y v : ℝ) : x/y*v=x/(y*(k:ℝ))*((k:ℝ)*v) := by
        rw [div_mul_eq_div_div x y (k:ℝ),←mul_assoc,div_mul_cancel₀ _ hk'.ne']
      exact cancel _ _ _

private theorem eval_forgotten_mark (k N : ℕ) (c : ℕ→ℝ) (base : ℝ) :
    (forgetDegree (markDegreeBin k N c)).eval base =
       ∑ s ∈ Icc k N, c s*base^degreeBin k s := by
  rw [forgetDegree,markDegreeBin]
  simp only [Polynomial.map_sum,map_monomial,eval_finsetSum,eval_monomial]
  simp

/-- The product generating the absolute bin masses has bounded exponential tilt
at the principal pole, uniformly in both the pole window and degree truncation. -/
theorem literal_principal_tilt {n j : ℕ} {θ : ℝ} {d : ℕ→ℝ} (hd : Spec (j+2) d)
    (hn : 10000 ≤ n) (hkn : n ≤ 48*(j+2)) (hS : 0 < sin θ) (hangle : 6/5 ≤ (n:ℝ)*sin θ^2)
    (A : Finset ℤ) (N : ℕ) :
    (binFull (A.erase 0) (fun q =>
      forgetDegree (literalMarkedPrimitive (j+2) N (cos θ) (sin θ) 0 q))).eval (9/8) ≤ exp 14 := by
  let k := j+2
  have hk : 2 ≤ k := by dsimp [k]; omega
  let f (s:ℕ) := (k:ℝ)*|numeratorDiff k d s| *(9/8:ℝ)^degreeBin k s
  let R := principalRowKernel k θ
  have hR (q:ℤ) : 0 ≤ R q := by dsimp [R,principalRowKernel]; positivity
  apply product_tilt_cost_bound
  · intro q _
    unfold literalMarkedPrimitive
    rw [eval_forgotten_mark]
    exact sum_nonneg (fun _ _ => by positivity)
  have hsingle (q : ℤ) (hq : q ∈ A.erase 0) :
      (forgetDegree (literalMarkedPrimitive k N (cos θ) (sin θ) 0 q)).eval (9/8) ≤
        R q*(∑ s ∈ Icc k N, f s) := by
    rw [literalMarkedPrimitive,eval_forgotten_mark,mul_sum]
    apply sum_le_sum
    intro s hs
    rw [←mul_assoc]
    exact mul_le_mul_of_nonneg_right (principal_primitive_norm_majorant hd (by omega) (mem_Icc.mp hs).1 hS
      (ne_of_mem_erase hq)) (by positivity)
  apply (sum_le_sum hsingle).trans
  rw [←sum_mul]
  have hsum := finite_principal_row_kernel hn hkn hS hangle (A.erase 0) (by simp)
  have hmass := tilted_numerator_mass hd hk N
  have h := mul_le_mul hsum hmass.le (sum_nonneg (fun _ _ => by positivity))
    (by norm_num : (0:ℝ) ≤ 4/5)
  exact h.trans (by norm_num)

#print axioms principal_primitive_norm_majorant
#print axioms literal_principal_tilt
end OpenMathResearch.LongCycleExcedances
