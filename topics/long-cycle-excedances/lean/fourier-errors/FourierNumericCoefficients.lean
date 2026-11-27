import FourierNormalizedError
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real

private theorem norm_frequency_product {j k : ℤ} (hk : 0 ≤ k) (hj : k ≤ j) (z : ℂ) :
    ‖((j-k:ℤ):ℂ)*(j:ℂ)*z‖ = (j:ℝ)*((j:ℝ)-(k:ℝ))*‖z‖ := by
  have hj' : (0:ℝ) ≤ (j:ℝ) := by exact_mod_cast hk.trans hj
  have hjk : (0:ℝ) ≤ ((j-k:ℤ):ℝ) := by exact_mod_cast (sub_nonneg.mpr hj)
  rw [norm_mul,norm_mul,Complex.norm_intCast,Complex.norm_intCast,abs_of_nonneg hj',
    abs_of_nonneg hjk,Int.cast_sub]
  ring

/-- Apply the scalar reduction directly to integer-frequency Fourier coefficients,
preserving the lower shifted frequency and the signed adjacent difference. -/
theorem numerical_fourier_coefficient_pair {n k : ℤ} (hk : 0 < k) {x : ℝ} (hx : 48 ≤ x)
    (hn : (n:ℝ)=x*(k:ℝ)) (F : ℤ → ℂ) (a A C : ℂ)
    {S M r T decay B O J : ℝ} (hS : 0 < S)
    (hr : 0 ≤ r) (hT : 0 < T) (hO : 0 ≤ O) (hJ : 0 ≤ J)
    (hdec : decay ≤ Real.exp (-(19/20)*x))
    (hamp : r*M/T ≤ (k:ℝ)*Real.exp (2997/100)*B)
    (hB₁ : x ≤ 100 → B ≤ 457) (hB₂ : 100 ≤ x → B ≤ (46/100)*x*Real.sqrt x)
    (hold : O ≤ 83*x^2) (hnew : J+((9/10)*x/(x-2)+1/50)*O ≤ x^2*(110*Real.sqrt x+80))
    (hA : ‖A‖ ≤ (9/10)*(n:ℝ)*S) (ha : ‖a‖ ≤ (1/50)*(n:ℝ)*S)
    (hbase : ∀ j : ℤ, ‖((j-k:ℤ):ℂ)*(j:ℂ)*F j‖ ≤ M*(k:ℝ)*O)
    (hadj : ‖((n-k:ℤ):ℂ)*(n:ℂ)*(a*F (n+1)-C*F n)‖ ≤
      M*S*(k:ℝ)*J+‖((n-k:ℤ):ℂ)*A*F (n+1-k)‖+‖((n-k:ℤ):ℂ)*a*F (n+1)‖) :
    (r/(2*T))*decay*‖F n‖ < 1/25 ∧
      (r/(2*T))*decay*‖a*F (n+1)-C*F n‖ < S/25 := by
  have hk' : (0:ℝ)<k := by exact_mod_cast hk
  have h2 : 2*k ≤ n := by
    have hh := mul_le_mul_of_nonneg_right hx hk'.le
    exact_mod_cast (show 2*(k:ℝ) ≤ (n:ℝ) by linarith only [hh,hn,hk'])
  have hnk : k ≤ n := by omega
  have hx0 : 0 < x := by linarith
  have hbase' (j : ℤ) (hj : k ≤ j) : (j:ℝ)*((j:ℝ)-(k:ℝ))*‖F j‖ ≤ M*(k:ℝ)*O := by
    simpa only [norm_frequency_product hk.le hj] using hbase j
  have habs : 0 ≤ ((n-k:ℤ):ℝ) := by exact_mod_cast (sub_nonneg.mpr hnk)
  have hnA (z u : ℂ) : ‖((n-k:ℤ):ℂ)*z*u‖ = ((n:ℝ)-(k:ℝ))*‖z‖*‖u‖ := by
    rw [norm_mul,norm_mul,Complex.norm_intCast,abs_of_nonneg habs,Int.cast_sub]
  have ha0 := hadj
  rw [norm_frequency_product hk.le hnk,hnA,hnA] at ha0
  have hf₀ := hbase' (n+1-k) (by omega)
  have hg₀ := hbase' (n+1) (by omega)
  push_cast at hf₀ hg₀
  have hf : ((n:ℝ)+1-k)*((n:ℝ)+1-2*k)*‖F (n+1-k)‖ ≤ M*k*O := by
    simpa only [show (n:ℝ)+1-k-k=(n:ℝ)+1-2*k by ring] using hf₀
  have HA := absorb_adjacent_fourier_corrections hx hk' hn hS.le
    (norm_nonneg _) (norm_nonneg _) hA ha hf hg₀ ha0
  have hxd : 0 < x-2 := by linarith
  have hcor : 0 ≤ (9/10)*x/(x-2)+1/50 := by positivity
  have hroot : 1 ≤ Real.sqrt x := (sq_le_sq₀ (by norm_num) (Real.sqrt_nonneg _)).mp
    (by nlinarith only [hx,Real.sq_sqrt hx0.le])
  have hbudget : O ≤ x^2*(110*Real.sqrt x+80) := by
    apply hold.trans
    have hh := mul_le_mul_of_nonneg_left (show (83:ℝ) ≤ 110*Real.sqrt x+80 by linarith) (sq_nonneg x)
    linarith only [hh]
  constructor
  · exact normalized_circle_error hx hk' hn hr hT zero_lt_one (norm_nonneg _) hO
      (by simpa only [mul_one] using hbase' n hnk) hamp hdec hB₁ hB₂ hbudget
  · exact normalized_circle_error hx hk' hn hr hT hS (norm_nonneg _) (add_nonneg hJ (mul_nonneg hcor hO))
      HA hamp hdec hB₁ hB₂ hnew

#print axioms numerical_fourier_coefficient_pair
end OpenMathResearch.LongCycleExcedances
