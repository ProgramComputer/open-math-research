import FourierUniformDecay

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real

/-- The scaled old and adjacent kernel bounds share one budget on x≥48,
including both corrections from the signed Fourier identity. -/
theorem scaled_fourier_kernel_bounds {x s₀ s₁ t₀ t₁ : ℝ} (hx : 48 ≤ x)
    (h₀ : 0 ≤ s₀) (h₁ : 0 ≤ s₁)
    (hs₀ : s₀ ≤ 9*x) (hs₁ : s₁ ≤ 12*x*Real.sqrt x)
    (ht₀ : t₀ ≤ 10*x*Real.sqrt x) (ht₁ : t₁ ≤ 13*x^2) :
    s₀^2+t₀ ≤ 83*x^2 ∧ s₀*s₁+t₁ ≤ 110*x^2*Real.sqrt x ∧
    s₀*s₁+t₁+((9/10)*x/(x-2)+1/50)*(s₀^2+t₀) ≤ x^2*(110*Real.sqrt x+80) := by
  have hx0 : 0 < x := by linarith
  have hs := Real.sq_sqrt hx0.le
  have hs1 : 13/2 ≤ Real.sqrt x := (sq_le_sq₀ (by norm_num) (Real.sqrt_nonneg _)).mp
    (by nlinarith only [hs,hx])
  have h10 : 10*Real.sqrt x ≤ 2*x := by
    nlinarith only [hs,mul_le_mul_of_nonneg_right hs1 (Real.sqrt_nonneg x)]
  have hold : s₀^2+t₀ ≤ 83*x^2 := by
    nlinarith only [pow_le_pow_left₀ h₀ hs₀ 2, ht₀, mul_le_mul_of_nonneg_left h10 hx0.le]
  have hnew : s₀*s₁+t₁ ≤ 110*x^2*Real.sqrt x := by
    have hh := mul_le_mul hs₀ hs₁ h₁ (by positivity)
    nlinarith only [hh,ht₁,mul_le_mul_of_nonneg_left hs1 (sq_nonneg x)]
  have hden : 0 < x-2 := by linarith
  have hcor : (9/10)*x/(x-2)+1/50 ≤ 80/83 := by
    apply (le_sub_iff_add_le).mp
    apply (div_le_iff₀ hden).mpr
    linarith
  have hc0 : 0 ≤ (9/10)*x/(x-2)+1/50 := by positivity
  have hcorrect := mul_le_mul_of_nonneg_left hold hc0
  have hlast := mul_le_mul_of_nonneg_right hcor (by positivity : 0 ≤ 83*x^2)
  exact ⟨hold,hnew,by nlinarith only [hnew,hcorrect.trans hlast]⟩

#print axioms scaled_fourier_kernel_bounds
end OpenMathResearch.LongCycleExcedances
