import FourierLogarithmicGap

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real Complex

/-- Zero is a nearest exponential period throughout the principal closed strip. -/
theorem principal_strip_exponential_gap (v : ℂ) (hv : |v.im| ≤ π) :
    ‖v‖/(1+‖v‖) ≤ ‖1-Complex.exp v‖ := by
  apply exponential_period_gap v (norm_nonneg _)
  intro l
  have him : |v.im| ≤ |v.im - (l:ℝ)*(2*π)| := by
    rcases lt_trichotomy l 0 with h | h | h
    · have hi : (l:ℝ) ≤ -1 := by exact_mod_cast (show l ≤ -1 by omega)
      have hl := mul_le_mul_of_nonneg_right hi (by positivity : 0 ≤ 2*π)
      have hh : |v.im| ≤ v.im - (l:ℝ)*(2*π) := by linarith [(abs_le.mp hv).1]
      exact hh.trans (le_abs_self _)
    · simp [h]
    · have hi : 1 ≤ (l:ℝ) := by exact_mod_cast (show 1 ≤ l by omega)
      have hl := mul_le_mul_of_nonneg_right hi (by positivity : 0 ≤ 2*π)
      have hh : |v.im| ≤ -(v.im - (l:ℝ)*(2*π)) := by linarith [(abs_le.mp hv).2]
      exact hh.trans (neg_le_abs _)
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [Complex.sq_norm,Complex.sq_norm,Complex.normSq_apply,Complex.normSq_apply]
  have he : (v-(l:ℂ)*(2*π*I)).re=v.re ∧ (v-(l:ℂ)*(2*π*I)).im = v.im-(l:ℝ)*(2*π) := by
    simp [Complex.sub_re,Complex.sub_im,Complex.mul_re,Complex.mul_im]
  rw [he.1,he.2]
  nlinarith only [sq_le_sq.mpr him]

theorem principal_point_denominator {K s : ℝ} (hk : 1 ≤ K) :
    let p := (s:ℂ)+(π:ℂ)*I
    let q := ‖p‖/K
    q/(1+q) ≤ ‖1-Complex.exp (-p/(K:ℂ))‖ := by
  intro p q
  have hp : 0 < K := by linarith
  have hn : ‖-p/(K:ℂ)‖ = q := by rw [norm_div,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hp]
  have hi : (-p/(K:ℂ)).im = -(π/K) := by
    dsimp only [p]; rw [Complex.div_ofReal_im,Complex.neg_im,Complex.add_im]
    simp [neg_div]
  have h : |(-p/(K:ℂ)).im| ≤ π := by
    rw [hi,abs_neg,abs_of_pos (div_pos Real.pi_pos hp)]
    exact div_le_self Real.pi_pos.le hk
  simpa only [hn] using principal_strip_exponential_gap (-p/(K:ℂ)) h

#print axioms principal_strip_exponential_gap
#print axioms principal_point_denominator
end OpenMathResearch.LongCycleExcedances
