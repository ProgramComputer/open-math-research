import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.Real.Pi.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real Complex MeasureTheory

private theorem exp_segment_mass {u : ℝ} (hu : 0 ≤ u) :
    1/(1+u) ≤ ∫ t in (0:ℝ)..1, Real.exp (-u*t) := by
  rcases eq_or_lt_of_le hu with h | h
  · subst u
    simp
  rw [intervalIntegral.integral_comp_mul_left Real.exp (neg_ne_zero.mpr h.ne'),
    mul_zero, mul_one, integral_exp, Real.exp_zero]
  rw [smul_eq_mul, Real.exp_neg, inv_neg]
  have he := Real.add_one_le_exp u
  have hpos := Real.exp_pos u
  field_simp [h.ne',show 0 < 1+u by linarith]
  apply (div_le_div_iff₀ (by linarith : 0 < 1+u) (mul_pos h hpos)).mpr
  nlinarith

/-- An integral along the segment from zero to z bounds the principal
denominator without separating its real and imaginary parts into cases. -/
theorem exp_principal_denominator {z : ℂ} (hu : 0 ≤ z.re)
    (hv : 0 ≤ z.im) (hb : z.im ≤ Real.pi/2) :
    Real.cos z.im * (1/(1+z.re)) * ‖z‖ ≤ ‖1-Complex.exp (-z)‖ := by
  by_cases hz : z=0
  · simp [hz]
  let g := fun t : ℝ => Complex.exp (-z*(t:ℂ))
  let h := fun t : ℝ => Real.exp (-z.re*t)
  have cg : Continuous g := by dsimp [g]; fun_prop
  have ch : Continuous h := by dsimp [h]; fun_prop
  have ccos : 0 ≤ Real.cos z.im := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos],hb⟩
  have hpoint (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) : Real.cos z.im * h t ≤ (g t).re := by
    have ht0 := ht.1
    have ht1 := ht.2
    have hc := Real.cos_le_cos_of_nonneg_of_le_pi (mul_nonneg hv ht0)
      (show z.im ≤ Real.pi by linarith [Real.pi_pos]) (mul_le_of_le_one_right hv ht1)
    dsimp [g,h]
    rw [Complex.exp_re]
    simp only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.neg_re,
      Complex.neg_im,mul_zero,sub_zero,zero_add,neg_mul,Real.cos_neg]
    exact (mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le).trans_eq (mul_comm _ _)
  have hi := intervalIntegral.integral_mono_on (μ:=volume) (zero_le_one : (0:ℝ)≤1)
    ((continuous_const.mul ch).intervalIntegrable _ _)
    ((Complex.continuous_re.comp cg).intervalIntegrable _ _) hpoint
  rw [intervalIntegral.integral_const_mul] at hi
  have hre := Complex.reCLM.intervalIntegral_comp_comm (cg.intervalIntegrable (μ:=volume) 0 1)
  change (∫ t in (0:ℝ)..1, (g t).re) = (∫ t in (0:ℝ)..1, g t).re at hre
  change Real.cos z.im * (∫ t in (0:ℝ)..1, h t) ≤ ∫ t in (0:ℝ)..1, (g t).re at hi
  rw [hre] at hi
  have hl := (mul_le_mul_of_nonneg_left (exp_segment_mass hu) ccos).trans
    (hi.trans (Complex.re_le_norm _))
  have he : (∫ t in (0:ℝ)..1, g t)*z = 1-Complex.exp (-z) := by
    dsimp only [g]
    rw [integral_exp_mul_complex (neg_ne_zero.mpr hz)]
    simp only [Complex.ofReal_one,Complex.ofReal_zero,mul_zero,mul_one,Complex.exp_zero]
    field_simp [hz,neg_ne_zero.mpr hz]
    ring
  rw [←he,norm_mul]
  exact mul_le_mul_of_nonneg_right hl (norm_nonneg _)

private theorem exp_real_gap (z : ℂ) (hu : 0 ≤ z.re) :
    z.re/(1+z.re) ≤ ‖1-Complex.exp (-z)‖ := by
  have h1 : z.re/(1+z.re) ≤ 1-Real.exp (-z.re) := by
    rw [Real.exp_neg]
    have hp := Real.exp_pos z.re
    have hd : 0 < 1+z.re := by linarith
    apply (div_le_iff₀ hd).mpr
    rw [sub_mul,one_mul,inv_mul_eq_div]
    have he : (1+z.re)/Real.exp z.re ≤ 1 := (div_le_one hp).mpr (by linarith [Real.add_one_le_exp z.re])
    linarith
  apply h1.trans ((le_trans _ (Complex.re_le_norm _)) : 1-Real.exp (-z.re) ≤ ‖1-Complex.exp (-z)‖)
  simp only [Complex.sub_re,Complex.one_re,Complex.exp_re,Complex.neg_re,Complex.neg_im,Real.cos_neg]
  exact sub_le_sub_left (mul_le_of_le_one_right (Real.exp_pos _).le (Real.cos_le_one _)) 1

/-- The three denominator budgets of the common-circle proof follow from
one complex estimate at heights at most 1/10 in the imaginary direction. -/
theorem uniform_principal_denominator {z : ℂ} (hu : 0 ≤ z.re) (hv : 0 ≤ z.im)
    (hb : z.im ≤ 1/10) :
    ‖z‖/(2+‖z‖) ≤ ‖1-Complex.exp (-z)‖ ∧
    (‖z‖ ≤ Real.pi → ‖z‖/5 ≤ ‖1-Complex.exp (-z)‖) ∧
    (‖z‖ ≤ (12/25)*Real.pi → ‖z‖/3 ≤ ‖1-Complex.exp (-z)‖) := by
  have hz := norm_nonneg z
  have hden : 0 < 1+z.re := by linarith
  have hc : 99/100 ≤ Real.cos z.im := by
    have ht := Real.one_sub_sq_div_two_le_cos (x:=z.im)
    nlinarith [mul_nonneg (sub_nonneg.mpr hb) (show 0 ≤ 1/10+z.im by linarith)]
  have h := exp_principal_denominator hu hv (by linarith [Real.pi_gt_three] : z.im ≤ Real.pi/2)
  have hub := Complex.re_le_norm z
  have hsimple (a : ℝ) (ha : a ≤ (99/100)/(1+z.re)) :
      a*‖z‖ ≤ ‖1-Complex.exp (-z)‖ := by
    apply le_trans _ h
    apply mul_le_mul_of_nonneg_right _ hz
    exact ha.trans (by rw [mul_one_div]; exact div_le_div_of_nonneg_right hc hden.le)
  refine ⟨?_,?_,?_⟩
  · by_cases hq : ‖z‖ ≤ 1
    · rw [div_eq_inv_mul]
      apply hsimple
      rw [←one_div]
      apply (div_le_div_iff₀ (by positivity) hden).mpr
      linarith
    · have ht := Complex.norm_le_abs_re_add_abs_im z
      rw [abs_of_nonneg hu,abs_of_nonneg hv] at ht
      apply le_trans _ (exp_real_gap z hu)
      apply (div_le_div_iff₀ (by positivity) hden).mpr
      nlinarith
  · intro hq
    rw [div_eq_inv_mul]
    apply hsimple
    apply (le_div_iff₀ hden).mpr
    linarith [Real.pi_lt_d4]
  · intro hq
    rw [div_eq_inv_mul]
    apply hsimple
    apply (le_div_iff₀ hden).mpr
    linarith [Real.pi_lt_d4]

/-- All three bounds in the units of the principal pole of the original
permutation rows. The radial direction s may be arbitrarily large. -/
theorem original_principal_denominator {K s r : ℝ} (hk : 100 ≤ K) (hs : 0 ≤ s)
    (hr : 0 < r) (hr2 : r^2 = s^2+Real.pi^2) :
    let z : ℂ := (⟨s,Real.pi⟩ : ℂ)/(K:ℂ)
    let q := r/K
    q/(2+q) ≤ ‖1-Complex.exp (-z)‖ ∧
    (q ≤ Real.pi → q/5 ≤ ‖1-Complex.exp (-z)‖) ∧
    (q ≤ (12/25)*Real.pi → q/3 ≤ ‖1-Complex.exp (-z)‖) := by
  let p : ℂ := ⟨s,Real.pi⟩
  let z := p/(K:ℂ)
  have hp : ‖p‖ = r := by
    have h : ‖p‖^2 = r^2 := by rw [Complex.sq_norm,Complex.normSq_apply,hr2]; simp [p,pow_two]
    nlinarith [norm_nonneg p]
  have hK : 0 < K := by linarith
  have hn : ‖z‖ = r/K := by simp [z,norm_div,hp,abs_of_pos hK]
  have he : z.re = s/K ∧ z.im = Real.pi/K := by
    simp [z,p,Complex.div_ofReal_re,Complex.div_ofReal_im]
  have hsmall : Real.pi/K ≤ 1/10 := (div_le_iff₀ hK).mpr (by linarith [Real.pi_lt_d4])
  have h := uniform_principal_denominator (z:=z)
    (he.1.symm ▸ div_nonneg hs hK.le) (he.2.symm ▸ div_nonneg Real.pi_pos.le hK.le)
    (he.2 ▸ hsmall)
  simpa only [hn] using h

#print axioms original_principal_denominator
#print axioms uniform_principal_denominator
#print axioms exp_principal_denominator
end OpenMathResearch.LongCycleExcedances
