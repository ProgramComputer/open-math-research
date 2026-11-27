import TaylorCircle
import FourierLogisticPoles
import FourierCircleShift

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Filter Set Metric Complex Finset
open scoped Topology NNReal Interval Real

private theorem circle_coefficient_fourier (f : ℂ → ℂ) {R : ℝ} (hR : 0 < R) (n : ℕ) :
    (∮ z in C((0:ℂ), R), f z / z^(n+1)) =
      ((2:ℂ)*Real.pi*I) * (normalizedFourierIntegral (fun x => f (circleMap 0 R x)) n / (R:ℂ)^n) := by
  have hR' : (R:ℂ) ≠ 0 := ofReal_ne_zero.mpr hR.ne'
  have hpi : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hp (x : ℝ) : circleMap 0 R x = (R:ℂ)*exp ((x:ℂ)*I) := by
    simp [circleMap]
  have hp0 (x : ℝ) : circleMap 0 R x ≠ 0 := by
    rw [hp]
    exact mul_ne_zero hR' (exp_ne_zero _)
  have he (x : ℝ) : (exp ((x:ℂ)*I))⁻¹ ^ n = circleWave (-(n:ℤ)) x := by
    rw [← exp_neg, ← exp_nat_mul]
    unfold circleWave
    push_cast
    congr 1
    ring
  have hfun : (fun x : ℝ =>
      deriv (circleMap 0 R) x • (f (circleMap 0 R x) / (circleMap 0 R x)^(n+1))) =
      fun x : ℝ => (I/(R:ℂ)^n) * (circleWave (-(n:ℤ)) x * f (circleMap 0 R x)) := by
    funext x
    rw [deriv_circleMap, smul_eq_mul]
    let w := circleMap 0 R x
    change (w*I) * (f w / w^(n+1)) =
      (I/(R:ℂ)^n) * (circleWave (-(n:ℤ)) x * f w)
    have hcancel : (w*I) * (f w / w^(n+1)) = I*(w⁻¹)^n*f w := by
      rw [pow_succ, div_eq_mul_inv, mul_inv_rev, ←inv_pow]
      calc
        _ = (w*w⁻¹)*(I*(w⁻¹)^n*f w) := by ring
        _ = _ := by rw [mul_inv_cancel₀ (hp0 x), one_mul] <;> ring
    have hpow : (w⁻¹)^n = ((R:ℂ)^n)⁻¹ * circleWave (-(n:ℤ)) x := by
      dsimp only [w]
      rw [hp,mul_inv_rev,mul_pow,he,inv_pow,mul_comm]
    rw [hcancel,hpow,div_eq_mul_inv]
    ring
  unfold circleIntegral normalizedFourierIntegral
  rw [hfun, intervalIntegral.integral_const_mul]
  field_simp [hR',hpi]
  <;> ring

/-- The analytic small-circle coefficient equals the outer Fourier boundary
coefficient plus contributions from the enclosed odd logistic poles. -/
theorem logistic_contour_coefficient
    {s R : ℝ} {ρ : ℝ≥0} (hρ : 0 < ρ) (hR : (ρ:ℝ) ≤ R)
    (P : Finset ℂ)
    (hsmall : ∀ p ∈ range (fun l : ℤ => (s:ℂ)+(2*(l:ℂ)+1)*π*I), (ρ:ℝ) < ‖p‖)
    (hregular : ∀ p ∈ range (fun l : ℤ => (s:ℂ)+(2*(l:ℂ)+1)*π*I), ‖p‖ ≠ R)
    (hP : ∀ p : ℂ, p ∈ P ↔ p ∈ range (fun l : ℤ => (s:ℂ)+(2*(l:ℂ)+1)*π*I) ∧ ‖p‖ < R)
    {N : ℂ → ℂ} (hN : ∀ z, AnalyticAt ℂ N z) (a : ℕ → ℂ)
    (hs : ∀ᶠ w in 𝓝 (0:ℂ), HasSum (fun n => a n*w^n)
      (N w/(1+exp (w-s)))) (n : ℕ) :
    a n = normalizedFourierIntegral
      (fun x => N (circleMap 0 R x)/(1+exp (circleMap 0 R x-s))) n / (R:ℂ)^n +
      ∑ p ∈ P, N p/p^(n+1) := by
  let D (z : ℂ) := 1+exp (z-s)
  let f (z : ℂ) := N z / D z
  let F (z : ℂ) := f z/z^(n+1)
  let A (p : ℂ) := -(N p/p^(n+1))
  have hD (z : ℂ) : AnalyticAt ℂ D z :=
    analyticAt_const.add (analyticAt_cexp.comp (analyticAt_id.sub analyticAt_const))
  have hρ' : (0:ℝ) < ρ := hρ
  have hf (z : ℂ) (hz : D z ≠ 0) : AnalyticAt ℂ f z := (hN z).div (hD z) hz
  have hinner : (∮ z in C((0:ℂ), (ρ:ℝ)), F z) = ((2:ℂ)*π*I)*a n := by
    apply taylor_circle_extract hρ _ hs n
    intro z hz
    apply (hf z _).differentiableAt.differentiableWithinAt
    intro he
    have hc : ‖z‖ ≤ (ρ:ℝ) := by simpa [mem_closedBall, dist_zero_right] using hz
    exact (not_lt_of_ge hc) (hsmall z ((logistic_denominator_zero_iff s z).mp he))
  have hout := annular_principal_parts hρ' hR P A F
    (fun p hp => ⟨hsmall p ((hP p).mp hp).1, ((hP p).mp hp).2⟩)
    (fun z hz hzP => ?_) (fun p hp => ?_)
  · have hb := circle_coefficient_fourier f (hρ'.trans_le hR) n
    rw [hinner, hb] at hout
    have he : (2:ℂ)*π*I ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num)
      (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
    simp only [A, sum_neg_distrib, ←mul_sub, ←mul_neg] at hout
    have hh := mul_left_cancel₀ he hout
    dsimp only [f, D] at hh
    linear_combination -hh
  · have hz0 : z ≠ 0 := by
      intro e
      subst z
      exact hz.2 (mem_ball_self hρ')
    have hzD : D z ≠ 0 := by
      intro e
      have hp := (logistic_denominator_zero_iff s z).mp e
      have hzR : ‖z‖ ≤ R := by simpa [mem_closedBall, dist_zero_right] using hz.1
      exact hzP ((hP z).mpr ⟨hp, lt_of_le_of_ne hzR (hregular z hp)⟩)
    exact (hf z hzD).div (analyticAt_id.pow _) (pow_ne_zero _ hz0)
  · have hpole := ((hP p).mp hp).1
    have hzero : D p = 0 := (logistic_denominator_zero_iff s p).mpr hpole
    have hp0 : p ≠ 0 := norm_pos_iff.mp (hρ'.trans (hsmall p hpole))
    have hder : HasDerivAt D (-1) p := by
      have hh := (hasDerivAt_const p (1:ℂ)).add ((hasDerivAt_id p).sub_const (s:ℂ)).cexp
      apply hh.congr_deriv
      have he : (1:ℂ)+exp (p-s)=0 := hzero
      simp only [id_eq, add_zero, one_mul, zero_add]
      linear_combination he
    obtain ⟨g,hg,he⟩ := analytic_remove_simple_pole
      ((hN p).div (analyticAt_id.pow (n+1)) (pow_ne_zero _ hp0))
      (hD p) hzero hder (by norm_num)
    refine ⟨g,hg,he.mono fun z hz => ?_⟩
    simpa [F,f,A,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using hz

#print axioms logistic_contour_coefficient
end OpenMathResearch.LongCycleExcedances
