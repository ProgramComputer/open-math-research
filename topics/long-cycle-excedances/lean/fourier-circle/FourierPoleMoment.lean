import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Complex Real Metric MeasureTheory
open scoped ComplexConjugate

def invertedPole (p : ℂ) (R : ℝ) : ℂ := (R:ℂ)^2/conj p

theorem invertedPole_norm (p : ℂ) {R : ℝ} (hR : 0<R) :
    ‖invertedPole p R‖ = R^2/‖p‖ := by
  simp [invertedPole,norm_div,norm_pow,abs_of_pos hR]

private theorem square_norm_cast (z : ℂ) : ((‖z‖^2 : ℝ):ℂ)=conj z*z := by
  rw [Complex.sq_norm,Complex.normSq_eq_conj_mul_self]

theorem circle_inverse_pole (p : ℂ) {R : ℝ} (hR : 0<R) (hg : ‖p‖ ≠ R) :
    circleIntegral (fun w => (w-p)⁻¹) 0 R =
      if ‖p‖<R then 2*(π:ℂ)*Complex.I else 0 := by
  by_cases hp : ‖p‖<R
  · rw [if_pos hp]
    exact circleIntegral.integral_sub_inv_of_mem_ball (by simpa using hp)
  · rw [if_neg hp]
    have hpo : R<‖p‖ := lt_of_le_of_ne (le_of_not_gt hp) hg.symm
    have hdiff : DifferentiableOn ℂ (fun w : ℂ => (w-p)⁻¹) (closedBall 0 R) := by
      intro w hw
      apply (differentiableAt_id.sub_const p).inv ?_ |>.differentiableWithinAt
      apply sub_ne_zero.mpr
      intro he
      change w = p at he
      subst w
      exact (not_le_of_gt hpo) (by simpa using hw)
    exact Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hR.le
      Set.countable_empty hdiff.continuousOn (fun w hw =>
        hdiff.differentiableAt (Metric.closedBall_mem_nhds_of_mem hw.1))

theorem squared_pole_partial_fractions {p w : ℂ} {R : ℝ} (hp : p≠0) (hw : ‖w‖=R)
    (hwp : w≠p) (hwi : w≠invertedPole p R) :
    ((‖p‖^2-R^2:ℝ):ℂ)*((‖p-w‖^2:ℝ):ℂ)⁻¹ =
      w*((w-invertedPole p R)⁻¹-(w-p)⁻¹) := by
  let z := invertedPole p R
  have hp' : conj p≠0 := by simpa using hp
  have hz : z*conj p=(R:ℂ)^2 := by dsimp only [z,invertedPole]; exact div_mul_cancel₀ _ hp'
  have hww : conj w*w=(R:ℂ)^2 := by rw [←square_norm_cast,hw]; push_cast; rfl
  have hbar : conj (p-w) ≠ 0 := (map_ne_zero conj).mpr (sub_ne_zero.mpr hwp.symm)
  rw [Complex.ofReal_sub,square_norm_cast,square_norm_cast,Complex.ofReal_pow]
  change (conj p*p-(R:ℂ)^2)*(conj (p-w)*(p-w))⁻¹ = w*((w-z)⁻¹-(w-p)⁻¹)
  have hz' : w-z≠0 := sub_ne_zero.mpr hwi
  have hconj : conj p - conj w ≠ 0 := by simpa only [map_sub] using hbar
  rw [map_sub conj]
  field_simp [hconj, hz', sub_ne_zero.mpr hwp, sub_ne_zero.mpr hwp.symm]
  linear_combination (norm := ring_nf) (w-p)*((p-z)*hww + (w-p)*hz)

/-- The angular square-integral of a single pole, on either side of the circle. -/
theorem angular_inverse_square {p : ℂ} {R : ℝ} (hR : 0 < R) (hg : ‖p‖ ≠ R) :
    (∫ x in (0:ℝ)..2*π, (‖p-circleMap 0 R x‖^2)⁻¹) =
      (2*π)/|‖p‖^2-R^2| := by
  by_cases hp : p = 0
  · subst p
    simp [norm_circleMap_zero, abs_of_pos hR, div_eq_mul_inv]
  let z := invertedPole p R
  have hp0 : 0 < ‖p‖ := norm_pos_iff.mpr hp
  have hnz : ‖z‖ = R^2/‖p‖ := invertedPole_norm p hR
  have hzlt : ‖z‖ < R ↔ R < ‖p‖ := by
    rw [hnz, div_lt_iff₀ hp0, pow_two]
    exact mul_lt_mul_iff_of_pos_left hR
  have hzg : ‖z‖ ≠ R := by
    rw [hnz, ne_eq, div_eq_iff hp0.ne', pow_two]
    exact fun h => hg ((mul_left_cancel₀ hR.ne' h).symm)
  have ci (a : ℂ) (ha : ‖a‖ ≠ R) : CircleIntegrable (fun w => (w-a)⁻¹) 0 R := by
    apply circleIntegrable_sub_inv_iff.mpr
    exact Or.inr (by simpa [abs_of_pos hR] using ha)
  let M := ∫ x in (0:ℝ)..2*π, (‖p-circleMap 0 R x‖^2)⁻¹
  have hcircle :
      circleIntegral (fun w => (w-z)⁻¹-(w-p)⁻¹) 0 R =
        (I*((‖p‖^2-R^2:ℝ):ℂ))*(M:ℂ) := by
    unfold circleIntegral
    calc
      _ = ∫ x in (0:ℝ)..2*π, (I*((‖p‖^2-R^2:ℝ):ℂ))*(((‖p-circleMap 0 R x‖^2)⁻¹:ℝ):ℂ) := by
        apply intervalIntegral.integral_congr
        intro x _
        let w := circleMap 0 R x
        have hw : ‖w‖ = R := (norm_circleMap_zero R x).trans (abs_of_pos hR)
        have hwa (a : ℂ) (ha : ‖a‖ ≠ R) : w ≠ a := fun h => ha (h ▸ hw)
        have hs := squared_pole_partial_fractions hp hw (hwa p hg) (hwa z hzg)
        dsimp only
        rw [deriv_circleMap, smul_eq_mul, Complex.ofReal_inv]
        change w*I*((w-z)⁻¹-(w-p)⁻¹)=_
        linear_combination -I*hs
      _ = _ := by rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_ofReal]
  rw [circleIntegral.integral_sub (ci z hzg) (ci p hg),
    circle_inverse_pole z hR hzg,circle_inverse_pole p hR hg] at hcircle
  change M = _
  rcases lt_or_gt_of_ne hg with h | h
  · rw [if_neg (fun hz => (not_lt_of_gt h) (hzlt.mp hz)),if_pos h,zero_sub] at hcircle
    have hreal := congrArg Complex.im hcircle
    simp [Complex.mul_im,Complex.mul_re] at hreal
    rw [abs_of_neg (by nlinarith [sq_nonneg (‖p‖-R)] : ‖p‖^2-R^2 < 0)]
    apply (eq_div_iff (by nlinarith [sq_nonneg (‖p‖-R)])).2
    simp only [←Complex.ofReal_pow, Complex.ofReal_re] at hreal
    linear_combination hreal
  · rw [if_pos (hzlt.mpr h),if_neg (not_lt_of_gt h),sub_zero] at hcircle
    have hreal := congrArg Complex.im hcircle
    simp [Complex.mul_im,Complex.mul_re] at hreal
    rw [abs_of_pos (by nlinarith [sq_nonneg (‖p‖-R)] : 0 < ‖p‖^2-R^2)]
    apply (eq_div_iff (by nlinarith [sq_nonneg (‖p‖-R)])).2
    simp only [←Complex.ofReal_pow, Complex.ofReal_re] at hreal
    linear_combination -hreal

#print axioms angular_inverse_square

#print axioms circle_inverse_pole
#print axioms squared_pole_partial_fractions
end OpenMathResearch.LongCycleExcedances
