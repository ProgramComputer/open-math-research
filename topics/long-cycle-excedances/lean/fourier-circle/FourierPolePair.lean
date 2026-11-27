import FourierPoleMoment
import Mathlib.Tactic.Positivity

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Complex Real MeasureTheory

def poleGap (p : ℂ) (R : ℝ) : ℝ := |‖p‖^2 - R^2|

def normalizedPole (p : ℂ) (R x : ℝ) : ℝ :=
  √(poleGap p R) / ‖p - circleMap 0 R x‖

theorem poleGap_pos {p : ℂ} {R : ℝ} (hR : 0 < R) (hp : ‖p‖ ≠ R) :
    0 < poleGap p R := by
  apply abs_pos.mpr
  rcases lt_or_gt_of_ne hp with h | h
  · exact ne_of_lt (sub_neg.mpr (sq_lt_sq' (by linarith [norm_nonneg p]) h))
  · exact ne_of_gt (sub_pos.mpr (sq_lt_sq' (by linarith [norm_nonneg p]) h))

theorem normalizedPole_continuous {p : ℂ} {R : ℝ} (hR : 0 < R) (hp : ‖p‖ ≠ R) :
    Continuous (normalizedPole p R) := by
  apply continuous_const.div ((continuous_const.sub (continuous_circleMap _ _)).norm)
  intro x
  apply norm_ne_zero_iff.mpr
  apply sub_ne_zero.mpr
  intro h
  exact hp ((congrArg norm h).trans ((norm_circleMap_zero R x).trans (abs_of_pos hR)))

theorem normalizedPole_second_moment {p : ℂ} {R : ℝ} (hR : 0 < R) (hp : ‖p‖ ≠ R) :
    (∫ x in (0:ℝ)..2*π, normalizedPole p R x^2) = 2*π := by
  have hg := poleGap_pos hR hp
  have h := angular_inverse_square hR hp
  calc
    _ = ∫ x in (0:ℝ)..2*π, poleGap p R * (‖p - circleMap 0 R x‖^2)⁻¹ := by
      apply intervalIntegral.integral_congr
      intro x _
      dsimp only [normalizedPole]
      rw [div_pow, Real.sq_sqrt hg.le, div_eq_mul_inv]
    _ = _ := by
      rw [intervalIntegral.integral_const_mul,h]
      change poleGap p R * ((2*π)/poleGap p R) = 2*π
      field_simp [hg.ne']

/-- The pair estimate holds for two poles on arbitrary sides of the circle. -/
theorem normalizedPole_pair_integral {p q : ℂ} {R : ℝ} (hR : 0 < R)
    (hp : ‖p‖ ≠ R) (hq : ‖q‖ ≠ R) :
    (∫ x in (0:ℝ)..2*π, normalizedPole p R x * normalizedPole q R x) ≤ 2*π := by
  let u := normalizedPole p R
  let v := normalizedPole q R
  have cu : Continuous u := normalizedPole_continuous hR hp
  have cv : Continuous v := normalizedPole_continuous hR hq
  have hs := intervalIntegral.integral_mono_on (μ := volume) Real.two_pi_pos.le
    ((continuous_const.mul (cu.mul cv)).intervalIntegrable _ _)
    (((cu.pow 2).add (cv.pow 2)).intervalIntegrable _ _)
    (fun x _ => (by nlinarith [sq_nonneg (u x - v x)] : 2*(u x*v x) ≤ u x^2+v x^2))
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
    ((cu.pow 2).intervalIntegrable _ _) ((cv.pow 2).intervalIntegrable _ _)] at hs
  dsimp only [u,v] at hs
  rw [normalizedPole_second_moment hR hp,normalizedPole_second_moment hR hq] at hs
  linarith

#print axioms normalizedPole_second_moment
#print axioms normalizedPole_pair_integral
end OpenMathResearch.LongCycleExcedances
