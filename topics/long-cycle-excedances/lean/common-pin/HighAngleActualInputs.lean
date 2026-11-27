import HighAngleLattice
import HighAngleScalar
import TiltAnalyticEvaluation
import Mathlib.Analysis.Complex.ExponentialBounds

noncomputable section
open Finset
open scoped Real
open OpenMathResearch.LongCycleExcedances
namespace RepositoryQuotientAudit

def highAngleRadius (x : ℝ) (k : ℕ) : ℝ :=
  ‖coherentPole x 0‖ * (1+1/(k:ℝ))

theorem highAngleRadius_pos (x : ℝ) (k : ℕ) : 0 < highAngleRadius x k :=
  mul_pos (coherentPole_near_pos x) (by positivity)

theorem actual_high_angle_log_mass {k : ℕ} (hk : 7 ≤ k) {x : ℝ} (hx : 0 ≤ x)
    (hangle : ‖coherentPole x 0‖ ≤ 2*π) :
    let t := -Real.exp (-x)
    let R := highAngleRadius x k
    (∑ i ∈ range (k-1), |cutoffLogCoefficient k t (i+1)*R^(i+1)|) ≤
      5 + 18*Real.log k := by
  dsimp only
  let t := -Real.exp (-x)
  let r := ‖coherentPole x 0‖
  let R := highAngleRadius x k
  let γ := 1+(1:ℝ)/k
  have hγ : 0 < γ := by dsimp [γ]; positivity
  have hr : 0 < r := coherentPole_near_pos x
  have hR := highAngleRadius_pos x k
  have hk' : (7:ℝ) ≤ k := by exact_mod_cast hk
  have hγ' : γ ≤ 8/7 := by
    have h := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<7) hk'
    dsimp [γ]
    linarith
  have hR' : R ≤ 10 := by
    change r * γ ≤ 10
    have h : r * γ ≤ 2*π*(8/7) := mul_le_mul hangle hγ' hγ.le (by positivity)
    refine h.trans ((mul_le_mul_of_nonneg_right
      (show 2*π ≤ 8 by linarith only [Real.pi_lt_four]) (by norm_num : (0:ℝ) ≤ 8/7)).trans ?_)
    norm_num
  have ht0 : t ≤ 0 := neg_nonpos.mpr (Real.exp_pos _).le
  have ht : -1 ≤ t := neg_le_neg (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx))
  apply high_angle_finite_log_bound (by omega : 2 ≤ k)
  · simpa [cutoffLogCoefficient, t] using coherentLinearTilt_bound ht ht0 hR.le hR'
  · intro j hj hjk
    have hj1 : j ≠ 1 := by omega
    have hj0 : (0:ℝ)<j := by positivity
    have hf0 : (0:ℝ)<(j-1).factorial := by positivity
    have hf : (j.factorial:ℝ) = (j:ℝ)*(j-1).factorial := by
      exact_mod_cast (show j.factorial = j*(j-1).factorial by
        cases j with
        | zero => omega
        | succ j => simp [Nat.factorial_succ])
    have he := congrArg Complex.re (LongCycleBounds.Band.moment_poles j hj x hx)
    simp only [Complex.ofReal_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
      zero_mul, sub_zero] at he
    have hb := scaledPoleSum_re_bound x j hj hangle
    have hγj := cutoff_radius_power_le_exp_one (by omega : 0 < k) hjk.le
    have heuler : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
    simp only [cutoffLogCoefficient, hj1, if_false, hj, hjk, and_self, if_true]
    rw [he, hf]
    have hre :
        |-(↑(j-1).factorial * (LongCycleBounds.oddPoleSum j x).re) /
            ((j:ℝ)*↑(j-1).factorial) * R^j| =
          |(LongCycleBounds.oddPoleSum j x).re * r^j| * γ^j / (j:ℝ) := by
      rw [show R=r*γ by rfl, mul_pow]
      simp only [abs_mul, abs_div, abs_neg, abs_of_pos hf0, abs_of_pos hj0,
        abs_of_nonneg (pow_nonneg hr.le _), abs_of_nonneg (pow_nonneg hγ.le _)]
      field_simp [ne_of_gt hf0, ne_of_gt hj0] <;> ring
    rw [hre]
    apply (div_le_div_iff_of_pos_right hj0).2
    exact (mul_le_mul hb hγj (pow_nonneg hγ.le _) (by positivity)).trans (by linarith)

end RepositoryQuotientAudit
