import PhaseMiddle
import ActualPhaseDerivative

noncomputable section
namespace RepositoryQuotientAudit
open OpenMathResearch.LongCycleExcedances
open Real Set

def principalPhaseX (n k : ℕ) (x : ℝ) : ℝ :=
  ((n:ℝ)+1)*poleAngle x - (principalLogTilt k x).im

/-- The full middle-regime phase slope in the logarithmic modulus variable,
with the actual Eulerian sum used in the original-label generating function. -/
theorem original_middle_phase_slope {n k : ℕ} (hk : 7 ≤ k) (hn : k ≤ n)
    (x : ℝ) (hx : 0 ≤ x) (hmid : 1 ≤ (n:ℝ)*(π/‖coherentPole x 0‖)^2) :
    let r := ‖coherentPole x 0‖
    |deriv (principalPhaseX n k) x + n*π/r^2| < (32/35)*(n:ℝ)*π/r^2 :=
  middle_slope_from_moment hk hn (principalLogTilt k) _ x
    (actual_principalLogTilt_derivative (by omega) x hx) hmid

/-- The principal phase is strictly decreasing as the logarithmic modulus
increases up to the endpoint of any middle interval. With increasing pole
angle the order is reversed. -/
theorem original_middle_phase_strictAnti {n k : ℕ} (hk : 7 ≤ k) (hn : k ≤ n)
    (b : ℝ) (hb : b^2+π^2 ≤ (n:ℝ)*π^2) :
    StrictAntiOn (principalPhaseX n k) (Icc 0 b) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc 0 b)
  · intro x hx
    have h := actual_principalLogTilt_derivative (by omega : 2 ≤ k) x hx.1
    exact (((poleAngle_hasDerivAt x).continuousAt.const_mul ((n:ℝ)+1)).sub
      (Complex.continuous_im.continuousAt.comp h.continuousAt)).continuousWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    let r := ‖coherentPole x 0‖
    have hr : 0 < r := coherentPole_near_pos x
    have hsq : r^2=x^2+π^2 := by
      have hre : (coherentPole x 0).re = x := by simp [coherentPole, Complex.add_re,
        Complex.mul_I_re, Complex.mul_im, Complex.add_im]
      have him : (coherentPole x 0).im=π := by simpa using coherentPole_im x 0
      dsimp only [r]
      rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
      ring
    have hr2 : r^2 ≤ (n:ℝ)*π^2 := by
      rw [hsq]
      exact (add_le_add_right (pow_le_pow_left₀ hx.1.le hx.2.le 2) _).trans hb
    have hm : 1 ≤ (n:ℝ)*(π/r)^2 := by
      rw [div_pow, ← mul_div_assoc, le_div_iff₀ (pow_pos hr _), one_mul]
      exact hr2
    have h := original_middle_phase_slope hk hn x hx.1.le hm
    change |deriv (principalPhaseX n k) x + (n:ℝ)*π/r^2| < (32/35)*(n:ℝ)*π/r^2 at h
    have h' := (abs_lt.mp h).2
    have hnreal : (0:ℝ) < n := by exact_mod_cast (show 0<n by omega)
    have hp : 0 < (n:ℝ)*π/r^2 := div_pos (mul_pos hnreal pi_pos) (pow_pos hr _)
    linarith only [h', hp, show (32/35)*(n:ℝ)*π/r^2=(32/35)*((n:ℝ)*π/r^2) by ring]

#print axioms original_middle_phase_slope
#print axioms original_middle_phase_strictAnti
end RepositoryQuotientAudit
