import RepositoryPoleTransport
import MinorPoleRadius
import TiltAnalyticEvaluation

set_option autoImplicit false
noncomputable section
namespace RepositoryQuotientAudit
open OpenMathResearch.LongCycleExcedances Finset Real

private theorem odd_pole_norm_square (x : ℝ) (j : ℤ) :
    ‖coherentPole x j‖^2 = x^2 + ((2*(j:ℝ)+1)*π)^2 := by
  rw [Complex.sq_norm,Complex.normSq_apply]
  simp [coherentPole,Complex.add_re,Complex.add_im,Complex.mul_I_re,Complex.mul_I_im,Complex.mul_re,Complex.mul_im]
  ring

theorem enclosed_coherent_radial_decay {n k : ℕ} (hk : 7 ≤ k) (x : ℝ) (j : ℕ)
    (henc : ‖coherentPole x (j:ℤ)‖ ≤ ‖coherentPole x 0‖*(1+1/(50*(k:ℝ))))
    (hm : 1 ≤ (n:ℝ)*(π/‖coherentPole x 0‖)^2) :
    (‖coherentPole x 0‖ / ‖coherentPole x (j:ℤ)‖)^n ≤
      exp (-(49/100)*((2*(j:ℝ)+1)^2-1)) := by
  let r := ‖coherentPole x 0‖
  have hr : 0 < r := coherentPole_near_pos x
  apply enclosed_radius_decay hk hr (hr.trans_le (coherentPole_near_le x _))
    (show 1 ≤ 2*(j:ℝ)+1 by linarith [Nat.cast_nonneg (α := ℝ) j]) _ henc hm
  have hr2 : r^2 = x^2+π^2 := by simpa [r] using odd_pole_norm_square x 0
  change (‖coherentPole x (j:ℤ)‖/r)^2 = _
  rw [div_pow, odd_pole_norm_square, Int.cast_natCast]
  change _ = 1+_*(π/r)^2
  rw [div_pow]
  field_simp [hr.ne']
  nlinarith only [hr2]

/-- Positive nonprincipal half of the normalized residue mass, for any
finite collection of odd poles inside the enlarged circle. -/
theorem actual_enclosed_minor_poles_le_fifth {n k : ℕ} (hk : 7 ≤ k) {x : ℝ}
    (hx : 10*√(k:ℝ) ≤ x) (hm : 1 ≤ (n:ℝ)*(π/‖coherentPole x 0‖)^2)
    (s : Finset ℕ) (henc : ∀ i ∈ s, ‖coherentPole x ((i+1:ℕ):ℤ)‖ ≤
      ‖coherentPole x 0‖*(1+1/(50*(k:ℝ)))) :
    let T := coherentTilt k (-exp (-x))
    ∑ i ∈ s, (2*(i+1:ℕ)+1:ℝ) *
      (‖coherentPole x 0‖/‖coherentPole x ((i+1:ℕ):ℤ)‖)^n *
      ‖seriesValue T (coherentPole x ((i+1:ℕ):ℤ))/seriesValue T (coherentPole x 0)‖ ≤ 1/5 := by
  intro T
  apply weighted_minor_poles_le_fifth
  intro i hi
  let j := i+1
  let p : ℝ := 2*j+1
  have hE := henc i hi
  have hrad := enclosed_coherent_radial_decay hk x j hE hm
  have htilt := actual_logTilt_far_exp_ratio hk hx (show (0:ℤ) < (j:ℤ) by dsimp [j]; omega) hE
  have evalT (w : ℂ) : seriesValue T w = Complex.exp (actualLogTiltAt k x w) :=
    seriesValue_original_coherentTilt (by omega) _ _
  rw [← actualLogTiltAt_principal k x] at htilt
  rw [evalT,evalT]
  have he : (24/25:ℝ)*((j:ℤ):ℝ) = (12/25)*(p-1) := by
    dsimp only [p]; push_cast; ring
  rw [he] at htilt
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have h := mul_le_mul hrad htilt.le (norm_nonneg _) (exp_pos _).le
  change p*_ * _ ≤ p*exp _
  rw [mul_assoc,exp_add]
  exact mul_le_mul_of_nonneg_left h hp

#print axioms enclosed_coherent_radial_decay
#print axioms actual_enclosed_minor_poles_le_fifth
end RepositoryQuotientAudit
