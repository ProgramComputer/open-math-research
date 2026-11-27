import PoleChord
import RepositoryLogTiltDiscrete
import ActualPhaseDerivative

set_option autoImplicit false
noncomputable section
namespace RepositoryQuotientAudit
open Finset Real OpenMathResearch.LongCycleExcedances

/-- The finite logarithm of the actual tilt, evaluated at any complex point. -/
def actualLogTiltAt (k : ℕ) (x : ℝ) (w : ℂ) : ℂ :=
  logPolyAt (k-1) (fun d => (cutoffLogCoefficient k (-Real.exp (-x)) d : ℂ)) w

theorem actualLogTiltAt_principal (k : ℕ) (x : ℝ) :
    actualLogTiltAt k x (coherentPole x 0) = principalLogTilt k x := rfl

private theorem verticalArgument_odd_pole (x : ℝ) (j : ℤ) :
    verticalArgument x ((2*(j:ℝ)+1)*π) = coherentPole x j := by
  unfold verticalArgument coherentPole
  push_cast
  rfl

private theorem principal_coherentPole_sq (x : ℝ) :
    ‖coherentPole x 0‖^2 = x^2+π^2 := by
  rw [Complex.sq_norm,Complex.normSq_apply]
  simp [coherentPole,Complex.add_re,Complex.add_im,Complex.mul_I_re,Complex.mul_I_im,pow_two]

private theorem principal_in_inflated_radius (x : ℝ) (k : ℕ) :
    ‖coherentPole x 0‖ ≤ ‖coherentPole x 0‖*(1+1/(50*(k:ℝ))) :=
  le_mul_of_one_le_right (norm_nonneg _) (le_add_of_nonneg_right (by positivity))

/-- A chord between actual odd poles on the inflated principal disk.
One unit of integer pole index is a vertical distance of 2π. -/
theorem actual_logTilt_pole_chord {k : ℕ} (hk : 7 ≤ k) {x : ℝ}
    (hx : 10*√(k:ℝ) ≤ x) {l u : ℤ} (hlu : l < u)
    (hl : ‖coherentPole x l‖ ≤ ‖coherentPole x 0‖*(1+1/(50*(k:ℝ))))
    (hu : ‖coherentPole x u‖ ≤ ‖coherentPole x 0‖*(1+1/(50*(k:ℝ)))) :
    ‖actualLogTiltAt k x (coherentPole x u)-actualLogTiltAt k x (coherentPole x l)‖ <
      (24/25)*((u:ℝ)-(l:ℝ)) := by
  let L : ℝ := (2*(l:ℝ)+1)*π
  let U : ℝ := (2*(u:ℝ)+1)*π
  have hlU : L < U := by
    have hh : (l:ℝ) < (u:ℝ) := by exact_mod_cast hlu
    dsimp only [L,U]
    exact mul_lt_mul_of_pos_right (by linarith) pi_pos
  have hL : verticalArgument x L = coherentPole x l := verticalArgument_odd_pole x l
  have hU : verticalArgument x U = coherentPole x u := verticalArgument_odd_pole x u
  have hk₀ : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hx₀ : 0 < x := (mul_pos (by norm_num : (0:ℝ)<10) (Real.sqrt_pos.mpr hk₀)).trans_le hx
  let t : ℂ := ((-Real.exp (-x):ℝ):ℂ)
  let g (d : ℕ) : ℂ := (cutoffLogCoefficient k (-Real.exp (-x)) d : ℂ)
  have hc (j : ℕ) (hj : j ∈ range (k-1)) :
      HasSum (fun i : ℕ => t^(i+1)*((i+1:ℕ):ℂ)^j)
        (-g (j+1)*((j+1).factorial:ℂ)) := by
    have hjk : j+1 < k := by have := mem_range.mp hj; omega
    simpa only [Nat.add_sub_cancel] using cutoffLogCoefficient_hasSum (Nat.succ_pos j) hjk hx₀
  have hb := coherent_log_chord_bound hk hx (norm_nonneg (coherentPole x 0))
    (principal_coherentPole_sq x) hlU (hL.symm ▸ hl) (hU.symm ▸ hu) t
    (hL.symm ▸ coherentPole_exp_neg x l) (hU.symm ▸ coherentPole_exp_neg x u) g hc
  rw [hL,hU] at hb
  have hs : (12/25:ℝ)*(U-L) = π*((24/25)*((u:ℝ)-(l:ℝ))) := by
    dsimp only [L,U]
    ring
  rw [hs] at hb
  exact (mul_lt_mul_left pi_pos).mp hb

theorem actual_logTilt_far_pole {k : ℕ} (hk : 7 ≤ k) {x : ℝ}
    (hx : 10*√(k:ℝ) ≤ x) {j : ℤ} (hj : 0 < j)
    (hr : ‖coherentPole x j‖ ≤ ‖coherentPole x 0‖*(1+1/(50*(k:ℝ)))) :
    ‖actualLogTiltAt k x (coherentPole x j)-principalLogTilt k x‖ < (24/25)*(j:ℝ) := by
  simpa only [Int.cast_zero,sub_zero,actualLogTiltAt_principal] using
    actual_logTilt_pole_chord hk hx hj (principal_in_inflated_radius x k) hr

/-- The principal phase correction is half the imaginary chord of its two
adjacent conjugate poles. -/
theorem principalLogTilt_im_bound {k : ℕ} (hk : 7 ≤ k) {x : ℝ}
    (hx : 10*√(k:ℝ) ≤ x) : |(principalLogTilt k x).im| < 12/25 := by
  have hc : coherentPole x (-1) = (starRingEnd ℂ) (coherentPole x 0) := by
    simpa using coherentPole_conj x 0
  have hlo : ‖coherentPole x (-1)‖ ≤ ‖coherentPole x 0‖*(1+1/(50*(k:ℝ))) := by
    rw [hc,Complex.norm_conj]
    exact principal_in_inflated_radius x k
  have h := actual_logTilt_pole_chord hk hx (by decide : (-1:ℤ) < 0)
    hlo (principal_in_inflated_radius x k)
  have hconj : actualLogTiltAt k x (coherentPole x (-1)) =
      (starRingEnd ℂ) (principalLogTilt k x) := by
    rw [hc,←actualLogTiltAt_principal]
    exact conjugate_logPolyAt (k-1) (cutoffLogCoefficient k (-Real.exp (-x))) _
  rw [hconj,actualLogTiltAt_principal] at h
  let z := principalLogTilt k x
  have he : z-(starRingEnd ℂ) z = ((2*z.im:ℝ):ℂ)*Complex.I := by
    apply Complex.ext
    · simp [Complex.sub_re,Complex.conj_re,Complex.mul_I_re]
    · simp [Complex.sub_im,Complex.conj_im,Complex.mul_I_im]
      ring
  change ‖z-(starRingEnd ℂ) z‖ < _ at h
  rw [he,norm_mul,Complex.norm_real,Complex.norm_I,mul_one,Real.norm_eq_abs,abs_mul] at h
  norm_num at h
  linarith only [h]

theorem actual_logTilt_far_exp_ratio {k : ℕ} (hk : 7 ≤ k) {x : ℝ}
    (hx : 10*√(k:ℝ) ≤ x) {j : ℤ} (hj : 0 < j)
    (hr : ‖coherentPole x j‖ ≤ ‖coherentPole x 0‖*(1+1/(50*(k:ℝ)))) :
    ‖Complex.exp (actualLogTiltAt k x (coherentPole x j)) /
      Complex.exp (principalLogTilt k x)‖ < Real.exp ((24/25)*(j:ℝ)) := by
  rw [←Complex.exp_sub, Complex.norm_exp]
  apply Real.exp_lt_exp.mpr
  exact (le_abs_self _).trans_lt ((Complex.abs_re_le_norm _).trans_lt
    (actual_logTilt_far_pole hk hx hj hr))

#print axioms actualLogTiltAt_principal
#print axioms actual_logTilt_pole_chord
#print axioms actual_logTilt_far_pole
#print axioms principalLogTilt_im_bound
#print axioms actual_logTilt_far_exp_ratio
end RepositoryQuotientAudit
