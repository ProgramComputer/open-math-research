import AngularGeometry
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real

theorem angleCoordinate_hasDerivAt {θ : ℝ} (hs : sin θ ≠ 0) :
    HasDerivAt angleCoordinate (-π/(sin θ)^2) θ := by
  have h := ((hasDerivAt_cos θ).div (hasDerivAt_sin θ) hs).const_mul π
  have he : -sin θ*sin θ-cos θ*cos θ = -1 := by
    nlinarith [sin_sq_add_cos_sq θ]
  rw [he, ← mul_div_assoc, mul_neg_one] at h
  exact h

/-- Angular chain rule and conjugate-pole readout. The complex error is the
sum with the two nearest poles removed, before projection to a real phase. -/
theorem angular_phase_remainder {θ : ℝ} (ha : π/6 ≤ θ) (hb : θ ≤ π/2)
    (k : ℕ) {F : ℝ → ℂ} {L : ℝ} {C : ℂ} {B : ℝ}
    (hF : HasDerivAt F ((L:ℂ)+C/((angleCoordinate θ:ℂ)+(π:ℂ)*Complex.I)) (angleCoordinate θ))
    (hTail : ‖C-1-(((angleCoordinate θ:ℂ)+(π:ℂ)*Complex.I)/
      star ((angleCoordinate θ:ℂ)+(π:ℂ)*Complex.I))^k‖ ≤ B) :
    DifferentiableAt ℝ (fun u => (F (angleCoordinate u)).im) θ ∧
    |deriv (fun u => (F (angleCoordinate u)).im) θ - 1 +
        sin ((2*(k:ℝ)-1)*θ)/sin θ| ≤ B/sin θ := by
  let w : ℂ := (angleCoordinate θ:ℂ)+(π:ℂ)*Complex.I
  let z := Complex.exp (-(θ:ℂ)*Complex.I)
  let r := π/sin θ
  have hs : 0 < sin θ := sin_pos_of_pos_of_lt_pi (by linarith [pi_pos]) (by linarith [pi_pos])
  have hr : 0 < r := div_pos pi_pos hs
  have hr₀ : (r:ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  obtain ⟨_,hw₀,_,hnorm,hw,hz⟩ := angular_pole_geometry ha hb
  change ‖w‖ = r at hnorm
  change w = (r:ℂ)*Complex.exp ((θ:ℂ)*Complex.I) at hw
  change (‖w‖:ℂ)/w = z at hz
  rw [hnorm] at hz
  have hD := hF.scomp θ (angleCoordinate_hasDerivAt hs.ne')
  have hγ := Complex.imCLM.hasFDerivAt.comp_hasDerivAt θ hD
  have hder : HasDerivAt (fun u => (F (angleCoordinate u)).im)
      (-(1/sin θ)*(z*C).im) θ := by
    have hzC : C/w = (z*C)/(r:ℂ) := by
      rw [← hz]
      simp only [div_eq_mul_inv]
      calc
        C*w⁻¹ = ((r:ℂ)*(r:ℂ)⁻¹)*(C*w⁻¹) := by rw [mul_inv_cancel₀ hr₀, one_mul]
        _ = _ := by ring
    have he : (-π/(sin θ)^2) * ((L:ℂ)+C/w).im = -(1/sin θ)*(z*C).im := by
      rw [hzC, Complex.add_im, Complex.ofReal_im, zero_add, Complex.div_ofReal_im]
      dsimp [r]
      field_simp [hs.ne',pi_ne_zero] <;> ring
    simp only [Complex.imCLM_apply, Complex.smul_im, smul_eq_mul] at hγ
    change HasDerivAt (fun u => (F (angleCoordinate u)).im)
      ((-π/(sin θ)^2) * ((L:ℂ)+C/w).im) θ at hγ
    rwa [he] at hγ
  have hwconj : star w = (r:ℂ)*z := by
    rw [hw]
    change (starRingEnd ℂ) ((r:ℂ)*Complex.exp ((θ:ℂ)*Complex.I)) = _
    rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
      Complex.conj_I, mul_neg, ← neg_mul]
  have hz₀ : z ≠ 0 := Complex.exp_ne_zero _
  have hc : (z*(w/star w)^k).im = sin ((2*(k:ℝ)-1)*θ) := by
    rw [hwconj, hw, mul_div_mul_left _ _ hr₀]
    change (Complex.exp (-(θ:ℂ)*Complex.I) *
      (Complex.exp ((θ:ℂ)*Complex.I)/Complex.exp (-(θ:ℂ)*Complex.I))^k).im = _
    rw [← Complex.exp_sub, ← Complex.exp_nat_mul, ← Complex.exp_add, Complex.exp_im]
    have he : -(θ:ℂ)*Complex.I + (k:ℂ)*
          ((θ:ℂ)*Complex.I - -(θ:ℂ)*Complex.I) =
        (((2*(k:ℝ)-1)*θ:ℝ):ℂ)*Complex.I := by push_cast; ring
    rw [he, Complex.mul_I_re, Complex.ofReal_im, neg_zero, exp_zero, one_mul,
      Complex.mul_I_im, Complex.ofReal_re]
  have hzi : z.im = -sin θ := by
    dsimp [z]
    rw [Complex.exp_im, Complex.mul_I_re, Complex.mul_I_im, Complex.neg_re,
      Complex.neg_im, Complex.ofReal_im, neg_zero, neg_zero, exp_zero, one_mul,
      Complex.ofReal_re, sin_neg]
  let E := C-1-(w/star w)^k
  have hNorm : |(z*E).im| ≤ B := by
    apply (Complex.abs_im_le_norm _).trans
    rw [norm_mul, show ‖z‖ = 1 by
      dsimp [z]; rw [← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I],one_mul]
    exact hTail
  have hsplit : (z*C).im = -sin θ + sin ((2*(k:ℝ)-1)*θ)+(z*E).im := by
    rw [show z*C = z+z*(w/star w)^k+z*E by dsimp [E]; ring,
      Complex.add_im, Complex.add_im, hzi,hc]
  refine ⟨hder.differentiableAt, ?_⟩
  rw [hder.deriv, hsplit,
    show -(1/sin θ)*(-sin θ+sin ((2*(k:ℝ)-1)*θ)+(z*E).im) - 1 +
      sin ((2*(k:ℝ)-1)*θ)/sin θ = -(z*E).im/sin θ by field_simp [hs.ne']; ring,
    abs_div, abs_neg, abs_of_pos hs]
  exact div_le_div_of_nonneg_right hNorm hs.le

#print axioms angular_phase_remainder
end OpenMathResearch.LongCycleExcedances
