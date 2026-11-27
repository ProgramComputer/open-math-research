import UniformHighDegreeLattice
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Real.Pi.Bounds

noncomputable section

namespace OpenMathResearch.LongCycleExcedances

/-- The odd pole at integer index l has imaginary height (2l+1)π. -/
def uniformTiltPole (x : ℝ) (l : ℤ) : ℂ :=
  (x:ℂ) + (2*(l:ℂ)+1)*Real.pi*Complex.I

private theorem uniformTiltPole_re (x : ℝ) (l : ℤ) :
    (uniformTiltPole x l).re = x := by
  simp [uniformTiltPole, Complex.add_re, Complex.mul_I_re, Complex.mul_im]

private theorem uniformTiltPole_im (x : ℝ) (l : ℤ) :
    (uniformTiltPole x l).im = (2*(l:ℝ)+1)*Real.pi := by
  simp [uniformTiltPole, Complex.add_im, Complex.mul_I_im, Complex.mul_re, Complex.add_re]

private theorem uniformTiltPole_pos (x : ℝ) (l : ℤ) : 0 < ‖uniformTiltPole x l‖ := by
  apply norm_pos_iff.mpr
  intro hz
  have ho : (2*(l:ℝ)+1) ≠ 0 := by
    exact_mod_cast (show (2*l+1:ℤ) ≠ 0 by omega)
  exact (mul_ne_zero ho Real.pi_ne_zero) (by simpa [hz] using (uniformTiltPole_im x l).symm)

private theorem uniformTiltPole_sq (x : ℝ) (l : ℤ) :
    ‖uniformTiltPole x l‖^2 = x^2+((2*(l:ℝ)+1)*Real.pi)^2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, uniformTiltPole_re, uniformTiltPole_im]
  ring

private def uniformTiltPoleRatio (x : ℝ) (l : ℤ) : ℝ :=
  ‖uniformTiltPole x 0‖ / ‖uniformTiltPole x l‖

private theorem uniformTiltPoleRatio_nonneg (x : ℝ) (l : ℤ) :
    0 ≤ uniformTiltPoleRatio x l := div_nonneg (norm_nonneg _) (norm_nonneg _)

private theorem uniformTiltPoleRatio_zero (x : ℝ) :
    uniformTiltPoleRatio x 0 = 1 := div_self (uniformTiltPole_pos x 0).ne'

private theorem uniformTiltPoleRatio_sym (x : ℝ) (j : ℕ) :
    uniformTiltPoleRatio x (-((j:ℤ)+1)) = uniformTiltPoleRatio x (j:ℤ) := by
  have h : ‖uniformTiltPole x (-((j:ℤ)+1))‖^2 = ‖uniformTiltPole x (j:ℤ)‖^2 := by
    rw [uniformTiltPole_sq, uniformTiltPole_sq]
    push_cast
    ring
  unfold uniformTiltPoleRatio
  rw [(sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h]

private theorem uniformTiltPoleRatio_geometry (x : ℝ) (j : ℕ) :
    let r := ‖uniformTiltPole x 0‖
    (uniformTiltPoleRatio x ((j+1:ℕ):ℤ))^2*
      (1+4*((j:ℝ)+1)*((j:ℝ)+2)*(Real.pi/r)^2) ≤ 1 := by
  let r := ‖uniformTiltPole x 0‖
  let W := ‖uniformTiltPole x ((j+1:ℕ):ℤ)‖
  have hr : 0 < r := uniformTiltPole_pos x 0
  have hW : 0 < W := uniformTiltPole_pos x _
  have hr2 : r^2 = x^2+Real.pi^2 := by simpa [r] using uniformTiltPole_sq x 0
  have hW2 : W^2 = r^2+4*((j:ℝ)+1)*((j:ℝ)+2)*Real.pi^2 := by
    dsimp only [W]
    rw [uniformTiltPole_sq, hr2]
    push_cast
    ring
  have hp : r^2*(1+4*((j:ℝ)+1)*((j:ℝ)+2)*(Real.pi/r)^2) = W^2 := by
    rw [hW2]
    field_simp [hr.ne']
  change (r/W)^2*(1+4*((j:ℝ)+1)*((j:ℝ)+2)*(Real.pi/r)^2) ≤ 1
  rw [div_pow, div_mul_eq_mul_div, hp, div_self (pow_ne_zero _ hW.ne')]

/-- The high-degree odd-pole bound holds even below sin θ = 1/2. -/
theorem uniform_high_degree_odd_poles (x : ℝ) {ell : ℕ} (hel : 7 ≤ ell)
    (hscale : (1:ℝ)/2 ≤ ell*(Real.pi/‖uniformTiltPole x 0‖)^2) :
    Summable (fun l : ℤ => ‖uniformTiltPole x 0 / uniformTiltPole x l‖^ell) ∧
      (∑' l : ℤ, ‖uniformTiltPole x 0 / uniformTiltPole x l‖^ell) ≤ 13/3 := by
  simpa only [norm_div, uniformTiltPoleRatio] using
    uniform_high_degree_lattice hel hscale (uniformTiltPoleRatio x)
      (uniformTiltPoleRatio_nonneg x) (uniformTiltPoleRatio_zero x)
      (uniformTiltPoleRatio_sym x) (uniformTiltPoleRatio_geometry x)

/-- On the bounded logarithmic interval every degree at least two has odd-pole
mass at most eight. -/
theorem uniform_small_modulus_odd_poles {x : ℝ} (hx : 0 ≤ x) (hmax : x ≤ 10)
    {ell : ℕ} (hel : 2 ≤ ell) :
    Summable (fun l : ℤ => ‖uniformTiltPole x 0 / uniformTiltPole x l‖^ell) ∧
      (∑' l : ℤ, ‖uniformTiltPole x 0 / uniformTiltPole x l‖^ell) ≤ 8 := by
  let r := ‖uniformTiltPole x 0‖
  have hr : 0 < r := uniformTiltPole_pos x 0
  have hS : 0 < Real.pi/r := div_pos Real.pi_pos hr
  obtain ⟨hs, h⟩ := square_majorized_lattice hS hel (uniformTiltPoleRatio x)
    (uniformTiltPoleRatio_nonneg x) (uniformTiltPoleRatio_zero x)
    (uniformTiltPoleRatio_sym x) (uniformTiltPoleRatio_geometry x)
  have hp : (31:ℝ)/10 < Real.pi := by linarith [Real.pi_gt_d2]
  have hπ : (100:ℝ)/11 ≤ Real.pi^2 := by
    nlinarith only [mul_pos (sub_pos.mpr hp) (show 0 < Real.pi+31/10 by positivity)]
  have hx2 : x^2 ≤ 100 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hmax) (show 0 ≤ 10+x by positivity)]
  have hr2 : r^2 = x^2+Real.pi^2 := by simpa [r] using uniformTiltPole_sq x 0
  have hfrac : 1/(2*(Real.pi/r)^2) = r^2/(2*Real.pi^2) := by
    field_simp [hr.ne', Real.pi_ne_zero]
  have hbound : 2+1/(2*(Real.pi/r)^2) ≤ (8:ℝ) := by
    rw [hfrac]
    have hq : r^2/(2*Real.pi^2) ≤ 6 := by
      apply (div_le_iff₀ (by positivity : (0:ℝ) < 2*Real.pi^2)).2
      nlinarith only [hπ, hx2, hr2]
    linarith only [hq]
  simpa only [norm_div, uniformTiltPoleRatio] using And.intro hs (h.trans hbound)

/-- Degrees beyond the cut in the large-x tilt split meet the hypotheses
of the elementary pole bound. -/
theorem uniform_high_degree_scale_of_cut {x : ℝ} (hx : 10 ≤ x) {ell : ℕ}
    (hell : x^2/16 < (ell:ℝ)) :
    7 ≤ ell ∧ (1:ℝ)/2 ≤ ell*(Real.pi/‖uniformTiltPole x 0‖)^2 := by
  have hx2 : 100 ≤ x^2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hx) (show 0 ≤ x+10 by linarith)]
  constructor
  · by_contra! hb
    have hd : (ell:ℝ) ≤ 6 := by exact_mod_cast (show ell ≤ 6 by omega)
    linarith only [hell, hx2, hd]
  · have hpi2 : 9 < Real.pi^2 := by
      nlinarith only [mul_pos (sub_pos.mpr Real.pi_gt_three) (show 0 < Real.pi+3 by positivity)]
    have hw := uniformTiltPole_pos x 0
    rw [div_pow, ← mul_div_assoc, le_div_iff₀ (pow_pos hw 2)]
    rw [show ‖uniformTiltPole x 0‖^2 = x^2+Real.pi^2 by simpa using uniformTiltPole_sq x 0]
    have hp := mul_nonneg (sub_nonneg.mpr hx2) (show 0 ≤ Real.pi^2-8 by linarith)
    have hn := mul_lt_mul_of_pos_right hell (show 0 < Real.pi^2 by positivity)
    nlinarith only [hp, hn, hpi2]

#print axioms uniform_high_degree_odd_poles
#print axioms uniform_small_modulus_odd_poles
#print axioms uniform_high_degree_scale_of_cut
end OpenMathResearch.LongCycleExcedances
