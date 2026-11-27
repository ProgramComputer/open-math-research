import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open scoped Real
open Real

theorem phase_readout_cis (G : ℂ) (θ : ℝ) (m : ℕ) :
    let a := Complex.exp G * Complex.exp (-(θ:ℂ)*Complex.I)^m /
      (‖Complex.exp G‖ : ℂ)
    a.re = Real.cos ((m:ℝ)*θ-G.im) ∧
      a.im = -Real.sin ((m:ℝ)*θ-G.im) := by
  dsimp only
  rw [← Complex.exp_nat_mul, ← Complex.exp_add, Complex.norm_exp]
  let H := G + (m:ℂ) * (-(θ:ℂ)*Complex.I)
  change (Complex.exp H / (Real.exp G.re : ℂ)).re = _ ∧
    (Complex.exp H / (Real.exp G.re : ℂ)).im = _
  have hr : H.re = G.re := by
    simp [H, Complex.add_re, mul_assoc, Complex.mul_I_re, Complex.mul_im]
  have hi : H.im = -((m:ℝ)*θ-G.im) := by
    simp [H, Complex.add_im, mul_assoc, Complex.mul_I_im, Complex.mul_re, Complex.mul_im]
    ring
  have hp : (Real.exp G.re) ≠ 0 := (Real.exp_pos _).ne'
  rw [div_eq_mul_inv, ← Complex.ofReal_inv]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, zero_add, add_zero, Complex.exp_re, Complex.exp_im,
    hr, hi, Real.cos_neg, Real.sin_neg]
  constructor <;> field_simp [hp] <;> ring

noncomputable def angleCoordinate (θ : ℝ) : ℝ := π * (cos θ / sin θ)

theorem angular_pole_geometry {θ : ℝ} (ha : π/6 ≤ θ) (hb : θ ≤ π/2) :
    let x := angleCoordinate θ
    let w : ℂ := (x:ℂ) + (π:ℂ)*Complex.I
    0 ≤ x ∧ 0 < ‖w‖ ∧ ‖w‖ ≤ 2*π ∧
      ‖w‖ = π/sin θ ∧ w = ((π/sin θ:ℝ):ℂ)*Complex.exp ((θ:ℂ)*Complex.I) ∧
      (‖w‖:ℂ)/w = Complex.exp (-(θ:ℂ)*Complex.I) := by
  dsimp only
  let x := angleCoordinate θ
  let w : ℂ := (x:ℂ) + (π:ℂ)*Complex.I
  let r := π/sin θ
  have hsin : 1/2 ≤ sin θ := by
    rw [← sin_pi_div_six]
    exact sin_le_sin_of_le_of_le_pi_div_two (by linarith [pi_pos]) hb ha
  have hsin₀ : 0 < sin θ := by linarith
  have hr : 0 < r := div_pos pi_pos hsin₀
  have hx : 0 ≤ x := by
    exact mul_nonneg pi_pos.le (div_nonneg
      (cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], hb⟩) hsin₀.le)
  have hw : w = (r:ℂ)*Complex.exp ((θ:ℂ)*Complex.I) := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    apply Complex.ext
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_I_re,
        Complex.ofReal_im, neg_zero, add_zero, Complex.mul_re,
        Complex.add_im, Complex.mul_I_im, zero_mul, sub_zero]
      dsimp [x,r,angleCoordinate,w]
      ring
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_I_im,
        Complex.ofReal_re, zero_add, Complex.mul_im, zero_mul, add_zero]
      dsimp [w,r]
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_I_im, Complex.ofReal_re, zero_add]
      field_simp
  have hnorm : ‖w‖ = r := by
    rw [hw,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr,
      Complex.norm_exp_ofReal_mul_I,mul_one]
  refine ⟨hx,hnorm ▸ hr,?_,hnorm,hw,?_⟩
  · rw [hnorm]
    exact (div_le_iff₀ hsin₀).2 (by nlinarith [mul_nonneg pi_pos.le (sub_nonneg.mpr hsin)])
  · change (‖w‖:ℂ)/w = _
    rw [hnorm,hw,div_mul_eq_div_div,div_self (by exact_mod_cast hr.ne'),
      one_div, ← Complex.exp_neg, neg_mul]

#print axioms phase_readout_cis
#print axioms angular_pole_geometry
end OpenMathResearch.LongCycleExcedances
