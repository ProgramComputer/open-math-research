import PairedSineComparison
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.NormNum

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances

/-- Multiplying by the literal signed pole denominator produces a single
elliptical trigonometric factor. -/
theorem paired_sine_pole_identity (a v z : ℝ)
    (hw : ((Real.cos z : ℂ) + Complex.I*a*Real.sin z) ≠ 0) :
    (Real.sin (v+z):ℂ) - ((Real.cos z : ℂ)+Complex.I*a*Real.sin z)⁻¹*Real.sin v =
    (Real.sin z:ℂ)*((Real.cos z : ℂ)+Complex.I*a*Real.sin z)⁻¹*
      ((Real.cos (v+z):ℂ) + Complex.I*a*Real.sin (v+z)) := by
  have hreal : Real.sin (v+z)*Real.cos z-Real.sin v = Real.cos (v+z)*Real.sin z := by
    have h := Real.sin_sub (v+z) z
    rw [add_sub_cancel_right] at h
    linarith only [h]
  have h : (Real.sin (v+z):ℂ)*Real.cos z-Real.sin v =
      (Real.cos (v+z):ℂ)*Real.sin z := by exact_mod_cast hreal
  let w : ℂ := (Real.cos z:ℂ)+Complex.I*a*Real.sin z
  have hw' : w ≠ 0 := hw
  have hn : w*(Real.sin (v+z):ℂ)-Real.sin v =
      (Real.sin z:ℂ)*((Real.cos (v+z):ℂ)+Complex.I*a*Real.sin (v+z)) := by
    dsimp only [w]
    linear_combination h
  change _ - w⁻¹*_ = _*w⁻¹*_
  calc
    _ = w⁻¹*(w*(Real.sin (v+z):ℂ)-Real.sin v) := by
      rw [mul_sub,←mul_assoc,inv_mul_cancel₀ hw',one_mul]
    _ = _ := by rw [hn]; ring

theorem paired_sine_ellipse_bound (a v : ℝ) (ha : 1 ≤ |a|) :
    ‖(Real.cos v:ℂ) + Complex.I*a*Real.sin v‖ ≤ |a| := by
  have hquad := Real.sin_sq_add_cos_sq v
  have hsq : 1 ≤ a^2 := by nlinarith only [sq_abs a, sq_nonneg (|a|-1),ha]
  have he := mul_le_mul_of_nonneg_right hsq (sq_nonneg (Real.cos v))
  have hcalc : ‖(Real.cos v:ℂ)+ Complex.I*a*Real.sin v‖^2 ≤ |a|^2 := by
    rw [Complex.sq_norm,Complex.normSq_apply,sq_abs]
    simp only [Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,zero_mul,one_mul,
      mul_zero,mul_one,zero_add,add_zero,sub_zero,sub_self,zero_sub]
    nlinarith only [he,congrArg (fun b : ℝ => a^2*b) hquad]
  nlinarith only [hcalc,norm_nonneg ((Real.cos v:ℂ)+ Complex.I*a*Real.sin v),abs_nonneg a,
    sq_nonneg (‖(Real.cos v:ℂ)+ Complex.I*a*Real.sin v‖-|a|)]

theorem paired_sine_pole_bound (a v z : ℝ) (ha : 1 ≤ |a|) (hS : 0 ≤ Real.sin z)
    (hw : ((Real.cos z : ℂ) + Complex.I*a*Real.sin z) ≠ 0) :
    ‖(Real.sin (v+z):ℂ) - ((Real.cos z : ℂ)+Complex.I*a*Real.sin z)⁻¹*Real.sin v‖ ≤
      Real.sin z * ‖((Real.cos z : ℂ)+Complex.I*a*Real.sin z)⁻¹‖ * |a| := by
  rw [paired_sine_pole_identity a v z hw,norm_mul,norm_mul,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg hS]
  exact mul_le_mul_of_nonneg_left (paired_sine_ellipse_bound a (v+z) ha)
    (mul_nonneg hS (norm_nonneg _))

/-- Transfer one distinguished occupied term between consecutive degrees.
The common factor may include an integer power and an arbitrary product coefficient. -/
theorem paired_sine_occupied_term (a v z d b : ℝ) (T : ℂ) (ha : 1 ≤ |a|)
    (hS : 0 ≤ Real.sin z) (hw : ((Real.cos z:ℂ)+Complex.I*a*Real.sin z) ≠ 0) :
    let p := ((Real.cos z:ℂ)+Complex.I*a*Real.sin z)⁻¹
    ‖(Real.sin (v+z):ℂ)*(T*d)-(Real.sin v:ℂ)*(T*p*(d+b))‖ ≤
      ‖T‖*‖p‖*(Real.sin z* |a| * |d|+|b|) := by
  let p := ((Real.cos z:ℂ)+Complex.I*a*Real.sin z)⁻¹
  change ‖(Real.sin (v+z):ℂ)*(T*d)-(Real.sin v:ℂ)*(T*p*(d+b))‖ ≤ _
  have hcoeff :
      (Real.sin (v+z):ℂ)*(T*d)-(Real.sin v:ℂ)*(T*p*(d+b)) =
        T*((d:ℂ)*((Real.sin (v+z):ℂ)-p*Real.sin v)-(b:ℂ)*p*Real.sin v) := by ring
  rw [hcoeff,norm_mul]
  have hd := paired_sine_pole_bound a v z ha hS hw
  have hs : |Real.sin v| ≤ 1 := by
    exact abs_le.mpr ⟨Real.neg_one_le_sin _,Real.sin_le_one _⟩
  calc
    _ ≤ ‖T‖*(‖(d:ℂ)*((Real.sin (v+z):ℂ)-p*Real.sin v)‖+‖(b:ℂ)*p*Real.sin v‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _)
    _ ≤ ‖T‖*(|d| * (Real.sin z*‖p‖* |a|)+|b| * ‖p‖) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs]
      apply add_le_add (mul_le_mul_of_nonneg_left hd (abs_nonneg _))
      exact mul_le_of_le_one_right (mul_nonneg (abs_nonneg _) (norm_nonneg _)) hs
    _ = _ := by ring

#print axioms paired_sine_occupied_term
#print axioms paired_sine_pole_identity
#print axioms paired_sine_ellipse_bound
#print axioms paired_sine_pole_bound
end OpenMathResearch.LongCycleExcedances
