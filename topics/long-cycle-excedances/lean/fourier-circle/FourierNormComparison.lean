import FourierAdjacentIdentity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real MeasureTheory

private theorem circleWave_norm (j : ℤ) (x : ℝ) : ‖circleWave j x‖ = 1 := by
  rw [circleWave, Complex.norm_exp]
  simp [Complex.mul_re,Complex.mul_im]

/-- The doubly integrated coefficient is controlled by the product and
derivative masses in normalized angular measure. The same estimate applies
to the old row and the adjacent-row contrast. -/
theorem fourier_kernel_error {f D B E : ℝ → ℂ} {M U V : ℝ}
    (cf : Continuous f) (cd : Continuous D) (cb : Continuous B) (ce : Continuous E)
    (hM : 0 ≤ M) (hf : ∀ x, ‖f x‖ ≤ M)
    (hprod : (∫ x in (0:ℝ)..2*π, ‖D x*B x‖) ≤ 2*π*U)
    (hder : (∫ x in (0:ℝ)..2*π, ‖E x‖) ≤ 2*π*V) (k j : ℤ) :
    ‖normalizedFourierIntegral (fun x => f x*(circleWave k x*D x*B x+E x)) j‖ ≤
      M*(U+V) := by
  let g := fun x => circleWave (-j) x*(f x*(circleWave k x*D x*B x+E x))
  let major := fun x : ℝ => M*(‖D x*B x‖+‖E x‖)
  have hg : Continuous g := (circleWave_continuous _).mul
    (cf.mul ((((circleWave_continuous _).mul cd).mul cb).add ce))
  have hm : Continuous major := continuous_const.mul ((cd.mul cb).norm.add ce.norm)
  have hle (x : ℝ) : ‖g x‖ ≤ major x := by
    dsimp only [g,major]
    rw [norm_mul,circleWave_norm,one_mul,norm_mul]
    apply mul_le_mul (hf x) _ (norm_nonneg _) hM
    exact (norm_add_le _ _).trans (by rw [mul_assoc,norm_mul,circleWave_norm,one_mul])
  have hi := (intervalIntegral.norm_integral_le_integral_norm (μ:=volume) (f:=g) Real.two_pi_pos.le).trans
    (intervalIntegral.integral_mono_on Real.two_pi_pos.le (hg.norm.intervalIntegrable _ _)
      (hm.intervalIntegrable _ _) (fun x _ => hle x))
  have he : (∫ x in (0:ℝ)..2*π, major x) ≤ (2*π)*(M*(U+V)) := by
    dsimp only [major]
    have hadd : (∫ x in (0:ℝ)..2*π, ‖D x*B x‖+‖E x‖) =
        (∫ x in (0:ℝ)..2*π, ‖D x*B x‖) + (∫ x in (0:ℝ)..2*π, ‖E x‖) :=
      intervalIntegral.integral_add (f := fun x => ‖D x*B x‖) (g := fun x => ‖E x‖)
        ((cd.mul cb).norm.intervalIntegrable _ _) (ce.norm.intervalIntegrable _ _)
    rw [intervalIntegral.integral_const_mul,hadd]
    exact (mul_le_mul_of_nonneg_left (add_le_add hprod hder) hM).trans_eq (by ring)
  unfold normalizedFourierIntegral
  rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  norm_num
  exact (div_le_iff₀ Real.two_pi_pos).mpr (by simpa only [mul_comm (2*π)] using hi.trans he)

theorem fourier_old_coefficient_bound {f D E : ℝ → ℂ} {M U V : ℝ} (j k : ℤ)
    (hf0 : f (2*π) = f 0) (hd0 : D (2*π) = D 0) (ce : Continuous E)
    (hf : ∀ x, HasDerivAt f (Complex.I*circleWave k x*(f x*D x)) x)
    (hd : ∀ x, HasDerivAt D (Complex.I*E x) x) (hM : 0 ≤ M) (hmax : ∀ x, ‖f x‖ ≤ M)
    (hu : (∫ x in (0:ℝ)..2*π, ‖D x * D x‖) ≤ 2*π*U)
    (hv : (∫ x in (0:ℝ)..2*π, ‖E x‖) ≤ 2*π*V) :
    ‖((j-k : ℤ) : ℂ)*(j : ℂ)*normalizedFourierIntegral f j‖ ≤ M*(U+V) := by
  have cf := continuous_iff_continuousAt.mpr (fun x => (hf x).continuousAt)
  have cd := continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)
  rw [fourier_old_row_twice j k hf0 hd0 ce hf hd]
  exact fourier_kernel_error cf cd cd ce hM hmax hu hv k (j-k)

/-- The frequency-shift and endpoint corrections keep their own amplitudes.
Their magnitudes are taken only after the two signed integrations. -/
theorem fourier_adjacent_coefficient_bound {f D B E : ℝ → ℂ} {M U V : ℝ}
    (n k : ℤ) (a C A : ℂ) (hf0 : f (2*π) = f 0) (hb0 : B (2*π) = B 0)
    (cd : Continuous D) (ce : Continuous E)
    (hf : ∀ x, HasDerivAt f (Complex.I*circleWave k x*(f x*D x)) x)
    (hb : ∀ x, HasDerivAt B (Complex.I*E x) x)
    (hsplit : ∀ x, (a*circleWave (-1) x-C)*D x = B x + A*circleWave (-1) x)
    (hM : 0 ≤ M) (hmax : ∀ x, ‖f x‖ ≤ M)
    (hu : (∫ x in (0:ℝ)..2*π, ‖D x*B x‖) ≤ 2*π*U)
    (hv : (∫ x in (0:ℝ)..2*π, ‖E x‖) ≤ 2*π*V) :
    ‖((n-k : ℤ) : ℂ)*(n : ℂ)*(a*normalizedFourierIntegral f (n+1)-C*normalizedFourierIntegral f n)‖ ≤
      M*(U+V) + ‖((n-k : ℤ) : ℂ)*A*normalizedFourierIntegral f (n+1-k)‖
        + ‖((n-k : ℤ) : ℂ)*a*normalizedFourierIntegral f (n+1)‖ := by
  have cf := continuous_iff_continuousAt.mpr (fun x => (hf x).continuousAt)
  have cb := continuous_iff_continuousAt.mpr (fun x => (hb x).continuousAt)
  rw [fourier_adjacent_twice n k a C A hf0 hb0 cd ce hf hb hsplit]
  apply (norm_sub_le _ _).trans
  apply add_le_add_right
  exact (norm_add_le _ _).trans (add_le_add_right
    (fourier_kernel_error cf cd cb ce hM hmax hu hv k (n-k)) _)

#print axioms fourier_old_coefficient_bound
#print axioms fourier_adjacent_coefficient_bound
#print axioms fourier_kernel_error
end OpenMathResearch.LongCycleExcedances
