import FourierCircleShift

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real MeasureTheory

private theorem wave_zero_index (x : ℝ) : circleWave 0 x=1 := by simp [circleWave]

theorem fourier_modulation (f : ℝ → ℂ) (j k : ℤ) :
    normalizedFourierIntegral (fun x => circleWave k x*f x) j =
      normalizedFourierIntegral f (j-k) := by
  unfold normalizedFourierIntegral
  congr 1
  apply intervalIntegral.integral_congr
  intro x _
  change circleWave (-j) x*(circleWave k x*f x) = circleWave (-(j-k)) x*f x
  rw [←mul_assoc,circleWave_add,show -j+k = -(j-k) by omega]

theorem fourier_linear_pair {f g : ℝ→ℂ} (hf : Continuous f) (hg : Continuous g)
    (a b : ℂ) (j : ℤ) :
    normalizedFourierIntegral (fun x => a*f x+b*g x) j =
      a*normalizedFourierIntegral f j+b*normalizedFourierIntegral g j := by
  let w := circleWave (-j)
  have h (x:ℝ) : w x*(a*f x+b*g x)=a*(w x*f x)+b*(w x*g x) := by ring
  change (∫ x in (0:ℝ)..2*π,w x*(a*f x+b*g x))/(2*(π:ℂ)) = _
  simp_rw [h]
  have cw : Continuous w := circleWave_continuous _
  have hadd : (∫ x in (0:ℝ)..2*π, a*(w x*f x)+b*(w x*g x)) =
      (∫ x in (0:ℝ)..2*π, a*(w x*f x)) + (∫ x in (0:ℝ)..2*π, b*(w x*g x)) :=
    intervalIntegral.integral_add (f := fun x => a*(w x*f x)) (g := fun x => b*(w x*g x))
      ((continuous_const.mul (cw.mul hf)).intervalIntegrable _ _)
      ((continuous_const.mul (cw.mul hg)).intervalIntegrable _ _)
  rw [hadd,intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]
  unfold normalizedFourierIntegral
  dsimp only [w]
  ring

/-- Exact second integration for a product with a pole kernel.  The factor
B can be the unweighted kernel D or its contrast-weighted version. -/
theorem fourier_kernel_second {f D B E : ℝ→ℂ} (k m : ℤ)
    (hf0 : f (2*π)=f 0) (hb0 : B (2*π)=B 0)
    (hD : Continuous D) (hE : Continuous E)
    (hf : ∀ x, HasDerivAt f (Complex.I*circleWave k x*(f x*D x)) x)
    (hB : ∀ x, HasDerivAt B (Complex.I*E x) x) :
    (m:ℂ)*normalizedFourierIntegral (fun x => f x*B x) m =
      normalizedFourierIntegral (fun x => f x*(circleWave k x*D x*B x+E x)) m := by
  have cf := continuous_iff_continuousAt.mpr (fun x => (hf x).continuousAt)
  have cb := continuous_iff_continuousAt.mpr (fun x => (hB x).continuousAt)
  have hs := shifted_periodic_derivative (f:=fun x => f x*B x)
    (g:=fun x => f x*(circleWave k x*D x*B x+E x)) 0 m (by simp only [hf0,hb0])
    (cf.mul ((((circleWave_continuous _).mul hD).mul cb).add hE))
    (fun x => ((hf x).mul (hB x)).congr_deriv (by rw [wave_zero_index]; ring))
  simpa only [sub_zero] using hs

theorem fourier_old_row_twice {f D E : ℝ→ℂ} (j k : ℤ)
    (hf0 : f (2*π)=f 0) (hd0 : D (2*π)=D 0) (hE : Continuous E)
    (hf : ∀ x, HasDerivAt f (Complex.I*circleWave k x*(f x*D x)) x)
    (hD : ∀ x, HasDerivAt D (Complex.I*E x) x) :
    ((j-k:ℤ):ℂ)*(j:ℂ)*normalizedFourierIntegral f j =
      normalizedFourierIntegral (fun x => f x*(circleWave k x*D x*D x+E x)) (j-k) := by
  have cf := continuous_iff_continuousAt.mpr (fun x => (hf x).continuousAt)
  have cd := continuous_iff_continuousAt.mpr (fun x => (hD x).continuousAt)
  rw [mul_assoc,shifted_periodic_derivative k j hf0 (cf.mul cd) hf]
  exact fourier_kernel_second k (j-k) hf0 hd0 cd hE hf hD

#print axioms fourier_modulation
#print axioms fourier_linear_pair
#print axioms fourier_kernel_second
#print axioms fourier_old_row_twice
end OpenMathResearch.LongCycleExcedances
