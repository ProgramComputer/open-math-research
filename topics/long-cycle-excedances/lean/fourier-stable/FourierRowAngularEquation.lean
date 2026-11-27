import FourierCutoffLogSlope
import Mathlib.MeasureTheory.Integral.CircleIntegral

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Complex Real Set

/-- Multiplication by the angular velocity shifts the remainder from degree
k−1 to frequency k. The radius in the residues is the integration radius. -/
theorem angular_cutoff_remainder {ι : Type*} (P : ι→ℂ) (d : ℕ) (R x : ℝ) :
    circleMap 0 R x * (∑' i, (circleMap 0 R x)^d/(P i^d*(P i-circleMap 0 R x))) =
    Complex.exp (((d+1:ℕ):ℂ)*I*(x:ℂ)) *
      (∑' i, (((R:ℂ)^(d+1))/P i^d)/(P i-circleMap 0 R x)) := by
  let w := circleMap 0 R x
  have hw : w^(d+1) = (R:ℂ)^(d+1)*Complex.exp (((d+1:ℕ):ℂ)*I*(x:ℂ)) := by
    dsimp [w,circleMap]
    rw [zero_add,mul_pow,←Complex.exp_nat_mul]
    congr 2
    ring
  rw [←tsum_mul_left,←tsum_mul_left]
  apply tsum_congr
  intro i
  change w*(w^d/(P i^d*(P i-w)))=_
  rw [←mul_div_assoc,←pow_succ',hw]
  dsimp only [w]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

/-- The exact differential equation required by the first Fourier integration. -/
theorem angular_finite_fourier_row (s R : ℝ) (m : ℕ) (b : ℕ→ℂ)
    (hreal : ∀ x : ℝ, x < s → inverseSquarePoleSum (fourierRowPole s) (x:ℂ) =
      -Complex.exp ((x:ℂ)-s)/(1+Complex.exp ((x:ℂ)-s))^2)
    (hb1 : b 1 = Complex.exp (-(s:ℂ))/(1+Complex.exp (-(s:ℂ))))
    (hb : ∀ j < m, b (j+2)*((j+2:ℕ):ℂ) = -(∑' i, (1:ℂ)/fourierRowPole s i^(j+2)))
    (x : ℝ) (hw : circleMap 0 R x ∉ range (fourierRowPole s)) :
    let f := fun z : ℂ => Complex.exp (finiteFourierLog m b z)/(1+Complex.exp (z-s))
    let w := circleMap 0 R x
    HasDerivAt (fun y : ℝ => f (circleMap 0 R y))
      (I*Complex.exp (((m+2:ℕ):ℂ)*I*(x:ℂ))*(f w*
        ∑' i, ((R:ℂ)^(m+2)/fourierRowPole s i^(m+1))/(fourierRowPole s i-w))) x := by
  dsimp only
  have h := (finiteFourierQuotient_deriv s m b hreal hb1 hb hw).scomp x (hasDerivAt_circleMap 0 R x)
  apply h.congr_deriv
  rw [smul_eq_mul]
  have he := angular_cutoff_remainder (fourierRowPole s) (m+1) R x
  linear_combination (Complex.I*(Complex.exp (finiteFourierLog m b (circleMap 0 R x))/
    (1+Complex.exp (circleMap 0 R x-s))))*he

#print axioms angular_cutoff_remainder
#print axioms angular_finite_fourier_row
end OpenMathResearch.LongCycleExcedances
