import FourierAnchoredLogistic
import FourierGeometricRemainder
import Mathlib.Analysis.Calculus.Deriv.Pow

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Complex Real Set Finset

/-- The finite log tilt written in the same degree order as the original
coefficient identity. The cutoff is m+2, so the highest degree is m+1. -/
def finiteFourierLog (m : ℕ) (b : ℕ → ℂ) (w : ℂ) : ℂ :=
  ∑ i ∈ range (m+1), b (i+1)*w^(i+1)

def finiteFourierSlope (m : ℕ) (b : ℕ → ℂ) (w : ℂ) : ℂ :=
  ∑ i ∈ range (m+1), (b (i+1)*((i+1:ℕ):ℂ))*w^i

theorem finiteFourierLog_deriv (m : ℕ) (b : ℕ→ℂ) (w : ℂ) :
    HasDerivAt (finiteFourierLog m b) (finiteFourierSlope m b w) w := by
  apply HasDerivAt.fun_sum
  intro i _
  apply ((hasDerivAt_pow (i+1) w).const_mul (b (i+1))).congr_deriv
  simp [mul_assoc]

theorem finiteFourierSlope_remainder (s : ℝ) (m : ℕ) (b : ℕ→ℂ)
    (hreal : ∀ x : ℝ, x < s → inverseSquarePoleSum (fourierRowPole s) (x:ℂ) =
      -Complex.exp ((x:ℂ)-s)/(1+Complex.exp ((x:ℂ)-s))^2)
    (hb1 : b 1 = Complex.exp (-(s:ℂ))/(1+Complex.exp (-(s:ℂ))))
    (hb : ∀ j < m, b (j+2)*((j+2:ℕ):ℂ) = -(∑' i, (1:ℂ)/fourierRowPole s i^(j+2)))
    {w : ℂ} (hw : w ∉ range (fourierRowPole s)) :
    finiteFourierSlope m b w - Complex.exp (w-s)/(1+Complex.exp (w-s)) =
      ∑' i, w^(m+1)/(fourierRowPole s i^(m+1)*(fourierRowPole s i-w)) := by
  let P := fourierRowPole s
  have hp i : P i ≠ 0 := fun h => real_not_fourierRowPole s 0 ⟨i,by simpa only [Complex.ofReal_zero] using h⟩
  have hs (j : ℕ) : Summable (fun i => 1/‖P i‖^(j+2)) := rowPole_summable s j
  have hrem := anchoredPoleSum_taylor_remainder P hp hs (fourierRowPole_compl_open s)
    (fun i h => h ⟨i,rfl⟩) hw m
  rw [rowPole_anchored_of_real s hreal hw] at hrem
  have hpoly : finiteFourierSlope m b w =
      b 1 - ∑ j ∈ range m, w^(j+1)*(∑' i, (1:ℂ)/P i^(j+2)) := by
    unfold finiteFourierSlope
    rw [sum_range_succ']
    simp only [zero_add,Nat.cast_one,mul_one,pow_zero]
    have he : (∑ i ∈ range m, b (i+1+1)*((i+1+1:ℕ):ℂ)*w^(i+1)) =
        -∑ i ∈ range m, w^(i+1)*(∑' l, (1:ℂ)/P l^(i+2)) := by
      rw [←sum_neg_distrib]
      apply sum_congr rfl
      intro i hi
      rw [hb i (mem_range.mp hi)]
      ring
    rw [he]
    ring
  rw [hpoly,hb1]
  linear_combination hrem

/-- The complex derivative of the meromorphic row model on the full
pole-free domain, with the finite log coefficients supplied explicitly. -/
theorem finiteFourierQuotient_deriv (s : ℝ) (m : ℕ) (b : ℕ→ℂ)
    (hreal : ∀ x : ℝ, x < s → inverseSquarePoleSum (fourierRowPole s) (x:ℂ) =
      -Complex.exp ((x:ℂ)-s)/(1+Complex.exp ((x:ℂ)-s))^2)
    (hb1 : b 1 = Complex.exp (-(s:ℂ))/(1+Complex.exp (-(s:ℂ))))
    (hb : ∀ j < m, b (j+2)*((j+2:ℕ):ℂ) = -(∑' i, (1:ℂ)/fourierRowPole s i^(j+2)))
    {w : ℂ} (hw : w ∉ range (fourierRowPole s)) :
    HasDerivAt (fun z : ℂ => Complex.exp (finiteFourierLog m b z)/(1+Complex.exp (z-s)))
      ((Complex.exp (finiteFourierLog m b w)/(1+Complex.exp (w-s)))*
        (∑' i, w^(m+1)/(fourierRowPole s i^(m+1)*(fourierRowPole s i-w)))) w := by
  have he : HasDerivAt (fun z : ℂ => Complex.exp (z-s)) (Complex.exp (w-s)) w := by
    simpa using ((hasDerivAt_id w).sub_const (s:ℂ)).cexp
  have hn : 1+Complex.exp (w-s) ≠ 0 := fun h => hw ((logistic_denominator_zero_iff s w).mp h)
  apply ((finiteFourierLog_deriv m b w).cexp.div ((hasDerivAt_const w (1:ℂ)).add he) hn).congr_deriv
  dsimp only [Pi.add_apply]
  rw [←finiteFourierSlope_remainder s m b hreal hb1 hb hw]
  field_simp [hn]
  ring

#print axioms finiteFourierLog_deriv
#print axioms finiteFourierSlope_remainder
#print axioms finiteFourierQuotient_deriv
end OpenMathResearch.LongCycleExcedances
