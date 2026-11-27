import PairedSineComparison

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real Finset

/-- Coefficient of degree j+2 after multiplying the row series by
1-2cos(z)u+u². -/
def pairedDeflatedCoefficient (F : ℕ → ℝ) (z : ℝ) (j : ℕ) : ℝ :=
  F (j+2) - 2*cos z*F (j+1) + F j

theorem paired_sine_step (F : ℕ → ℝ) (z : ℝ) (j : ℕ) :
    pairedSineDifference (j+1) z (F (j+1)) (F (j+2)) -
      pairedSineDifference j z (F j) (F (j+1)) =
    -sin (((j:ℝ)+1)*z)*pairedDeflatedCoefficient F z j := by
  let x := ((j:ℝ)+1)*z
  have hrec : sin (x+z)+sin (x-z)=2*cos z*sin x := by rw [sin_add,sin_sub]; ring
  have hb : x-z=(j:ℝ)*z := by dsimp only [x]; ring
  have hf : (((j:ℝ)+1)+1)*z=x+z := by dsimp only [x]; ring
  rw [hb] at hrec
  simp only [pairedSineDifference,Nat.cast_add,Nat.cast_one,hf,pairedDeflatedCoefficient]
  change _ = -sin x * _
  linear_combination (F (j+1))*hrec

/-- A finite weighted Taylor sum exactly equals the adjacent-row comparison. -/
theorem paired_sine_partial_sum (F : ℕ → ℝ) (z : ℝ) (n : ℕ) :
    pairedSineDifference n z (F n) (F (n+1)) =
      sin z*F 0 - ∑ j ∈ range n, sin (((j:ℝ)+1)*z)*pairedDeflatedCoefficient F z j := by
  induction n with
  | zero => simp [pairedSineDifference]
  | succ n ih =>
    rw [sum_range_succ,←sub_sub]
    linarith only [paired_sine_step F z n,ih]

#print axioms paired_sine_step
#print axioms paired_sine_partial_sum
end OpenMathResearch.LongCycleExcedances
