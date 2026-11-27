import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real

def pairedAngleLog (z : ℝ) : ℝ := π * cos z / sin z
def pairedAngleRadius (z : ℝ) : ℝ := π / sin z
def pairedAngularRow (n : ℕ) (C : ℝ → ℝ) (z : ℝ) : ℝ :=
  (pairedAngleRadius z)^n / (n.factorial:ℝ) * C (pairedAngleLog z)

theorem paired_log_derivative {z : ℝ} (hz : sin z ≠ 0) :
    HasDerivAt pairedAngleLog (-(π/(sin z)^2)) z := by
  have h := ((hasDerivAt_cos z).const_mul π).div (hasDerivAt_sin z) hz
  have hv : ((π * -sin z) * sin z - (π*cos z) * cos z)/(sin z)^2 =
      -(π/(sin z)^2) := by
    rw [←neg_div]
    congr 1
    linear_combination -π*(sin_sq_add_cos_sq z)
  rw [hv] at h
  exact h

#print axioms paired_log_derivative
end OpenMathResearch.LongCycleExcedances
