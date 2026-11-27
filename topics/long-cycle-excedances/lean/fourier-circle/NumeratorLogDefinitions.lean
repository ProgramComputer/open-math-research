import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open scoped Real

def numeratorPole (s : ℝ) (l : ℤ) : ℂ :=
  (s : ℂ) + (2 * (l : ℂ) + 1) * π * Complex.I

def numeratorRadius (s : ℝ) : ℝ := Real.sqrt (s^2+π^2)

/-- Degree-normalized coefficients of the logistic logarithm, expressed by
its linear logistic value and the full odd-pole sum at every higher degree. -/
def numeratorLogSeries (s : ℝ) (j : ℕ) : ℂ :=
  if j = 0 then 0
  else if j = 1 then (numeratorRadius s/(1+Real.exp s):ℝ)
  else -(∑' l : ℤ, ((numeratorRadius s:ℂ)/numeratorPole s l)^j)/(j:ℂ)

end OpenMathResearch.LongCycleExcedances
