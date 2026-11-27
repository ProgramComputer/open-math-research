import FourierRowAngularEquation
import FourierRealAxis
import FourierOriginalLog
import TiltAnalyticEvaluation

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Complex Set RepositoryQuotientAudit

/-- For every cutoff, the numerator of the original permutation generating
function satisfies the signed angular residue equation at every regular point.
The argument is evaluated at the same radius that occurs in the residues. -/
theorem original_row_angular_equation {k : ℕ} (hk : 2 ≤ k) {s : ℝ} (hs : 0 ≤ s)
    (R x : ℝ) (hw : circleMap 0 R x ∉ range (fourierRowPole s)) :
    let f := fun z : ℂ => seriesValue (coherentTilt k (-Real.exp (-s))) z /
      (1 + Complex.exp (z - s))
    let w := circleMap 0 R x
    HasDerivAt (fun y : ℝ => f (circleMap 0 R y))
      (I * Complex.exp ((k : ℂ) * I * (x : ℂ)) * (f w *
        ∑' i, ((R : ℂ)^k / fourierRowPole s i^(k-1)) / (fourierRowPole s i - w))) x := by
  let m := k - 2
  have hm : m + 2 = k := by dsimp [m]; omega
  have hd : m + 1 = k - 1 := by omega
  let b := fun j : ℕ => (cutoffLogCoefficient k (-Real.exp (-s)) j : ℂ)
  have hrep (z : ℂ) : seriesValue (coherentTilt k (-Real.exp (-s))) z =
      Complex.exp (finiteFourierLog m b z) := by
    rw [seriesValue_original_coherentTilt hk]
    unfold finiteFourierLog
    rw [hd]
  have hb (j : ℕ) (hj : j < m) : b (j+2) * ((j+2 : ℕ) : ℂ) =
      -(∑' i, (1 : ℂ) / fourierRowPole s i^(j+2)) := by
    rw [mul_comm]
    exact original_cutoff_log_poles (by omega) (by omega) hs
  have he := angular_finite_fourier_row s R m b (fourier_squared_poles_real_axis s)
    (original_cutoff_log_linear k s) hb x hw
  dsimp only
  simp only [hrep]
  simpa only [hm, hd] using he

#print axioms original_row_angular_equation
end OpenMathResearch.LongCycleExcedances
