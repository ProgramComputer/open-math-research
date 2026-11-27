import PairedPoleConvergence
import Mathlib.Analysis.Real.Pi.Bounds

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open scoped PowerSeries

/-- The scaled signed pole power sum equals R^p times the original
Mittag–Leffler sum at logarithmic parameter x. -/
theorem paired_scaled_odd_sum (x : ℝ) {R : ℝ} (hR : 0 < R) (p : ℕ) :
    (∑' q : ℤ, ((pairedPoleDenom (x/R) (Real.pi/R) q)⁻¹)^p) =
      (R:ℂ)^p * ∑' q : ℤ, 1 / ((x:ℂ)+(2*(q:ℂ)+1)*Real.pi*Complex.I)^p := by
  rw [←tsum_mul_left]
  apply tsum_congr
  intro q
  let w := (x:ℂ)+(2*(q:ℂ)+1)*Real.pi*Complex.I
  have hden : pairedPoleDenom (x/R) (Real.pi/R) q = w/(R:ℂ) := by
    unfold pairedPoleDenom
    push_cast
    dsimp [w]
    ring
  rw [hden, inv_div, div_pow, mul_one_div]

/-- Transport the checked signed Eulerian pole identity to the logarithmic
cycle coefficient. The factor 1/p accounts for the factorial change. -/
theorem paired_single_cycle_normalization (x : ℝ) {R : ℝ} (hR : 0 < R) {p : ℕ} (hp : 0 < p)
    {E : ℂ} (hEuler : E = ((p-1).factorial:ℂ) *
      ∑' q : ℤ, 1 / ((x:ℂ)+(2*(q:ℂ)+1)*Real.pi*Complex.I)^p) :
    (R:ℂ)^p*E/(p.factorial:ℂ) =
      (∑' q : ℤ, ((pairedPoleDenom (x/R) (Real.pi/R) q)⁻¹)^p)/(p:ℂ) := by
  rw [hEuler, paired_scaled_odd_sum x hR]
  have hfac : (p.factorial:ℂ) = (p:ℂ)*((p-1).factorial:ℂ) := by
    exact_mod_cast (Nat.mul_factorial_pred hp.ne').symm
  have hpC : (p:ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hmC : ((p-1).factorial:ℂ) ≠ 0 := by exact_mod_cast (p-1).factorial_ne_zero
  rw [hfac]
  generalize (∑' q : ℤ, 1 / ((x:ℂ)+(2*(q:ℂ)+1)*Real.pi*Complex.I)^p) = T
  field_simp [hpC,hmC] <;> ring

#print axioms paired_scaled_odd_sum
#print axioms paired_single_cycle_normalization
end OpenMathResearch.LongCycleExcedances
