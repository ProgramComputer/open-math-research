import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open PowerSeries
open scoped PowerSeries Polynomial

/-- The series of positive integer powers, with the zeroth power series
equal to the full geometric series. -/
def colorPowerSeries (d : ℕ) : ℝ⟦X⟧ := mk (fun j => (j:ℝ)^d)

theorem colorPowerSeries_succ (d : ℕ) :
    colorPowerSeries (d+1) = X * derivative ℝ (colorPowerSeries d) := by
  ext j
  cases j with
  | zero => simp [colorPowerSeries,coeff_zero_eq_constantCoeff]
  | succ j => simp [colorPowerSeries,coeff_succ_X_mul,coeff_derivative,pow_succ]

/-- The ordinary Eulerian recurrence implies the single-cycle Worpitzky
kernel as an identity of formal power series, in every positive degree. -/
theorem color_eulerian_kernel (A : ℕ → ℝ[X]) (hOne : A 1=1)
    (hrec : ∀ m, A (m+1)=(1+Polynomial.C (m:ℝ)*Polynomial.X)*A m+
      Polynomial.X*(1-Polynomial.X)*(A m).derivative) {m : ℕ} (hm : 1 ≤ m) :
    (1-X:ℝ⟦X⟧)^(m+1)*colorPowerSeries m=X*((A m : ℝ[X]):ℝ⟦X⟧) := by
  let z : ℝ⟦X⟧ := 1-X
  have dz : derivative ℝ z = -1 := by simp [z]
  induction m,hm using Nat.le_induction with
  | base =>
    have hgeo : z * colorPowerSeries 0 = 1 := by
      have h := (invOneSubPow ℝ 1).inv_val
      rw [invOneSubPow_inv_eq_one_sub_pow,pow_one,invOneSubPow_val_succ_eq_mk_add_choose] at h
      simpa [colorPowerSeries,z] using h
    have dh := congrArg (derivative ℝ) hgeo
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, dz, Derivation.map_one_eq_zero] at dh
    rw [hOne,Polynomial.coe_one,mul_one,colorPowerSeries_succ]
    change z^(1+1)*(X*derivative ℝ (colorPowerSeries 0))=X
    linear_combination X*hgeo + (X*z)*dh
  | succ m hm ih =>
    change z^(m+1)*colorPowerSeries m = X*((A m:ℝ[X]):ℝ⟦X⟧) at ih
    have dh := congrArg (derivative ℝ) ih
    rw [Derivation.leibniz,Derivation.leibniz,Derivation.leibniz_pow,dz,derivative_X,
      derivative_coe] at dh
    simp only [smul_eq_mul, nsmul_eq_mul, Nat.cast_add,Nat.cast_one,Nat.add_sub_cancel,
      mul_one,mul_neg,neg_mul] at dh
    rw [colorPowerSeries_succ,hrec]
    push_cast
    change z^(m+1+1)*(X*derivative ℝ (colorPowerSeries m)) =
      X*((1+(m:ℝ⟦X⟧)*X)*((A m:ℝ[X]):ℝ⟦X⟧) +
        X*(1-X)*(((A m).derivative:ℝ[X]):ℝ⟦X⟧))
    have hx : z+X=1 := by dsimp [z]; ring
    linear_combination (X*z)*dh + ((m:ℝ⟦X⟧)+1)*X*ih +
      X*((A m:ℝ[X]):ℝ⟦X⟧)*hx - X^2*(((A m).derivative:ℝ[X]):ℝ⟦X⟧)*hx

#print axioms colorPowerSeries_succ
#print axioms color_eulerian_kernel
end OpenMathResearch.LongCycleExcedances
