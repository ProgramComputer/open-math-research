import FinitePoleProduct
import Mathlib.Data.Complex.Basic

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset
open scoped PowerSeries

/-- The integer q indexes the signed odd pole 2q+1. -/
def pairedPoleDenom (C S : ℝ) (q : ℤ) : ℂ :=
  (C:ℂ) + Complex.I * (2*(q:ℂ)+1) * (S:ℂ)

theorem pairedPoleDenom_sub (C S : ℝ) (q a : ℤ) :
    pairedPoleDenom C S q - pairedPoleDenom C S a =
      Complex.I * (2*((q:ℂ)-(a:ℂ))) * (S:ℂ) := by
  unfold pairedPoleDenom
  ring

private theorem pairedPoleDenom_im (C S : ℝ) (q : ℤ) :
    (pairedPoleDenom C S q).im = (2*(q:ℝ)+1)*S := by
  simp [pairedPoleDenom, Complex.mul_im, Complex.mul_re, Complex.add_im, Complex.add_re]

theorem pairedPoleDenom_injective (C : ℝ) {S : ℝ} (hS : S ≠ 0) :
    Function.Injective (pairedPoleDenom C S) := by
  intro q a ha
  have h := congrArg Complex.im ha
  rw [pairedPoleDenom_im,pairedPoleDenom_im] at h
  have ht := mul_right_cancel₀ hS h
  have hr : (q:ℝ)=(a:ℝ) := by linarith
  exact_mod_cast hr

theorem pairedPoleDenom_ne_zero (C : ℝ) {S : ℝ} (hS : S ≠ 0) (q : ℤ) :
    pairedPoleDenom C S q ≠ 0 := by
  intro h
  have ht := congrArg Complex.im h
  rw [pairedPoleDenom_im, Complex.zero_im] at ht
  have hz := (mul_eq_zero.mp ht).resolve_right hS
  have hq : 2*q+1=0 := by exact_mod_cast hz
  omega

/-- The finite paired-residue identity for the exact signed odd pole family. -/
theorem finite_paired_cycle_series (s : Finset ℤ) (C : ℝ) {S : ℝ} (hS : S ≠ 0)
    (D : ℂ⟦X⟧) :
    (∏ q ∈ s, PowerSeries.rescale (pairedPoleDenom C S q)⁻¹ D) - 1 =
      ∑ a ∈ s, PowerSeries.rescale (pairedPoleDenom C S a)⁻¹ (D-1) *
        ∏ q ∈ s.erase a, (1+PowerSeries.C (R := ℂ) (pairedPoleDenom C S q/
          (Complex.I*(2*((q:ℂ)-(a:ℂ)))*(S:ℂ)))*
          PowerSeries.rescale (pairedPoleDenom C S q)⁻¹ ((D-1)*(1-PowerSeries.X))) := by
  simpa only [pairedPoleDenom_sub] using
    finite_cycle_series_poles s (pairedPoleDenom C S) (pairedPoleDenom_injective C hS).injOn
      (fun q _ => pairedPoleDenom_ne_zero C hS q) D

/-- Read off the exact positive-degree coefficient used for the old and
residual rows. Removing the empty product costs only degree zero. -/
theorem finite_paired_cycle_coeff (s : Finset ℤ) (C : ℝ) {S : ℝ} (hS : S ≠ 0)
    (D : ℂ⟦X⟧) {M : ℕ} (hM : 0 < M) :
    PowerSeries.coeff (R := ℂ) M (∏ q ∈ s, PowerSeries.rescale (pairedPoleDenom C S q)⁻¹ D) =
      ∑ a ∈ s, PowerSeries.coeff (R := ℂ) M (PowerSeries.rescale (pairedPoleDenom C S a)⁻¹ (D-1) *
        ∏ q ∈ s.erase a, (1+PowerSeries.C (R := ℂ) (pairedPoleDenom C S q/
          (Complex.I*(2*((q:ℂ)-(a:ℂ)))*(S:ℂ)))*
          PowerSeries.rescale (pairedPoleDenom C S q)⁻¹ ((D-1)*(1-PowerSeries.X)))) := by
  have h := congrArg (PowerSeries.coeff (R := ℂ) M) (finite_paired_cycle_series s C hS D)
  simpa only [map_sub, map_sum, PowerSeries.coeff_one, hM.ne', if_false, sub_zero] using h

#print axioms pairedPoleDenom_sub
#print axioms finite_paired_cycle_series
#print axioms finite_paired_cycle_coeff
end OpenMathResearch.LongCycleExcedances
