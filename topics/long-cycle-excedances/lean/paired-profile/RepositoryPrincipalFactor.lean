import EntireCycleEvaluation
import RepositoryNumeratorVariation
import ActualOccupiedValue
import PrincipalFactor

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset
open scoped PowerSeries

theorem original_numerator_hasSum (m : ℕ) (v : ℂ) :
    HasSum (fun s => (CycleProbability.originalNumeratorCoeff (m+2) s : ℂ)*v^s)
      (Complex.exp (-(∑ i ∈ range (m+1), v^(i+1)/((i:ℂ)+1))) - (1-v)) := by
  have h := cutoff_numerator_hasSum (m+1) v
  unfold CoeffHasSum at h
  exact h.congr_fun (fun s => by rw [cutoffCycleNumerator,
    CycleProbability.coeff_cutoffCycleNumerator_eq_original (by omega : 2 ≤ m+2)])

private theorem hasSum_one_add {F : ℂ⟦X⟧} {v s : ℂ} (h : CoeffHasSum F v s) :
    CoeffHasSum (1+F) v (1+s) := by
  have hsum := (show HasSum _ _ from CoeffHasSum.one v).add h
  exact hsum.congr_fun (fun n => by rw [map_add,add_mul])

/-- Evaluate the actual occupied primitive at its distinguished denominator. -/
theorem occupied_primitive_hasSum (j : ℕ) (C S : ℝ) (a q : ℤ) :
    let A := pairedPoleDenom C S a
    let B := pairedPoleDenom C S q
    let v := A/B
    CoeffHasSum (occupiedPrimitive (j+2) C S a q) A
      (B/(B-A)*(Complex.exp (-(∑ i ∈ range (j+1), v^(i+1)/((i:ℂ)+1))) - (1-v))) := by
  dsimp only
  let A := pairedPoleDenom C S a
  let B := pairedPoleDenom C S q
  have h := cutoff_numerator_hasSum (j+1) (A/B)
  unfold CoeffHasSum at h
  apply (h.mul_left (B/(B-A))).congr_fun
  intro n
  rw [occupiedPrimitive,PowerSeries.coeff_C_mul,PowerSeries.coeff_rescale]
  dsimp only [cutoffCycleNumerator]
  change (B/(B-A)*(B⁻¹^n*_) * A^n) = _
  rw [div_eq_mul_inv A B,mul_pow]
  ring

theorem occupied_factor_hasSum_integral (j : ℕ) (C : ℝ) {S : ℝ} (hS : S ≠ 0)
    {a q : ℤ} (haq : a ≠ q)
    (hv : ‖pairedPoleDenom C S a / pairedPoleDenom C S q‖ ≤ 1) :
    CoeffHasSum (1+occupiedPrimitive (j+2) C S a q) (pairedPoleDenom C S a)
      (Complex.exp (principalLogIntegral j (pairedPoleDenom C S a / pairedPoleDenom C S q))) := by
  have h := hasSum_one_add (occupied_primitive_hasSum j C S a q)
  have hne := pairedPoleDenom_injective C hS |>.ne haq
  rw [← principal_lagrange_factor_eq_exp j (pairedPoleDenom_ne_zero C hS q) hne hv]
  exact h

theorem occupied_product_hasSum_integral (j : ℕ) (C : ℝ) {S : ℝ} (hS : S ≠ 0)
    (a : ℤ) (T : Finset ℤ) (ha : a ∉ T)
    (hv : ∀ q ∈ T, ‖pairedPoleDenom C S a / pairedPoleDenom C S q‖ ≤ 1) :
    CoeffHasSum (∏ q ∈ T, (1+occupiedPrimitive (j+2) C S a q)) (pairedPoleDenom C S a)
      (Complex.exp (∑ q ∈ T, principalLogIntegral j
        (pairedPoleDenom C S a / pairedPoleDenom C S q))) := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using CoeffHasSum.one (pairedPoleDenom C S a)
  | @insert q T hq ih =>
    have hne : a ≠ q := by intro e; exact ha (e ▸ mem_insert_self ..)
    have haT : a ∉ T := fun h => ha (mem_insert_of_mem h)
    rw [prod_insert hq,sum_insert hq,Complex.exp_add]
    exact CoeffHasSum.mul_series
      (occupied_factor_hasSum_integral j C hS hne (hv q (mem_insert_self ..)))
      (ih haT (fun r hr => hv r (mem_insert_of_mem hr)))

#print axioms original_numerator_hasSum
#print axioms occupied_primitive_hasSum
#print axioms occupied_factor_hasSum_integral
#print axioms occupied_product_hasSum_integral
end OpenMathResearch.LongCycleExcedances
