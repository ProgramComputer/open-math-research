import ActualOccupiedLimit
import EntireCycleEvaluation

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset
open scoped PowerSeries

private theorem coeff_product_by_right (F Q : ℂ⟦X⟧) (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n (F*Q) =
      ∑ t ∈ range (n+1), (PowerSeries.coeff (R := ℂ) t Q * PowerSeries.coeff (R := ℂ) (n-t) F) := by
  rw [mul_comm,PowerSeries.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

private theorem padded_old (d : ℕ → ℂ) (hd : d 0=0) (z : ℂ) (hz : z≠0)
    (Q : ℕ → ℂ) (n : ℕ) :
    (∑ t ∈ range (n+1), Q t*(z^(n-t)*d (n-t))) =
    ∑ t ∈ range (n+2), Q t*(z^(n+1-t)*(z⁻¹*d ((n+1-t)-1))) := by
  conv_rhs => rw [sum_range_succ]
  simp only [Nat.sub_self,Nat.zero_sub,hd,mul_zero,add_zero]
  apply sum_congr rfl
  intro t ht
  have htn : t ≤ n := by have := mem_range.mp ht; omega
  rw [show n+1-t = (n-t)+1 by omega, Nat.add_sub_cancel,pow_succ]
  field_simp <;> ring

/-- Adjacent coefficients of a rescaled distinguished factor times an arbitrary
occupied product. Degree n+1 is included on both sides of the common sum. -/
theorem finite_pole_adjacent (D Q : ℂ⟦X⟧) (hzero : PowerSeries.coeff (R := ℂ) 0 D = 0)
    {w : ℂ} (hw : w≠0) (n : ℕ) (x y : ℂ) :
    x*PowerSeries.coeff (R := ℂ) n (PowerSeries.rescale w⁻¹ D*Q) -
    y*PowerSeries.coeff (R := ℂ) (n+1) (PowerSeries.rescale w⁻¹ D*Q) =
    ∑ t ∈ range (n+2), let s := n+1-t
      let d := PowerSeries.coeff (R := ℂ) (s-1) D
      let b := PowerSeries.coeff (R := ℂ) s D - d
      PowerSeries.coeff (R := ℂ) t Q * w⁻¹^s * (d*(w*x-y)-b*y) := by
  rw [coeff_product_by_right,coeff_product_by_right]
  simp only [PowerSeries.coeff_rescale]
  rw [padded_old (fun s => PowerSeries.coeff (R := ℂ) s D) hzero w⁻¹ (inv_ne_zero hw)]
  rw [mul_sum,mul_sum,←sum_sub_distrib]
  apply sum_congr rfl
  intro t _
  simp only [inv_inv]
  ring

theorem finite_adjacent_occupied_rows (A : Finset ℤ) {k n : ℕ} (hk : 0 < k) (hn : 0 < n)
    (C : ℝ) {S : ℝ} (hS : S ≠ 0) (x y : ℂ) :
    let old := ∏ q ∈ A, PowerSeries.rescale (pairedPoleDenom C S q)⁻¹ (cutoffCycleSeries k)
    x*PowerSeries.coeff (R := ℂ) n old - y*PowerSeries.coeff (R := ℂ) (n+1) old =
    ∑ a ∈ A, ∑ t ∈ range (n+2),
      let w := pairedPoleDenom C S a
      let s := n+1-t
      let D := cutoffCycleSeries k-1
      let d := PowerSeries.coeff (R := ℂ) (s-1) D
      let b := PowerSeries.coeff (R := ℂ) s D - d
      PowerSeries.coeff (R := ℂ) t (∏ q ∈ A.erase a, (1+occupiedPrimitive k C S a q)) *
        w⁻¹^s * (d*(w*x-y)-b*y) := by
  dsimp only
  rw [finite_actual_occupiedCoeff A hn C hS,finite_actual_occupiedCoeff A (by omega) C hS,
    mul_sum,mul_sum,←sum_sub_distrib]
  apply sum_congr rfl
  intro a _
  apply finite_pole_adjacent _ _ _ (pairedPoleDenom_ne_zero C hS a)
  rw [map_sub,cutoffCycleSeries,coeff_cutoffExp hk (vanishesBelow_cutoffLog k)]
  simp

#print axioms finite_pole_adjacent
#print axioms finite_adjacent_occupied_rows
end OpenMathResearch.LongCycleExcedances
