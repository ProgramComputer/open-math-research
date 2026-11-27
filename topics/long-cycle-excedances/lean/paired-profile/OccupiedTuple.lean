import ActualOccupiedLimit
import Mathlib.Data.Finset.Sort

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset
open scoped PowerSeries

/-- A configuration is canonically a distinguished index and the strictly
increasing tuple of the other indices, with exactly the same term. -/
theorem occupiedCoeff_eq_sorted_tuple (P : ℤ → ℂ⟦X⟧) (B : ℤ → ℤ → ℂ⟦X⟧)
    (N : ℕ) (a : ℤ) (s : Finset ℤ) (ha : a ∉ s) :
    occupiedCoeff P B N (a,s) = PowerSeries.coeff (R := ℂ) N
      (P a * ∏ j : Fin s.card, B a (s.orderEmbOfFin rfl j)) := by
  simp only [occupiedCoeff, if_neg ha]
  congr 1
  congr 1
  rw [← prod_attach]
  exact (Fintype.prod_equiv (s.orderIsoOfFin rfl).toEquiv
    (fun j => B a (s.orderEmbOfFin rfl j)) (fun q : s => B a q)
    (fun j => congrArg (B a) (s.coe_orderIsoOfFin_apply rfl j).symm)).symm

#print axioms occupiedCoeff_eq_sorted_tuple
end OpenMathResearch.LongCycleExcedances
