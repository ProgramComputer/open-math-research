import CatalanStrictPeaksFirstReturn
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-!
# The generating function of the actual Catalan strict-peak polynomial

The length variable lives in PowerSeries and the strict-peak variable lives
in the coefficient ring Polynomial ℝ.
-/

namespace CatalanStrictPeaks.FirstReturn

open Polynomial Finset
open scoped BigOperators

local notation "R" => ℝ[X]
local notation "Z" => (PowerSeries.X : PowerSeries R)

/-- The series of the original word enumerator. -/
noncomputable def G : PowerSeries R := PowerSeries.mk C

private noncomputable def ascentsGF : PowerSeries R := PowerSeries.mk A

private noncomputable def nonemptyGF : PowerSeries R :=
  PowerSeries.mk (fun n => if n = 0 then 0 else C n)

private theorem emptyRow : C 0 = 1 := (Recurrence.enumerate_X_eq_C 0).symm

private theorem ascentsGF_eq : ascentsGF = Z * G := by
  apply PowerSeries.ext
  intro k
  cases k with
  | zero => simp [ascentsGF, A_zero]
  | succ k => simp [ascentsGF, G, A_succ]

private theorem nonemptyGF_eq : nonemptyGF = G - 1 := by
  apply PowerSeries.ext
  intro k
  cases k with
  | zero => simp [nonemptyGF, G, emptyRow]
  | succ k => simp [nonemptyGF, G]

private theorem firstReturnGF :
    G = 1 + Z * (G * G + PowerSeries.C R (X - 1) * (ascentsGF * nonemptyGF)) := by
  apply PowerSeries.ext
  intro k
  cases k with
  | zero => simp [G, emptyRow]
  | succ k =>
    simp only [G, PowerSeries.coeff_mk, map_add, PowerSeries.coeff_one,
      Nat.succ_ne_zero, if_false, zero_add, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_C_mul]
    simp only [PowerSeries.coeff_mul, ascentsGF, nonemptyGF, PowerSeries.coeff_mk,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    rw [mul_sum, ← sum_add_distrib, C_succ_split]
    apply sum_congr rfl
    intro a ha
    by_cases h : a < k
    · simp [h, Nat.sub_ne_zero_of_lt h, mul_assoc]
    · have hsub : k - a = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_not_lt h)
      simp [h, hsub]

/-- The published quadratic series identity, proved from the actual word
enumerator and its first-return decomposition. -/
theorem generatingFunction_eq :
    G = 1 + PowerSeries.C R (1 - X) * Z ^ 2 * G +
      Z * (1 + PowerSeries.C R (X - 1) * Z) * G ^ 2 := by
  calc
    G = 1 + Z * (G * G + PowerSeries.C R (X - 1) * (ascentsGF * nonemptyGF)) :=
      firstReturnGF
    _ = _ := by
      rw [ascentsGF_eq, nonemptyGF_eq, map_sub, map_sub, map_one]
      ring

end CatalanStrictPeaks.FirstReturn
