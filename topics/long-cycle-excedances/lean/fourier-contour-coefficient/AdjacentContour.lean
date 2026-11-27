import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset

/-- A common selected contour and common enclosed poles give the exact same-radius
contrast. No division by the original row value or a root hypothesis is involved. -/
theorem adjacent_contour_split (P : Finset ℂ) (N : ℂ → ℂ) (n : ℕ)
    {R r C u v a b : ℂ} (hR : R ≠ 0) (hp : ∀ p ∈ P, p ≠ 0)
    (hu : u = a/R^n + ∑ p ∈ P, N p/p^(n+1))
    (hv : v = b/R^(n+1) + ∑ p ∈ P, N p/p^(n+1+1)) :
    r*v-C*u = ((r/R)*b-C*a)/R^n +
      ∑ p ∈ P, (r/p-C)*(N p/p^(n+1)) := by
  rw [hu,hv,mul_add,mul_add,add_sub_add_comm]
  have hc : r*(b/R^(n+1))-C*(a/R^n) = ((r/R)*b-C*a)/R^n := by
    rw [pow_succ]
    field_simp [hR]
    <;> ring
  rw [hc, Finset.mul_sum,Finset.mul_sum,←Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro p hmem
  rw [pow_succ p (n+1)]
  field_simp [hp p hmem]
  <;> ring

#print axioms adjacent_contour_split
end OpenMathResearch.LongCycleExcedances
