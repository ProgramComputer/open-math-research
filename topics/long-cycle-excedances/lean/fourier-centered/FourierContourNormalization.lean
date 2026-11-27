import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset

/-- Normalize an exact Taylor-residue split on a selected circle. Multiplying
by the real scale puts a factor one half on the complete signed pole set. -/
theorem normalize_contour_split (n : ℕ) (r R U : ℝ) (P : Finset ℂ) (N D : ℂ → ℂ)
    (F y : ℂ) (hy : y=F/(R:ℂ)^n+∑ p ∈ P, D p*(N p/p^(n+1))) :
    let W := r/(2*U)*(r/R)^n
    let b := fun p : ℂ => (N p/(U:ℂ))*((r:ℂ)/p)^(n+1)
    ((r^(n+1)/(2*U):ℝ):ℂ)*y=(W:ℂ)*F+(∑ p ∈ P, D p*b p)/2 := by
  intro W b
  rw [hy,mul_add]
  congr 1
  · dsimp only [W]
    push_cast
    rw [div_pow,pow_succ]
    ring
  · conv_rhs => rw [div_eq_mul_inv,Finset.sum_mul]
    rw [mul_sum]
    apply sum_congr rfl
    intro p _
    dsimp only [b]
    push_cast
    rw [div_pow]
    ring

/-- The two normalizations of consecutive rows differ by exactly one
power of the principal radius. -/
theorem normalize_adjacent_real (n : ℕ) (r U C old next : ℝ) :
    r^(n+1)/(2*U)*(r*next-C*old)=
      r^(n+2)/(2*U)*next-C*(r^(n+1)/(2*U)*old) := by
  rw [show n+2=(n+1)+1 by omega,pow_succ r (n+1)]
  ring

#print axioms normalize_contour_split
#print axioms normalize_adjacent_real
end OpenMathResearch.LongCycleExcedances
