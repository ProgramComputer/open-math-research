import FiniteAdjacentResidues
import PrincipalFactor

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset
open scoped PowerSeries

def zeroLeft (d : ℕ→ℂ) (n t : ℕ) : ℂ := if t ≤ n then d (n-t) else 0

/-- Difference across adjacent rows, including the uppermost occupied degree. -/
private theorem zeroLeft_next {d : ℕ→ℂ} (hd : d 0=0) (n t : ℕ) :
    zeroLeft d (n+1) t - zeroLeft d n t =
      if t ≤ n+1 then d (n+1-t)-d ((n+1-t)-1) else 0 := by
  by_cases h : t ≤ n
  · simp [zeroLeft,h,show t ≤ n+1 by omega,show n+1-t-1 = n-t by omega]
  · by_cases he : t = n+1
    · subst t; simp [zeroLeft,hd]
    · simp [zeroLeft,h,show ¬ (t ≤ n+1) by omega]

private theorem finite_shift_hasSum (d f : ℕ→ℂ) (n : ℕ) :
    HasSum (fun t => zeroLeft d n t * f t)
      (∑ t ∈ range (n+1), d (n-t)*f t) := by
  rw [show (∑ t ∈ range (n+1), d (n-t)*f t) =
      ∑ t ∈ range (n+1), zeroLeft d n t*f t by
    refine sum_congr rfl (fun t ht => ?_)
    rw [zeroLeft,if_pos (by have := mem_range.mp ht; omega)]]
  exact hasSum_sum_of_ne_finset_zero (fun t ht => by
    simp [zeroLeft,show ¬ (t ≤ n) by intro h; exact ht (mem_range.mpr (by omega))])

theorem principal_error_hasSum {Q : ℂ⟦X⟧} {w value : ℂ} (hq : CoeffHasSum Q w value)
    (d : ℕ→ℂ) (center : ℂ) (n : ℕ) :
    HasSum (fun t => (zeroLeft d n t-center)*(PowerSeries.coeff (R := ℂ) t Q*w^t))
      ((∑ t ∈ range (n+1), d (n-t)*(PowerSeries.coeff (R := ℂ) t Q*w^t))-center*value) := by
  have hh := (finite_shift_hasSum d (fun t => PowerSeries.coeff (R := ℂ) t Q*w^t) n).sub (hq.mul_left center)
  exact hh.congr_fun (fun t => by ring)

theorem principal_error_increment (d f : ℕ→ℂ) (hd : d 0=0) (center : ℂ) (n : ℕ) :
    ((∑ t ∈ range (n+2), d (n+1-t)*f t)-center) -
    ((∑ t ∈ range (n+1), d (n-t)*f t)-center) =
    ∑ t ∈ range (n+2), (d (n+1-t)-d ((n+1-t)-1))*f t := by
  have hh := (finite_shift_hasSum d f (n+1)).sub (finite_shift_hasSum d f n)
  have hu : HasSum (fun t => (zeroLeft d (n+1) t-zeroLeft d n t)*f t)
      (∑ t ∈ range (n+2), (d (n+1-t)-d ((n+1-t)-1))*f t) := by
    let g (t : ℕ) := (zeroLeft d (n+1) t-zeroLeft d n t)*f t
    change HasSum g _
    rw [show (∑ t ∈ range (n+2), (d (n+1-t)-d ((n+1-t)-1))*f t) =
        ∑ t ∈ range (n+2), g t by
      refine sum_congr rfl (fun t ht => ?_)
      dsimp only [g]
      rw [zeroLeft_next hd,if_pos (by have := mem_range.mp ht; omega)]]
    exact hasSum_sum_of_ne_finset_zero (fun t ht => by
      simp [g,zeroLeft_next hd,show ¬ (t ≤ n+1) by intro h; exact ht (mem_range.mpr (by omega))])
  have h := hh.unique (hu.congr_fun (fun t => by ring))
  linear_combination h

#print axioms principal_error_hasSum
#print axioms principal_error_increment
end OpenMathResearch.LongCycleExcedances
