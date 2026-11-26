import CatalanStrictPeaksFarVieta
import CatalanStrictPeaksTopThree

open Polynomial
open OpenMathResearch.OrientedNegativeInterlace

namespace CatalanStrictPeaks.FarEdge

private theorem odd_top (m : ℕ) (hm : 2 ≤ m) :
    ShiftedTop (CatalanStrictPeaks.C (2*m+1)) m 1 (oddFirst m) (oddSecond m) :=
  ⟨TopThree.coeff_odd_top m, TopThree.coeff_odd_next m (by omega), TopThree.coeff_odd_next_two m hm⟩

private theorem even_top (m : ℕ) (hm : 2 ≤ m) :
    ShiftedTop (CatalanStrictPeaks.C (2*m+2)) m (evenLead m) (evenFirst m) (evenSecond m) :=
  ⟨TopThree.coeff_even_top m, TopThree.coeff_even_next m (by omega), TopThree.coeff_even_next_two m hm⟩

/-- The exact next-row sign at the farthest zero of the original strict-peak
word polynomial. The two complete root lists can be supplied by the all-size
root theorem. The proof reads only the top three translated coefficients. -/
theorem farthest_root_sign (n : ℕ) (hn : 150 ≤ n) :
    ∀ (old : Fin (rowDegree n) → ℝ) (new : Fin (rowDegree (n+1)) → ℝ),
    CompleteNegativeRoots (CatalanStrictPeaks.C n) old →
    CompleteNegativeRoots (CatalanStrictPeaks.C (n+1)) new →
    ∀ i, i.val + 1 = rowDegree n →
      0 < (-1 : ℝ)^(i.val+1) * (CatalanStrictPeaks.C (n+1)).eval (-old i) := by
  obtain ⟨m, hm, heq⟩ : ∃ m : ℕ, 74 ≤ m ∧ (n = 2*m+1 ∨ n = 2*m+2) := by
    by_cases hnodd : n % 2 = 1
    · exact ⟨(n-1)/2, by omega, Or.inl (by omega)⟩
    · exact ⟨(n-2)/2, by omega, Or.inr (by omega)⟩
  rcases heq with rfl | rfl
  · rw [show 2*m+1+1=2*m+2 by omega,
        show rowDegree (2*m+1)=m by unfold rowDegree; omega,
        show rowDegree (2*m+2)=m by unfold rowDegree; omega]
    intro old new ho he i hi
    rw [hi]
    exact odd_to_even_sign hm ho he (odd_top m (by omega)) (even_top m (by omega)) i
      (fun j => Fin.le_def.mpr (by omega))
  · rw [show 2*m+2+1=2*(m+1)+1 by omega,
        show rowDegree (2*m+2)=m by unfold rowDegree; omega,
        show rowDegree (2*(m+1)+1)=m+1 by unfold rowDegree; omega]
    intro old new he ho i hi
    rw [hi]
    exact even_to_odd_sign hm he ho (even_top m (by omega)) (by simpa using odd_top (m+1) (by omega)) i
      (fun j => Fin.le_def.mpr (by omega))

end CatalanStrictPeaks.FarEdge
