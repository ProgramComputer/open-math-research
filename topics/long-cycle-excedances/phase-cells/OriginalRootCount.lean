import CellRootSelection
import OriginalAngularDerivative

noncomputable section
namespace RepositoryQuotientAudit
open Real Set LongCycles OpenMathResearch.LongCycleExcedances

/-- These are distinct literal roots of the source enumerator in (-1,0).
The successor alternates on the selected roots in their true real order. -/
theorem original_ordered_high_angle_roots {n k : ℕ} (hn : 0 < n)
    (hk : 7 ≤ k) (hsize : 100*(k:ℝ)*log k ≤ n) :
    ∃ z : Fin (n/2 - (n+5)/6) → ℝ, StrictAnti z ∧
      ∀ i, z i ∈ Ioo (-1:ℝ) 0 ∧ (enumerator n k).eval (z i) = 0 ∧
        0 < (-1:ℝ)^((n+5)/6 + i.val + 1) * (enumerator (n+1) k).eval (z i) := by
  apply ordered_grid_roots (fun t => (enumerator n k).eval t)
    (fun t => (enumerator (n+1) k).eval t) n hn
  intro j ha hb
  obtain ⟨⟨θ, hθ, hz⟩, hs⟩ := original_high_angle_cells hn hk hsize ha hb
  exact ⟨θ,hθ,hz,hs θ ⟨hθ.1.le,hθ.2.le⟩ hz⟩

#print axioms original_ordered_high_angle_roots
end RepositoryQuotientAudit
