import ColorLagGrid
import SparseLagBudget
import RepositoryColorCombinatorial
import RepositoryColorInsertion
import RepositoryPolynomialFront

noncomputable section
namespace RepositoryQuotientAudit
open Finset LongCycles PowerSeries OpenMathResearch.LongCycleExcedances

/-- An unconditional upper bound on a literal lag coefficient using only
a single unweighted binomial grid; the residual probability is eliminated. -/
theorem original_lag_le_color_grid {n k p : ℕ} (hp : 0 < p) (hk : 2 ≤ k) (hn : k ≤ n) :
    (originalFrontLag n k).coeff p/(p:ℝ)^n ≤
    ∑ j ∈ range (p+1), colorLoad n (k-1) ((j:ℝ)/p) := by
  have hm : 0 < n+1-k := by omega
  have hd : k-1 ≤ n := by omega
  have hsub : n-(k-1)=n+1-k := by omega
  have h := (original_color_successor_lag hk (n:=n) p).2
  rw [original_color_successor_exact hk (by omega : k ≤ n+1) p] at h
  apply color_lag_grid_upper hd hp (fun i => coeff (R := ℝ) i
      (colorTransform (n+1-k) (enumerator (n+1-k) k))) _ h
  intro i
  rw [hsub,←original_color_count_eq_transform hm hk]
  exact (ColorAnchor.realCount_bounds _ _ _).2

#print axioms original_lag_le_color_grid
end RepositoryQuotientAudit
