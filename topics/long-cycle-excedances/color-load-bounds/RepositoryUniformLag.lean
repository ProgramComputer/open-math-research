import UniformLagBudget
import RepositoryBinomialGrid
import RepositoryLoadLag
import RepositoryColorAlpha

set_option autoImplicit false
noncomputable section
namespace RepositoryQuotientAudit
open LongCycles OpenMathResearch.LongCycleExcedances

/-- The full literal insertion lag, in the same normalization as the old
coefficient, is strictly smaller than one eighth of the old coefficient. -/
theorem original_uniform_front_lag {n k p : ℕ}
    (hn : 10000 ≤ n) (hk : 8 ≤ k) (hsector : 4000*k < n)
    (hp : 0 < p) (hrank : 4*p^2 ≤ n) :
    (originalFrontLag n k).coeff p/(p:ℝ)^n <
      ((enumerator n k).coeff p/(p:ℝ)^n)/8 := by
  apply uniform_front_lag_budget hn hk hsector hp hrank
  · exact original_lag_le_color_grid hp (by omega : 2 ≤ k) (by omega : k ≤ n)
  · intro _
    exact original_color_load_grid_mass hp (by omega : 0 < k-1) (by omega : 2*(k-1) ≤ n)
  · exact original_front_alpha_lower hn (by omega : 2 ≤ k) hsector hp hrank

#print axioms original_uniform_front_lag
end RepositoryQuotientAudit
