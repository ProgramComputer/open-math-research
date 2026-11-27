import ColorInsertion
import RepositoryColorTransform
import LongCycleBounds.UniversalRecurrence

set_option autoImplicit false
noncomputable section
namespace RepositoryQuotientAudit
open Finset LongCycles PowerSeries OpenMathResearch.LongCycleExcedances

/-- Adding one label shifts the literal transformed row by the exact
marked-cycle convolution. The boundary case with zero remaining labels is included. -/
theorem original_color_successor_exact {n k : ℕ} (hk : 2≤k) (hkn : k≤n+1) (p : ℕ) :
    coeff (R := ℝ) p (colorTransform (n+1) (enumerator (n+1) k)) -
      (p:ℝ)*coeff (R := ℝ) p (colorTransform n (enumerator n k)) =
    (n.choose (k-1):ℝ)*∑ j ∈ range (p+1), (j:ℝ)^(k-1)*
      coeff (R := ℝ) (p-j) (colorTransform (n+1-k) (enumerator (n+1-k) k)) := by
  apply color_successor_coefficient
  exact color_transform_successor eulerian LongCycleBounds.longEulerian_one
    LongCycleBounds.longEulerian_succ _ _ _ n k hk hkn _
    (LongCycleBounds.Insertion.enumerator_succ hk)

/-- The untransformed insertion lag is bounded by the coefficient gained by
adding one label, including in rows with a vanishing lag. -/
theorem original_color_successor_lag {n k : ℕ} (hk : 2≤k) (p : ℕ) :
    let L : Polynomial ℝ := Polynomial.C (n.choose (k-1):ℝ)*
      (Polynomial.X*eulerian (k-1))*enumerator (n+1-k) k
    0≤L.coeff p ∧ L.coeff p≤coeff (R := ℝ) p (colorTransform (n+1) (enumerator (n+1) k)) -
      (p:ℝ)*coeff (R := ℝ) p (colorTransform n (enumerator n k)) := by
  dsimp only
  apply color_lag_comparison _ _ _ n p (LongCycleBounds.Insertion.enumerator_succ hk)
  intro j
  exact color_lag_coefficients_nonneg LongCycles.descents _ (by positivity) _
    (fun i => (RunColors.original_coeff_envelope (n+1-k) k i hk).1) j

#print axioms original_color_successor_exact
#print axioms original_color_successor_lag
end RepositoryQuotientAudit
