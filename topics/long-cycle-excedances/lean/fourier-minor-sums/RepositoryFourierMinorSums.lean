import LiteralMinorSums
import RepositoryWideResidues

set_option autoImplicit false
noncomputable section
namespace RepositoryQuotientAudit
open OpenMathResearch.LongCycleExcedances Real Finset

/-- The normalized old row and its signed successor contrast on the enclosed
positive nonprincipal poles of the original permutation generating function.
The endpoint at height zero is included. -/
theorem original_fourier_minor_sums {n k : ℕ} (hk : 100 ≤ k) {s R : ℝ} (hs : 0 ≤ s)
    (hR : 0 ≤ R) (I : Finset ℕ) :
    let p := coherentPole s 0
    let r := ‖p‖
    let w := fun i : ℕ => coherentPole s ((i+1:ℕ):ℤ)
    let T := seriesValue (coherentTilt k (-Real.exp (-s)))
    let u := fun i => (T (w i)/(‖T p‖:ℂ))*((r:ℂ)/w i)^(n+1)
    R^2 ≤ r^2*(1+2/(k:ℝ)) → 1 ≤ (n:ℝ)*(π/r)^2 → (∀ i ∈ I, ‖w i‖ ≤ R) →
    ‖∑ i ∈ I, u i‖ ≤ 1/12 ∧ ‖∑ i ∈ I, ((r:ℂ)/w i-(s/r:ℝ))*u i‖ ≤ (π/r)/4 := by
  intro p r w T u hcap hm henc
  exact literal_minor_sums_of_positive_budgets hk hs T I hcap henc (fun h =>
    original_fourier_enclosed_budgets hk h hR hcap hm I henc)

#print axioms original_fourier_minor_sums
end RepositoryQuotientAudit
