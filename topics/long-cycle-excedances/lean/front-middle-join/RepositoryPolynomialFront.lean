import PolynomialFront
import LongCycleBounds.UniversalRecurrence

set_option autoImplicit false
noncomputable section

namespace RepositoryQuotientAudit
open LongCycles Polynomial OpenMathResearch.LongCycleExcedances

/-- The full lag summand of the unnormalized insertion recurrence. -/
def originalFrontLag (n k : ℕ) : ℝ[X] :=
  C (n.choose (k - 1) : ℝ) * (X * eulerian (k - 1)) * enumerator (n + 1 - k) k

/-- Ordered literal exterior witnesses supplied by real polynomial estimates. -/
theorem original_front_of_polynomial_bounds {n k H : ℕ} {cap : ℝ} (hk : 2 ≤ k)
    (a u : ℕ → ℝ) (ha : ∀ h < H, 0 < a h) (hu : ∀ h < H, 0 < u h)
    (hcap : ∀ h < H, u h ≤ cap)
    (hgap : ∀ h, h + 1 < H → 20 * u h < u (h + 1))
    (hb : ∀ h < H, FrontBounds (enumerator n k) (originalFrontLag n k) (h + 1) (a h) (u h)) :
    ∃ f : Fin H → ℝ, StrictMono f ∧
      ∀ i, 0 < f i ∧ f i ≤ (9 / 8 : ℝ) * cap ∧
        (enumerator n k).eval (-f i) = 0 ∧
        0 < (-1 : ℝ) ^ (i.val + 2) * (enumerator (n + 1) k).eval (-f i) :=
  polynomial_front_ordered a u ha hu hcap hgap hb
    (LongCycleBounds.Insertion.enumerator_succ hk :
      FrontInsertion (enumerator n k) (enumerator (n + 1) k) (originalFrontLag n k) (n : ℝ))

#print axioms original_front_of_polynomial_bounds
end RepositoryQuotientAudit
