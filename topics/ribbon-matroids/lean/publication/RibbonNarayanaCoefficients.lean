import RibbonChainBoundary
import CircuitNarayanaMatroid

open OpenMathResearch.MatroidKL

namespace Ribbon.Source

/-- The Narayana coefficient equality in the original ribbon conjecture. -/
theorem IsRibbonPresentation.narayana_coeff {n r : ℕ} {M : Matroid (Fin n)}
    {lower upper : Path n} (h : IsRibbonPresentation M r lower upper) (i : ℕ) :
    ((r + 1 : ℕ) : ℤ) * (matroidZ M).coeff i =
    ((r + 1).choose i : ℤ) * ((r + 1).choose (i + 1) : ℤ) := by
  obtain ⟨N, hGround, hBases, hZ⟩ := h.exists_circuitBoundary
  rw [hZ]
  exact (CircuitBases.mk hGround hBases).narayana_coeff i

end Ribbon.Source
