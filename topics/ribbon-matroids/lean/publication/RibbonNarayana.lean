import RibbonNarayanaCoefficients
import NarayanaRolle

open OpenMathResearch.MatroidKL

namespace Ribbon.Source

/-- The actual finite-matroid Z-polynomial has the Narayana coefficients.
Its complex roots are all real, strictly negative and simple. -/
theorem IsRibbonPresentation.narayana {n r : ℕ} {M : Matroid (Fin n)}
    {lower upper : Path n} (h : IsRibbonPresentation M r lower upper) :
    (∀ i : ℕ, ((r + 1 : ℕ) : ℤ) * (matroidZ M).coeff i =
      ((r + 1).choose i : ℤ) * ((r + 1).choose (i + 1) : ℤ)) ∧
    ((matroidZ M).map (Int.castRingHom ℂ)).roots.card = r ∧
    (∀ z : ℂ, (matroidZ M).eval₂ (Int.castRingHom ℂ) z = 0 →
      z.im = 0 ∧ z.re < 0 ∧ ((matroidZ M).map (Int.castRingHom ℂ)).rootMultiplicity z = 1) :=
  ⟨h.narayana_coeff, narayana_roots h.narayana_coeff⟩

end Ribbon.Source
