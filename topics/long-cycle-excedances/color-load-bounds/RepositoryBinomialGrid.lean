import ColorLoadGrid
import BinomialPeakAdapter
import LongCycleBounds.BandBinomial
import Lean.Elab.Term

set_option autoImplicit false
noncomputable section
namespace RepositoryQuotientAudit
open Finset Real OpenMathResearch.LongCycleExcedances

-- The supplying declaration is private in a legacy module. Form its exact
-- kernel name without editing the frozen module or adding a declaration to it.
elab "frozen_band_binomial_atom" : term => do
  let decl := Lean.mkPrivateNameCore `LongCycleBounds.BandBinomial `LongCycleBounds.Band.binomial_any
  let _ ← Lean.getConstInfo decl
  pure (Lean.mkConst decl)

/-- Specialize the frozen atom to the mode, then integrate over the finite mesh. -/
theorem original_color_load_grid_mass {n d p : ℕ} (hp : 0 < p)
    (hd : 0 < d) (half : 2*d ≤ n) :
    (∑ j ∈ range (p+1), colorLoad n d ((j:ℝ)/(p:ℝ))) ≤
      (p:ℝ)/((n:ℝ)+1)+1/√(d:ℝ) := by
  let atom := frozen_band_binomial_atom
  apply color_load_grid_mass hp hd (by omega)
  simpa only [colorLoad, binomialDensity, mul_comm ((n.choose d:ℕ):ℝ), mul_assoc] using
    binomial_peak_from_uniform_atom hd half (fun {A B N} hA hB hN {u v} hu hv => @atom A B N hA hB hN u v hu hv)

#print axioms original_color_load_grid_mass
end RepositoryQuotientAudit
