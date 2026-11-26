import CatalanStrictPeaksAllInterlacing

/-! Independently expanded specification using the published word polynomial.
The companion AuditCatalanWordBridge proves its equality with the separately defined enumerator. -/

namespace AuditExportType

open Polynomial

/-- The moduli specify exactly the degree-many roots, including multiplicity. -/
def CatalanRoots (p : Polynomial ℝ) {d : ℕ} (r : Fin d → ℝ) : Prop :=
  p.natDegree = d ∧ StrictMono r ∧ (∀ i, 0 < r i) ∧
    p.roots = (Finset.univ.image (fun i => -r i)).val

abbrev peakDegree (n : ℕ) : ℕ := (n - 1) / 2

/-- Every row and every successor pair, with the source's orientation expressed in moduli. -/
theorem catalan :
    (∀ n : ℕ, ∃ r : Fin (peakDegree n) → ℝ, CatalanRoots (CatalanStrictPeaks.C n) r) ∧
      ∀ n : ℕ, ∃ r : Fin (peakDegree n) → ℝ, ∃ s : Fin (peakDegree (n + 1)) → ℝ,
        CatalanRoots (CatalanStrictPeaks.C n) r ∧ CatalanRoots (CatalanStrictPeaks.C (n + 1)) s ∧
        (∀ i j, j.val = i.val → s j < r i) ∧
        (∀ i j, j.val = i.val + 1 → r i < s j) :=
  CatalanStrictPeaks.strict_peaks_all_lengths

#print axioms catalan

end AuditExportType
