import AuditCatalanOrderBridge
import CatalanStrictPeaksAllInterlacing

namespace AuditReference

/-- The stronger published result on independently defined word polynomials and
    increasing signed root lists. -/
theorem catalanSourcePublished : CatalanPublished :=
  catalanPublished_of_successors CatalanStrictPeaks.strict_peaks_all_lengths.2

/-- The original conjecture as independently specified from its source. -/
theorem catalanSourceOriginal : CatalanOriginal :=
  catalanOriginal_of_published catalanSourcePublished

#print axioms catalanSourcePublished
#print axioms catalanSourceOriginal

end AuditReference
