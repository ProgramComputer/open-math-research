import FirstPairChecks0
import FirstPairChecks6
import FirstPairChecks12
import FirstPairChecks18
import FirstPairChecks24

namespace RepositoryQuotientAudit

theorem firstPairAllChecks : firstPairGaps.all firstPairCheck = true := by
  have cover : firstPairGaps = firstPairGapBlock 0 ++ firstPairGapBlock 6 ++ firstPairGapBlock 12 ++ firstPairGapBlock 18 ++ firstPairGapBlock 24 := by decide
  rw [cover]
  simp only [List.all_append, firstPairBlock0, firstPairBlock6, firstPairBlock12, firstPairBlock18, firstPairBlock24]
  rfl

end RepositoryQuotientAudit

#print axioms RepositoryQuotientAudit.firstPairAllChecks
