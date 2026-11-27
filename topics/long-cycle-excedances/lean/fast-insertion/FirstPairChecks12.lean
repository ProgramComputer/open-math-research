import FirstPairChecks

namespace RepositoryQuotientAudit

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem firstPairBlock12 : (firstPairGapBlock 12).all firstPairCheck = true := by decide

end RepositoryQuotientAudit

#print axioms RepositoryQuotientAudit.firstPairBlock12
