import FirstPairModel

namespace RepositoryQuotientAudit
open LongCycles
open OpenMathResearch.LongCycleExcedances.InsertionTable

theorem firstPair_agreement :
    agrees 61 checkpoint251 (enumerator 251 13) ∧ agrees 61 checkpoint252 (enumerator 252 13) :=
  checkpoint_first_pair firstPairOriginal

end RepositoryQuotientAudit

#print axioms RepositoryQuotientAudit.firstPair_agreement
