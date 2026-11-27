import FirstPairRecurrence
import CheckpointReplay

namespace RepositoryQuotientAudit
open LongCycles Polynomial
open OpenMathResearch.LongCycleExcedances.InsertionTable

/-- The literal permutation sum and the supplying Eulerian polynomial
instantiate the checked consecutive insertion tables. -/
noncomputable def firstPairOriginal : CheckpointModel :=
  CheckpointModel.mk (eulerian 12) (fun n => enumerator n 13)
    firstPairWeightAgrees (enumerator_empty 13) firstPairSuccessor

end RepositoryQuotientAudit

#print axioms RepositoryQuotientAudit.firstPairOriginal
