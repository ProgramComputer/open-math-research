import FirstPairWeights
import CheckpointReplay

namespace RepositoryQuotientAudit
open LongCycles
open OpenMathResearch.LongCycleExcedances.InsertionTable

/-- The literal permutation sum and the supplying Eulerian polynomial
instantiate the checked consecutive insertion tables. -/
noncomputable def firstPairOriginal : CheckpointModel where
  A := eulerian 12
  E := fun n => enumerator n 13
  a_agrees := firstPairWeightAgrees
  zero_row := enumerator_empty 13
  successor := fun _ => LongCycleBounds.Insertion.enumerator_succ (by decide)

end RepositoryQuotientAudit

#print axioms RepositoryQuotientAudit.firstPairOriginal
