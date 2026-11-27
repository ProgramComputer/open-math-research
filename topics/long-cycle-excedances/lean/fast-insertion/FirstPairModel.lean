import FirstPairEulerian
import CheckpointReplay

namespace RepositoryQuotientAudit
open Polynomial LongCycles LongCycleFinite
open OpenMathResearch.LongCycleExcedances.InsertionTable

private theorem firstPairWeightAgrees : agrees 61 checkpointEulerian (eulerian 12) := by
  have weights : ∀ i : Fin 61, entry checkpointEulerian i = entry (descentCoeffs 12) i := by
    rw [descentCoeffsSnapshot12]
    decide
  intro i hi
  rw [show entry checkpointEulerian i = entry (descentCoeffs 12) i from weights ⟨i, hi⟩]
  exact insertionEulerian_agrees 61 13 i hi

/-- The literal permutation sum and the supplying Eulerian polynomial
instantiate the checked consecutive insertion tables. -/
noncomputable def firstPairOriginal : CheckpointModel where
  A := eulerian 12
  E := fun n => enumerator n 13
  a_agrees := firstPairWeightAgrees
  zero_row := enumerator_empty 13
  successor := fun _ => LongCycleBounds.Insertion.enumerator_succ (by decide)

theorem firstPairOldAgrees : agrees 61 checkpoint251 (enumerator 251 13) :=
  agrees_checkpoint251 firstPairOriginal

theorem firstPairNewAgrees : agrees 61 checkpoint252 (enumerator 252 13) :=
  agrees_checkpoint252 firstPairOriginal

end RepositoryQuotientAudit

#print axioms RepositoryQuotientAudit.firstPairOldAgrees
#print axioms RepositoryQuotientAudit.firstPairNewAgrees
