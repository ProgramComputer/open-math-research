import FirstPairEulerian
import CheckpointData000

namespace RepositoryQuotientAudit
open Polynomial LongCycles LongCycleFinite
open OpenMathResearch.LongCycleExcedances.InsertionTable

theorem firstPairWeights : checkpointEulerian = descentCoeffs 12 :=
  descentCoeffsSnapshot12.symm

theorem firstPairWeightAgrees : agrees 61 checkpointEulerian (eulerian 12) := by
  rw [firstPairWeights]
  exact insertionEulerian_agrees 61 13

end RepositoryQuotientAudit

#print axioms RepositoryQuotientAudit.firstPairWeights
#print axioms RepositoryQuotientAudit.firstPairWeightAgrees
