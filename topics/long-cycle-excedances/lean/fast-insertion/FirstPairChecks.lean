import OriginalInsertionSigns
import CheckpointReplay
import CheckedShard

namespace RepositoryQuotientAudit
open OpenMathResearch.LongCycleExcedances.InsertionTable
open WitnessLedger

/-- Entries for the first original pair in the checked archive shard. -/
def firstPairGaps : List Gap := checkedRows.filter fun g => g.n == 251 && g.k == 13

def oldLeftSign (rank : ℕ) : ℤ := if rank % 2 = 1 then 1 else -1

def endpointPasses (n : ℕ) (row : List ℤ) (d : WitnessLedger.Dyadic) (s : ℤ) : Bool :=
  integerEndpointCheck n 60 row d.num (2^d.bits) s

def firstPairCheck (g : Gap) : Bool :=
  let s := oldLeftSign g.rank
  decide (endpointPasses 251 checkpoint251 g.a s = true ∧
    endpointPasses 251 checkpoint251 g.b (-s) = true ∧
    endpointPasses 252 checkpoint252 g.a (-s) = true ∧
    endpointPasses 252 checkpoint252 g.b (-s) = true)

theorem firstPairRanks : firstPairGaps.map Gap.rank = (List.range 26).map (· + 6) := by decide

/-- Each arithmetic check reduces only one short contiguous block. -/
def firstPairGapBlock (start : ℕ) : List Gap := (firstPairGaps.drop start).take 6

end RepositoryQuotientAudit

#print axioms RepositoryQuotientAudit.firstPairRanks
