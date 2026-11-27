import OriginalInsertionSigns
import CheckpointReplay
import CheckedShard

namespace RepositoryQuotientAudit
open Polynomial LongCycles LongCycleFinite
open OpenMathResearch.LongCycleExcedances.InsertionTable
open WitnessLedger

/-- The model consists of the literal permutation sum and the Eulerian
polynomial in the previously checked insertion recurrence. -/
noncomputable def firstPairOriginal : CheckpointModel where
  A := eulerian 12
  E := fun n => enumerator n 13
  a_agrees := by
    have h : ∀ i : Fin 61, entry checkpointEulerian i = entry (descentCoeffs 12) i := by decide
    intro i hi
    rw [h ⟨i, hi⟩]
    exact insertionEulerian_agrees 61 13 i hi
  zero_row := enumerator_empty 13
  successor := fun _ => LongCycleBounds.Insertion.enumerator_succ (by decide)

/-- Entries for the first original pair in the checked archive shard. -/
def firstPairGaps : List Gap := checkedRows.filter fun g => g.n == 251 && g.k == 13

def oldLeftSign (rank : ℕ) : ℤ := if rank % 2 = 1 then 1 else -1

def endpointPasses (n : ℕ) (row : List ℤ) (d : Dyadic) (s : ℤ) : Bool :=
  integerEndpointCheck n 60 row d.num (2^d.bits) s

def firstPairCheck (g : Gap) : Bool :=
  let s := oldLeftSign g.rank
  decide (endpointPasses 251 checkpoint251 g.a s = true ∧
    endpointPasses 251 checkpoint251 g.b (-s) = true ∧
    endpointPasses 252 checkpoint252 g.a (-s) = true ∧
    endpointPasses 252 checkpoint252 g.b (-s) = true)

theorem firstPairRanks : firstPairGaps.map Gap.rank = (List.range 26).map (· + 6) := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem firstPairAllChecks : firstPairGaps.all firstPairCheck = true := by decide

def signedAt (n : ℕ) (s : ℤ) (d : Dyadic) : Prop :=
  0 < (s : ℝ) * ((enumerator n 13).divX).eval (-(d.value : ℝ))

private theorem signedAt_of_pass {n : ℕ} (hn : 0 < n) {row : List ℤ}
    (hrow : agrees 61 row (enumerator n 13)) (d : Dyadic) (s : ℤ)
    (hp : endpointPasses n row d s = true) : signedAt n s d := by
  have h := original_signed_of_integer_check n 13 60 hn (by decide) row hrow
    (d.num : ℤ) (2^d.bits) s hp
  simpa [signedAt, Dyadic.value] using h

/-- Both endpoint signs on each original row for all 26 first-pair gaps. -/
theorem firstPair_original_signs (g : Gap) (hg : g ∈ firstPairGaps) :
    signedAt 251 (oldLeftSign g.rank) g.a ∧ signedAt 251 (-(oldLeftSign g.rank)) g.b ∧
    signedAt 252 (-(oldLeftSign g.rank)) g.a ∧ signedAt 252 (-(oldLeftSign g.rank)) g.b := by
  have pass := List.all_eq_true.mp firstPairAllChecks g hg
  obtain ⟨a,b,c,d⟩ := of_decide_eq_true (show firstPairCheck g = true from pass)
  have old : agrees 61 checkpoint251 (enumerator 251 13) := agrees_checkpoint251 firstPairOriginal
  have newRow : agrees 61 checkpoint252 (enumerator 252 13) := agrees_checkpoint252 firstPairOriginal
  exact ⟨signedAt_of_pass (by decide) old _ _ a, signedAt_of_pass (by decide) old _ _ b,
    signedAt_of_pass (by decide) newRow _ _ c, signedAt_of_pass (by decide) newRow _ _ d⟩

end RepositoryQuotientAudit

#print axioms RepositoryQuotientAudit.firstPairRanks
#print axioms RepositoryQuotientAudit.firstPairAllChecks
#print axioms RepositoryQuotientAudit.firstPair_original_signs
