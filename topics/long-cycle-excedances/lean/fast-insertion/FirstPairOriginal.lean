import FirstPairArithmetic
import FirstPairModel

namespace RepositoryQuotientAudit
open Polynomial LongCycles
open OpenMathResearch.LongCycleExcedances.InsertionTable
open WitnessLedger

def signedAt (n : ℕ) (s : ℤ) (d : WitnessLedger.Dyadic) : Prop :=
  0 < (s : ℝ) * ((enumerator n 13).divX).eval (-(d.value : ℝ))

private theorem signedAt_of_pass {n : ℕ} (hn : 0 < n) {row : List ℤ}
    (hrow : agrees 61 row (enumerator n 13)) (d : WitnessLedger.Dyadic) (s : ℤ)
    (hp : endpointPasses n row d s = true) : signedAt n s d := by
  have h := original_signed_of_integer_check n 13 60 hn (by decide) row hrow
    (d.num : ℤ) (2^d.bits) s hp
  simpa [signedAt, WitnessLedger.Dyadic.value] using h

/-- Both endpoint signs on each original row for all 26 first-pair gaps. -/
theorem firstPair_original_signs (g : Gap) (hg : g ∈ firstPairGaps) :
    signedAt 251 (oldLeftSign g.rank) g.a ∧ signedAt 251 (-(oldLeftSign g.rank)) g.b ∧
    signedAt 252 (-(oldLeftSign g.rank)) g.a ∧ signedAt 252 (-(oldLeftSign g.rank)) g.b := by
  have pass := List.all_eq_true.mp firstPairAllChecks g hg
  obtain ⟨a,b,c,d⟩ := of_decide_eq_true (show firstPairCheck g = true from pass)
  have old : agrees 61 checkpoint251 (enumerator 251 13) := firstPairOldAgrees
  have newRow : agrees 61 checkpoint252 (enumerator 252 13) := firstPairNewAgrees
  exact ⟨signedAt_of_pass (by decide) old _ _ a, signedAt_of_pass (by decide) old _ _ b,
    signedAt_of_pass (by decide) newRow _ _ c, signedAt_of_pass (by decide) newRow _ _ d⟩

end RepositoryQuotientAudit

#print axioms RepositoryQuotientAudit.firstPair_original_signs
