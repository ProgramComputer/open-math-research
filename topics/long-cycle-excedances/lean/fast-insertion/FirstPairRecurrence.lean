import FirstPairWeights

namespace RepositoryQuotientAudit
open LongCycles Polynomial

theorem firstPairSuccessor (n : ℕ) :
    enumerator (n+1) 13 =
      C (n : ℝ) * X * enumerator n 13 +
      X * (1-X) * derivative (enumerator n 13) +
      C (n.choose 12 : ℝ) * (X * eulerian 12) * enumerator (n+1-13) 13 :=
  LongCycleBounds.Insertion.enumerator_succ (n := n) (k := 13) (by decide : 2 ≤ (13 : ℕ))

end RepositoryQuotientAudit

#print axioms RepositoryQuotientAudit.firstPairSuccessor
