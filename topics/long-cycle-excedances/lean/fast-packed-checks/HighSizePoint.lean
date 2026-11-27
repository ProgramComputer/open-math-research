import RepositoryFastPackedPoint

namespace OpenMathResearch.LongCycleExcedances.FastPointSamples
open IntegerSign TruncatedRows
open RepositoryQuotientAudit Polynomial LongCycles

structure Pair where
  cutoff : ℕ
  n : ℕ
  old : List ℕ
  next : List ℕ

structure Probe where
  upper : Bool
  num : ℤ
  bits : ℕ
  level : ℕ
  sign : ℤ

def row (f : Pair) (upper : Bool) : List ℕ := if upper then f.next else f.old

def size (f : Pair) (upper : Bool) : ℕ := if upper then f.n + 1 else f.n

def check (f : Pair) (p : Probe) : Bool :=
  fastCoarseCheck (size f p.upper) p.level p.bits (row f p.upper) p.num p.sign

def signedAt (f : Pair) (p : Probe) : Prop :=
  0 < (p.sign:ℝ) * ((enumerator (size f p.upper) f.cutoff).divX).eval
    (-(((p.num:ℚ)/(2^p.bits:ℕ) : ℚ):ℝ))

/-- The endpoint certificate deliberately takes the two rounded row identifications
as premises. A recurrence certificate can supply them separately. -/
def ActualRows (f : Pair) (hk : 2 ≤ f.cutoff) : Prop :=
  ∀ upper i, i < (row f upper).length →
    decode 48 ((row f upper)[i]?.getD 0) =
      lowerRows 48 f.cutoff (by omega) (compactCycleWeight f.cutoff) (size f upper) i

theorem signedAt_of_check (f : Pair) (hk : 2 ≤ f.cutoff) (hn : f.n+1 ≤ 1001)
    (rows : ActualRows f hk) (p : Probe) (ok : check f p = true) : signedAt f p := by
  have hsize : size f p.upper ≤ 1001 := by unfold size; split <;> omega
  exact original_signed_of_fast_packed_words f.cutoff (size f p.upper) p.level p.bits hk
    hsize (row f p.upper) p.num p.sign (rows p.upper) ok

#print axioms signedAt_of_check
end OpenMathResearch.LongCycleExcedances.FastPointSamples
