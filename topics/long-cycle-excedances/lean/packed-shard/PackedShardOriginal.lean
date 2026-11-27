import PackedRowSteps
import PackedShardChecks
import RepositoryPackedPoint

namespace RepositoryQuotientAudit
open Polynomial LongCycles WitnessLedger
open OpenMathResearch.LongCycleExcedances
open PackedShard TruncatedRows IntegerSign

set_option maxRecDepth 10000 in
private theorem weight_agrees : ∀ i, i < width → weight i = compactCycleWeight 13 i := by
  have h : ∀ i : Fin width, weight i = compactCycleWeight 13 i := by decide
  exact fun i hi => h ⟨i, hi⟩

theorem packedShard_row (n : ℕ) (hn : n ≤ 256) (i : ℕ) (hi : i < width) :
    readCount (packedRow n) i = lowerRows 48 13 (by decide) (compactCycleWeight 13) n i :=
  packedTable_sound packedRow (compactCycleWeight 13) 256 weight_agrees
    packedRow_short packedRow_seed packedSteps n hn i hi

/-- A strict signed value of the original, unweighted reduced row. -/
def signedAtShard (n : ℕ) (d : WitnessLedger.Dyadic) (s : ℤ) : Prop :=
  0 < (s : ℝ) * ((enumerator n 13).divX).eval (-(d.value : ℝ))

private theorem signedAtShard_of_check (n : ℕ) (hn : n ≤ 256) (d : WitnessLedger.Dyadic) (s : ℤ)
    (h : endpoint n d s = true) : signedAtShard n d s := by
  have h' := original_signed_of_packed_words 13 n width (by decide) (by omega)
    (packedRow n) (d.num : ℤ) (2^d.bits) s (packedShard_row n hn) h
  simpa [signedAtShard, WitnessLedger.Dyadic.value] using h'

/-- The actual old and new reduced rows have the four prescribed strict signs
at each of the 131 archived gaps of cutoff 13 and old sizes 251 through 255. -/
theorem firstShard_original_signs (g : Gap) (hg : g ∈ checkedRows) :
    g.k = 13 ∧ 251 ≤ g.n ∧ g.n ≤ 255 ∧
    signedAtShard g.n g.a (oldLeftSign g.rank) ∧
    signedAtShard g.n g.b (-(oldLeftSign g.rank)) ∧
    signedAtShard (g.n+1) g.a (-(oldLeftSign g.rank)) ∧
    signedAtShard (g.n+1) g.b (-(oldLeftSign g.rank)) := by
  obtain ⟨hk, hlo, hhi⟩ := shard_supported g hg
  have pass := shard_gapOK g hg
  unfold gapOK at pass
  obtain ⟨a, b, c, d⟩ := of_decide_eq_true pass
  exact ⟨hk, hlo, hhi, signedAtShard_of_check _ (by omega) _ _ a,
    signedAtShard_of_check _ (by omega) _ _ b,
    signedAtShard_of_check _ (by omega) _ _ c,
    signedAtShard_of_check _ (by omega) _ _ d⟩

#print axioms packedShard_row
#print axioms firstShard_original_signs
end RepositoryQuotientAudit
