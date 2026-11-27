import PackedRowData
import CompactPoint
import CheckedShard

namespace OpenMathResearch.LongCycleExcedances.PackedShard
open TruncatedRows IntegerSign WitnessLedger

def oldLeftSign (rank : ℕ) : ℤ := if rank % 2 = 1 then 1 else -1

def endpoint (n : ℕ) (d : Dyadic) (s : ℤ) : Bool :=
  packedPointCheck n width (fun i => (readCount (packedRow n) i : ℤ)) d.num (2^d.bits) s

def gapOK (g : Gap) : Bool :=
  let s := oldLeftSign g.rank
  decide (endpoint g.n g.a s = true ∧ endpoint g.n g.b (-s) = true ∧
    endpoint (g.n+1) g.a (-s) = true ∧ endpoint (g.n+1) g.b (-s) = true)

def shardSlice (n : ℕ) : List Gap := checkedRows.filter fun g => g.n == n

set_option maxRecDepth 10000 in
theorem checkedShard_card : checkedRows.length = 131 := by decide

private theorem support_ok :
    checkedRows.all (fun g => decide (g.k = 13 ∧ 251 ≤ g.n ∧ g.n ≤ 255)) = true := by decide

theorem shard_supported (g : Gap) (hg : g ∈ checkedRows) :
    g.k = 13 ∧ 251 ≤ g.n ∧ g.n ≤ 255 :=
  of_decide_eq_true (List.all_eq_true.mp support_ok g hg)

#print axioms checkedShard_card
#print axioms shard_supported
end OpenMathResearch.LongCycleExcedances.PackedShard
