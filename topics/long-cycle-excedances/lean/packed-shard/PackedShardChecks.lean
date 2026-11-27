import PackedEndpoints251
import PackedEndpoints252
import PackedEndpoints253
import PackedEndpoints254
import PackedEndpoints255

namespace OpenMathResearch.LongCycleExcedances.PackedShard
open WitnessLedger

theorem shard_gapOK (g : Gap) (hg : g ∈ checkedRows) : gapOK g = true := by
  obtain ⟨_, hlow, hhigh⟩ := shard_supported g hg
  have hs : g ∈ shardSlice g.n := by simp [shardSlice, hg]
  have hcases : g.n = 251 ∨ g.n = 252 ∨ g.n = 253 ∨ g.n = 254 ∨ g.n = 255 := by omega
  rcases hcases with h | h | h | h | h
  · exact List.all_eq_true.mp checks251 g (h ▸ hs)
  · exact List.all_eq_true.mp checks252 g (h ▸ hs)
  · exact List.all_eq_true.mp checks253 g (h ▸ hs)
  · exact List.all_eq_true.mp checks254 g (h ▸ hs)
  · exact List.all_eq_true.mp checks255 g (h ▸ hs)

#print axioms shard_gapOK
end OpenMathResearch.LongCycleExcedances.PackedShard
