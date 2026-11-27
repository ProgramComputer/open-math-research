import Init.Data.List.Lemmas
import Init.Data.Nat.Bitwise.Lemmas

namespace OpenMathResearch.LongCycleExcedances.PackedShard

/-- The first word occupies the least significant 64 bits. -/
def packWordRow : List Nat → Nat
  | [] => 0
  | word :: rest => word + (packWordRow rest <<< 64)

def unpackWordRow : Nat → Nat → List Nat
  | 0, _ => []
  | n+1, row => row % (1 <<< 64) :: unpackWordRow n (row >>> 64)

theorem unpackWordRow_packWordRow (words : List Nat)
    (hwords : ∀ word ∈ words, word < 2^64) :
    unpackWordRow words.length (packWordRow words) = words := by
  induction words with
  | nil => rfl
  | cons x xs ih =>
    rw [List.forall_mem_cons] at hwords
    have hbase : 0 < (2:Nat)^64 := by decide
    simp only [List.length_cons, packWordRow, unpackWordRow, Nat.shiftLeft_eq, Nat.one_mul,
      Nat.shiftRight_eq_div_pow, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hwords.1,
      Nat.add_mul_div_right _ _ hbase, Nat.div_eq_of_lt hwords.1, Nat.zero_add, ih hwords.2]

#print axioms unpackWordRow_packWordRow
end OpenMathResearch.LongCycleExcedances.PackedShard
