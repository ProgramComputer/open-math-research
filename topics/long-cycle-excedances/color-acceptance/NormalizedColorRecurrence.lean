import ColorRecurrence
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false
namespace OpenMathResearch.LongCycleExcedances.ColorAnchor
open Finset

theorem taggedCount_eq_finset (n p k : ℕ) :
    taggedCount n p k = (acceptedFinset n p k).card := by
  classical
  have e : (↑(acceptedFinset n p k) : Type) ≃ GoodPairs (Fin n) (Fin p) k :=
    Equiv.subtypeEquiv (Equiv.refl _) mem_acceptedFinset
  rw [taggedCount, ← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]

theorem taggedCount_zero_left (p k : ℕ) (hk : 1 ≤ k) :
    taggedCount 0 p k = if p = 0 then 1 else 0 := by
  rw [taggedCount_eq_finset]
  cases p with
  | zero =>
    have hf : acceptedFinset 0 0 k = univ := by
      ext pair
      simp [acceptedFinset]
    simp [hf, Fintype.card_prod, Fintype.card_fun, Fintype.card_perm]
  | succ p =>
    have he : acceptedFinset 0 (p + 1) k = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro pair h
      have hh : ∀ c, k ≤ boundedLoad pair.1 pair.2 c := (mem_filter.mp h).2
      have hz := hh 0
      simp [boundedLoad] at hz
      omega
    simp [he]

theorem taggedCount_zero_right (n k : ℕ) (hk : 1 ≤ k) :
    taggedCount n 0 k = if n = 0 then 1 else 0 := by
  cases n with
  | zero => exact taggedCount_zero_left 0 k hk
  | succ n => simp [taggedCount_succ n 0 k hk]

noncomputable def normalizedCount (n p k : ℕ) : ℚ :=
  (taggedCount n p k : ℚ) / (p.factorial : ℚ)

theorem normalizedCount_zero_left (p k : ℕ) (hk : 1 ≤ k) :
    normalizedCount 0 p k = if p = 0 then 1 else 0 := by
  rw [normalizedCount, taggedCount_zero_left p k hk]
  split <;> rename_i h
  · subst p
    norm_num
  · norm_num

theorem normalizedCount_succ (n p k : ℕ) (hk : 1 ≤ k) :
    normalizedCount (n+1) p k =
      ∑ m ∈ Icc k (n+1), ∑ j ∈ Icc 1 p,
        (n.choose (m-1) : ℚ) * (j : ℚ)^(m-1) * normalizedCount (n+1-m) (p-j) k := by
  rw [normalizedCount, taggedCount_succ n p k hk]
  simp only [Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, Finset.sum_div]
  apply sum_congr rfl
  intro m hm
  apply sum_congr rfl
  intro j hj
  have hjp := (mem_Icc.mp hj).2
  have hj1 := (mem_Icc.mp hj).1
  have hm1 := hk.trans (mem_Icc.mp hm).1
  have hc : (p.choose j : ℚ) * (j.factorial : ℚ) * ((p-j).factorial : ℚ) =
      (p.factorial : ℚ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hjp
  have hf : (j.factorial : ℚ) = (j : ℚ) * ((j-1).factorial : ℚ) := by
    exact_mod_cast (Nat.mul_factorial_pred (by omega : j ≠ 0)).symm
  have hpw : (j : ℚ)^m = (j : ℚ)^(m-1) * (j : ℚ) := by
    rw [← pow_succ, Nat.sub_add_cancel hm1]
  have hp0 : (p.factorial : ℚ) ≠ 0 := by positivity
  have hr0 : ((p-j).factorial : ℚ) ≠ 0 := by positivity
  rw [normalizedCount, hpw]
  field_simp
  rw [← hc, hf]
  ring

#print axioms taggedCount_eq_finset
#print axioms taggedCount_zero_left
#print axioms taggedCount_zero_right
#print axioms normalizedCount_zero_left
#print axioms normalizedCount_succ
end OpenMathResearch.LongCycleExcedances.ColorAnchor
