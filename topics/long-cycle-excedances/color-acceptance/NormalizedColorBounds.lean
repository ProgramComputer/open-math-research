import NormalizedColorRecurrence
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.Linarith

set_option autoImplicit false
namespace OpenMathResearch.LongCycleExcedances.ColorAnchor
open Finset

noncomputable def realCount (n p k : ℕ) : ℝ := normalizedCount n p k

theorem realCount_zero (p k : ℕ) (hk : 1 ≤ k) :
    realCount 0 p k = if p = 0 then 1 else 0 := by
  unfold realCount
  rw [normalizedCount_zero_left p k hk]
  split <;> norm_num

theorem realCount_recurrence (n p k : ℕ) (hk : 2 ≤ k) (hn : 0 < n) :
    realCount n p k = ∑ m ∈ Icc k n, (((n-1).choose (m-1)):ℝ) *
      ∑ j ∈ range (p+1), (j:ℝ)^(m-1) * realCount (n-m) (p-j) k := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  unfold realCount
  rw [normalizedCount_succ d p k (by omega : 1 ≤ k)]
  push_cast
  apply sum_congr rfl
  intro m hm
  rw [mul_sum]
  have h0 : (0 : ℝ) ^ (m - 1) = 0 := by
    apply zero_pow
    have := (mem_Icc.mp hm).1
    omega
  have hset : Icc 1 p = (range (p+1)).erase 0 := by
    ext j
    simp
    omega
  rw [hset]
  have hsum := sum_erase_add (range (p+1))
    (fun j => (d.choose (m-1):ℝ) * (j:ℝ)^(m-1) *
      (normalizedCount (d+1-m) (p-j) k : ℝ)) (show 0 ∈ range (p+1) by simp)
  simp only [Nat.cast_zero, h0, mul_zero, zero_mul, add_zero] at hsum
  calc
    _ = ∑ j ∈ range (p+1), (d.choose (m-1):ℝ) * (j:ℝ)^(m-1) *
      (normalizedCount (d+1-m) (p-j) k : ℝ) := hsum
    _ = _ := by
      apply sum_congr rfl
      intro j _
      rw [mul_assoc]

theorem realCount_bounds (n p k : ℕ) : 0 ≤ realCount n p k ∧ realCount n p k ≤ (p:ℝ)^n := by
  have hcard : taggedCount n p k ≤ p^n * p.factorial := by
    rw [taggedCount_eq_finset]
    calc
      _ ≤ (univ : Finset ((Fin n → Fin p) × Equiv.Perm (Fin p))).card :=
        card_le_card (subset_univ _)
      _ = _ := by simp [Fintype.card_prod, Fintype.card_fun, Fintype.card_perm]
  unfold realCount normalizedCount
  push_cast
  have hpos : (0:ℝ) < p.factorial := by exact_mod_cast Nat.factorial_pos p
  refine ⟨div_nonneg (Nat.cast_nonneg _) hpos.le, (div_le_iff₀ hpos).mpr ?_⟩
  exact_mod_cast hcard

#print axioms realCount_zero
#print axioms realCount_recurrence
#print axioms realCount_bounds
end OpenMathResearch.LongCycleExcedances.ColorAnchor
