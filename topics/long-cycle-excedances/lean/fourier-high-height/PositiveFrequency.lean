import HighHeightScalars
import Mathlib.Algebra.Order.Floor.Ring

set_option autoImplicit false
namespace OpenMathResearch.LongCycleExcedances
open Finset Real

theorem exp_mesh_sum {c : ℝ} (hc : 0 < c) (F : Finset ℕ) :
    (∑ a ∈ F, exp (-((a+1:ℕ):ℝ)*c)) ≤ 1/c := by
  have step (a : ℕ) :
      c*exp (-((a+1:ℕ):ℝ)*c) ≤ exp (-(a:ℝ)*c) - exp (-((a+1:ℕ):ℝ)*c) := by
    have he : exp c*exp (-((a+1:ℕ):ℝ)*c) = exp (-(a:ℝ)*c) := by
      rw [← exp_add]
      push_cast
      congr 1
      ring
    have hm := mul_le_mul_of_nonneg_right (add_one_le_exp c) (exp_pos (-((a+1:ℕ):ℝ)*c)).le
    rw [he] at hm
    linarith only [hm]
  have prefix_bound (n : ℕ) :
      (∑ a ∈ range n, c*exp (-((a+1:ℕ):ℝ)*c)) ≤ 1 - exp (-(n:ℝ)*c) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ]
      exact (add_le_add ih (step n)).trans_eq (by ring)
  let n := F.sup id + 1
  have hsub : F ⊆ range n := by
    intro i hi
    exact mem_range.mpr (Nat.lt_succ_of_le (le_sup (f := id) hi))
  rw [le_div_iff₀ hc, mul_comm, mul_sum]
  exact (sum_le_sum_of_subset_of_nonneg hsub (fun a _ _ => by positivity)).trans
    ((prefix_bound n).trans (by linarith [exp_pos (-(n:ℝ)*c)]))

/-- A positive-integer frequency band contains at most its real endpoint. -/
theorem positive_mesh_card {x : ℝ} (hx : 0 ≤ x) (F : Finset ℕ)
    (hF : ∀ a ∈ F, ((a+1:ℕ):ℝ) ≤ x) : (F.card : ℝ) ≤ x := by
  have hsub : F ⊆ range ⌊x⌋₊ := by
    intro a ha
    exact mem_range.mpr (Nat.lt_of_succ_le ((Nat.le_floor_iff hx).mpr (hF a ha)))
  calc
    (F.card:ℝ) ≤ (⌊x⌋₊:ℝ) := by
      exact_mod_cast (card_le_card hsub).trans (by simp)
    _ ≤ x := Nat.floor_le hx

/-- Pointwise envelopes on either side of a positive-frequency split. -/
theorem positive_mesh_split {x M B c : ℝ} (hx : 0 ≤ x) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hc : 0 < c) (F : Finset ℕ) (f : ℕ → ℝ)
    (hlo : ∀ a ∈ F, ((a+1:ℕ):ℝ) ≤ x → f a ≤ M)
    (hhi : ∀ a ∈ F, x < ((a+1:ℕ):ℝ) → f a ≤ B*exp (-((a+1:ℕ):ℝ)*c)) :
    (∑ a ∈ F, f a) ≤ x*M+B/c := by
  classical
  let low (a : ℕ) := ((a+1:ℕ):ℝ) ≤ x
  have hcL : ((F.filter low).card:ℝ) ≤ x :=
    positive_mesh_card hx _ (fun _ ha => (mem_filter.mp ha).2)
  have hsumL : (∑ a ∈ F.filter low, f a) ≤ x*M := by
    calc
      _ ≤ ∑ _a ∈ F.filter low, M :=
        sum_le_sum fun a ha => hlo a (mem_filter.mp ha).1 (mem_filter.mp ha).2
      _ ≤ _ := by
        rw [sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right hcL hM
  have hsumH : (∑ a ∈ F.filter (fun a => ¬low a), f a) ≤ B/c := by
    calc
      _ ≤ ∑ a ∈ F.filter (fun a => ¬low a), B*exp (-((a+1:ℕ):ℝ)*c) :=
        sum_le_sum fun a ha => hhi a (mem_filter.mp ha).1 (lt_of_not_ge (mem_filter.mp ha).2)
      _ = B*(∑ a ∈ F.filter (fun a => ¬low a), exp (-((a+1:ℕ):ℝ)*c)) := by rw [mul_sum]
      _ ≤ _ := by
        rw [show B/c=B*(1/c) by ring]
        exact mul_le_mul_of_nonneg_left (exp_mesh_sum hc _) hB
  rw [← sum_filter_add_sum_filter_not F low]
  exact add_le_add hsumL hsumH

#print axioms exp_mesh_sum
#print axioms positive_mesh_card
#print axioms positive_mesh_split
end OpenMathResearch.LongCycleExcedances
