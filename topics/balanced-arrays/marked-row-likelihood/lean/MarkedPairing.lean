import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! Exact pairing multiplicities for the marked-row likelihood comparison.
The dummy is the red slot numbered zero. A blue-exclusive mark, when present,
has the specified slot in the codomain of the pairing. Weights are scaled
by K+1 in each column. -/
namespace MarkedPairing
open scoped BigOperators

def weight (h K : ℕ) (mark : Option (Fin (h+1))) (p : Equiv.Perm (Fin (h+1))) : ℚ :=
  (K+1 : ℚ) - if some (p 0) = mark then (h+1 : ℚ) else 0

theorem weight_nonneg (h K : ℕ) (bound : h ≤ K) (mark) (p) :
    0 ≤ weight h K mark p := by
  unfold weight
  split
  · exact sub_nonneg.mpr (by exact_mod_cast Nat.add_le_add_right bound 1)
  · simp only [sub_zero]
    positivity

theorem sum_hit (h : ℕ) (m : Fin (h+1)) :
    (∑ p : Equiv.Perm (Fin (h+1)), if p 0 = m then (h+1 : ℚ) else 0) =
      (h+1 : ℚ) * h.factorial := by
  classical
  rw [← (Equiv.Perm.decomposeFin (n := h)).symm.sum_comp
    (fun p => if p 0 = m then (h+1 : ℚ) else 0), Fintype.sum_prod_type]
  simp [Fintype.card_perm, mul_comm]
  ring

theorem column_sum (h K : ℕ) (mark : Option (Fin (h+1))) :
    (∑ p, weight h K mark p) =
      ((h+1).factorial : ℚ) * (if mark.isSome then (K : ℚ) else K+1) := by
  classical
  cases mark with
  | none =>
    simp [weight, Fintype.card_perm, mul_comm]
    ring
  | some m =>
    simp only [weight, Option.some.injEq, Finset.sum_sub_distrib, sum_hit,
      Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
      nsmul_eq_mul, Option.isSome_some, if_true, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
      Nat.cast_one]
    ring

theorem all_columns (d K : ℕ) (h : Fin d → ℕ) (marks : (j : Fin d) → Option (Fin (h j+1))) :
    (∑ p : (j : Fin d) → Equiv.Perm (Fin (h j+1)), ∏ j, weight (h j) K (marks j) (p j)) =
      ∏ j, (((h j+1).factorial : ℚ) * (if (marks j).isSome then (K : ℚ) else K+1)) := by
  classical
  simp_rw [← column_sum]
  simpa using (Finset.prod_univ_sum (fun j : Fin d => (Finset.univ : Finset (Equiv.Perm (Fin (h j+1)))))
    (fun j p => weight (h j) K (marks j) p)).symm

theorem cancel_common_marks (c s t : ℕ) (hcs : c ≤ s) (hst : s ≤ t)
    (ρ source target : ℚ) (hρ : 0 < ρ)
    (comparison : ρ^(s-c) * source ≤ ρ^(t-c) * target) :
    (1/ρ)^(t-s) * source ≤ target := by
  have powers : t-c = (s-c)+(t-s) := by omega
  rw [powers, pow_add, mul_assoc] at comparison
  have h := (mul_le_mul_left (pow_pos hρ (s-c))).mp comparison
  rw [one_div, inv_pow, inv_mul_le_iff₀ (pow_pos hρ (t-s))]
  exact h

theorem sharp_binomial_factor (K d : ℕ) (pos : 0 < K) :
    ((2*K).choose K)^d * K^d = ((2*K).choose (K-1))^d * (K+1)^d := by
  have h := Nat.choose_succ_right_eq (2*K) (K-1)
  rw [show K-1+1=K by omega, show 2*K-(K-1)=K+1 by omega] at h
  simpa only [mul_pow] using congrArg (fun a : ℕ => a^d) h

/-- The hypergeometric numerator counts actual row-label subsets by a bijection. -/
theorem overlap_profile_card {α : Type*} [DecidableEq α]
    (rows blue : Finset α) (hb : blue ⊆ rows) (i h : ℕ) :
    (rows.powerset.filter (fun red => (red ∩ blue).card = i ∧ (red \ blue).card = h)).card =
      blue.card.choose i * (rows \ blue).card.choose h := by
  classical
  rw [← Finset.card_powersetCard, ← Finset.card_powersetCard, ← Finset.card_product]
  apply Finset.card_bij (fun red _ => (red ∩ blue, red \ blue))
  · intro red hr
    obtain ⟨hsub, hi, hh⟩ := Finset.mem_filter.mp hr
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_powersetCard.mpr ⟨Finset.inter_subset_right, hi⟩,
            Finset.mem_powersetCard.mpr ⟨?_, hh⟩⟩
    intro x hx
    obtain ⟨hrx,hbx⟩ := Finset.mem_sdiff.mp hx
    exact Finset.mem_sdiff.mpr ⟨(Finset.mem_powerset.mp hsub) hrx,hbx⟩
  · intro red _ red' _ heq
    have h₁ : red ∩ blue = red' ∩ blue := congrArg Prod.fst heq
    have h₂ : red \ blue = red' \ blue := congrArg Prod.snd heq
    calc
      red = (red \ blue) ∪ (red ∩ blue) := (Finset.sdiff_union_inter _ _).symm
      _ = red' := by rw [h₁,h₂,Finset.sdiff_union_inter]
  · rintro ⟨x,y⟩ hxy
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp hxy
    obtain ⟨hxB,hxcard⟩ := Finset.mem_powersetCard.mp hx
    obtain ⟨hyB,hycard⟩ := Finset.mem_powersetCard.mp hy
    have inter : (x ∪ y) ∩ blue = x := by
      ext j
      simp only [Finset.mem_inter,Finset.mem_union]
      constructor
      · rintro ⟨hxj|hyj,hbj⟩
        · exact hxj
        · exact ((Finset.mem_sdiff.mp (hyB hyj)).2 hbj).elim
      · intro hxj
        exact ⟨Or.inl hxj,hxB hxj⟩
    have diff : (x ∪ y) \ blue = y := by
      ext j
      simp only [Finset.mem_sdiff,Finset.mem_union]
      constructor
      · rintro ⟨hxj|hyj,hbj⟩
        · exact (hbj (hxB hxj)).elim
        · exact hyj
      · intro hyj
        exact ⟨Or.inr hyj,(Finset.mem_sdiff.mp (hyB hyj)).2⟩
    refine ⟨x ∪ y, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, ?_⟩, ?_⟩
    · exact Finset.union_subset (fun _ hj => hb (hxB hj))
        (fun _ hj => (Finset.mem_sdiff.mp (hyB hj)).1)
    · rw [inter,diff]
      exact ⟨hxcard,hycard⟩
    · exact Prod.ext inter diff

/-- The sum uses i for the overlap and h for the red-only count, with i+h=a.
The margins are a and a+u+1, on a+u+1+c rows. -/
def removedWeight (a u c : ℕ) : ℚ :=
  ∑ ij ∈ Finset.antidiagonal a, ((a+u).choose ij.1 : ℚ) * c.choose ij.2 *
    (u+1 : ℚ) / ((ij.2 : ℚ)+u+1)

theorem removedWeight_mul (a u c : ℕ) :
    removedWeight a u c * ((a : ℚ)+u+1) = (u+1 : ℚ) * (a+u+1+c).choose a := by
  have hv : ((a+u+1+c).choose a : ℚ) =
      ∑ ij ∈ Finset.antidiagonal a, ((a+u+1).choose ij.1 : ℚ) * c.choose ij.2 := by
    exact_mod_cast Nat.add_choose_eq (a+u+1) c a
  rw [removedWeight, Finset.sum_mul, hv, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ij hij
  have hs : ij.1 + ij.2 = a := Finset.mem_antidiagonal.mp hij
  have hn := Nat.choose_mul_succ_eq (a+u) ij.1
  rw [show a+u+1-ij.1=ij.2+u+1 by omega] at hn
  have hq : ((a+u).choose ij.1 : ℚ)*((a : ℚ)+u+1) =
      ((a+u+1).choose ij.1 : ℚ)*((ij.2 : ℚ)+u+1) := by exact_mod_cast hn
  have hd : (ij.2 : ℚ)+u+1 ≠ 0 := by positivity
  rw [div_mul_eq_mul_div, div_eq_iff hd]
  calc
    _ = (((a+u).choose ij.1 : ℚ)*((a : ℚ)+u+1)) * c.choose ij.2 * (u+1) := by ring
    _ = _ := by rw [hq]; ring

theorem removed_probability (a u c : ℕ) :
    removedWeight a u c / ((a+u+c).choose a : ℚ) =
      ((u : ℚ)+1)*(a+u+c+1) / (((a : ℚ)+u+1)*(u+c+1)) := by
  have hn := Nat.choose_mul_succ_eq (a+u+c) a
  rw [show a+u+c+1-a=u+c+1 by omega] at hn
  have hq : ((a+u+c).choose a : ℚ)*((a : ℚ)+u+c+1) =
      ((a+u+c+1).choose a : ℚ)*((u : ℚ)+c+1) := by exact_mod_cast hn
  rw [show a+u+c+1=a+u+1+c by omega] at hq
  have hz : ((a+u+c).choose a : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (show a ≤ a+u+c by omega)).ne'
  have hp : ((a : ℚ)+u+1)*((u : ℚ)+c+1) ≠ 0 := by positivity
  rw [div_eq_div_iff hz hp]
  calc
    _ = (removedWeight a u c*((a : ℚ)+u+1))*((u : ℚ)+c+1) := by ring
    _ = ((u : ℚ)+1)*(((a+u+1+c).choose a : ℚ)*((u : ℚ)+c+1)) := by
      rw [removedWeight_mul]; ring
    _ = _ := by rw [← hq]; ring

theorem retained_probability (a u c : ℕ) :
    1 - removedWeight a u c / ((a+u+c).choose a : ℚ) =
      (a : ℚ)*c/(((a : ℚ)+u+1)*(u+c+1)) := by
  rw [removed_probability]
  have hd : ((a : ℚ)+u+1)*((u : ℚ)+c+1) ≠ 0 := by positivity
  field_simp
  ring

end MarkedPairing

#print axioms MarkedPairing.weight_nonneg
#print axioms MarkedPairing.sum_hit
#print axioms MarkedPairing.column_sum
#print axioms MarkedPairing.all_columns
#print axioms MarkedPairing.cancel_common_marks
#print axioms MarkedPairing.sharp_binomial_factor
#print axioms MarkedPairing.overlap_profile_card
#print axioms MarkedPairing.removedWeight_mul
#print axioms MarkedPairing.removed_probability
#print axioms MarkedPairing.retained_probability
