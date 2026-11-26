import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Positivity

/-!
# Catalan-word strict-peak polynomials

The words are indexed from zero and stored in a finite alphabet of size n+1.
Every unbounded natural-valued Catalan word satisfies the same alphabet bound.
-/

namespace CatalanStrictPeaks

open Polynomial Finset
open scoped BigOperators

/-- A bounded word with n labeled positions. -/
abbrev Word (n : ℕ) := Fin n → Fin (n + 1)

/-- The first letter is zero, and each rise is at most one. -/
def IsCatalan {n : ℕ} (w : Word n) : Prop :=
  (∀ i : Fin n, i.val = 0 → (w i).val = 0) ∧
    ∀ i j : Fin n, j.val = i.val + 1 → (w j).val ≤ (w i).val + 1

instance {n : ℕ} (w : Word n) : Decidable (IsCatalan w) := by
  unfold IsCatalan
  infer_instance

/-- The bounded alphabet contains every natural-valued Catalan word. -/
theorem entry_le_index {n : ℕ} (w : Fin n → ℕ)
    (hzero : ∀ i : Fin n, i.val = 0 → w i = 0)
    (hstep : ∀ i j : Fin n, j.val = i.val + 1 → w j ≤ w i + 1)
    (i : Fin n) : w i ≤ i.val := by
  have all : ∀ k (hk : k < n), w ⟨k, hk⟩ ≤ k := by
    intro k
    induction k with
    | zero =>
      intro hk
      exact le_of_eq (hzero ⟨0, hk⟩ rfl)
    | succ k ih =>
      intro hk
      have hp : k < n := by omega
      have h := hstep ⟨k, hp⟩ ⟨k + 1, hk⟩ rfl
      exact h.trans (Nat.add_le_add_right (ih hp) 1)
  exact all i.val i.isLt

/-- The finite set of Catalan words of length n. -/
def words (n : ℕ) : Finset (Word n) := univ.filter IsCatalan

private def letter {n : ℕ} (w : Word n) (j : ℕ) : ℕ :=
  if h : j < n then (w ⟨j, h⟩).val else 0

/-- A strict peak in the middle of the triple starting at j. -/
def HasPeakAt {n : ℕ} (w : Word n) (j : ℕ) : Prop :=
  j + 2 < n ∧ letter w j < letter w (j + 1) ∧ letter w (j + 2) < letter w (j + 1)

instance {n : ℕ} (w : Word n) (j : ℕ) : Decidable (HasPeakAt w j) := by
  unfold HasPeakAt
  infer_instance

/-- The set of starts of triples with strict peaks. -/
def peaks {n : ℕ} (w : Word n) : Finset ℕ :=
  (range (n - 2)).filter (HasPeakAt w)

/-- The polynomial counting Catalan words by strict peaks. -/
noncomputable def C (n : ℕ) : ℝ[X] :=
  ∑ w ∈ words n, X ^ (peaks w).card

/-- The number of strict peaks attains at most this index. -/
def rowDegree (n : ℕ) : ℕ := (n - 1) / 2

private theorem peak_start_lt {n : ℕ} {w : Word n} {j : ℕ} (h : j ∈ peaks w) :
    j + 2 < n := by
  have hj := mem_range.mp (mem_filter.mp h).1
  omega

private theorem no_adjacent_peaks {n : ℕ} {w : Word n} {j : ℕ}
    (hj : j ∈ peaks w) (hnext : j + 1 ∈ peaks w) : False := by
  have h₁ : HasPeakAt w j := (mem_filter.mp hj).2
  have h₂ : HasPeakAt w (j + 1) := (mem_filter.mp hnext).2
  exact (not_lt_of_gt h₁.2.2) h₂.2.1

/-- Pair each peak's start with its successor to obtain the degree bound. -/
theorem peaks_card_le {n : ℕ} (w : Word n) : (peaks w).card ≤ rowDegree n := by
  let P := peaks w
  let S := P.image Nat.succ
  have hd : Disjoint P S := by
    apply disjoint_left.mpr
    intro j hj hs
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hs
    exact no_adjacent_peaks hi hj
  have hsub : P ∪ S ⊆ range (n - 1) := by
    intro j hj
    rw [mem_range]
    rcases mem_union.mp hj with hp | hs
    · have h := peak_start_lt hp
      omega
    · obtain ⟨i, hi, rfl⟩ := mem_image.mp hs
      have h := peak_start_lt hi
      omega
  have hc := card_le_card hsub
  rw [card_union_of_disjoint hd, card_range,
    show S.card = P.card from card_image_of_injective _ Nat.succ_injective] at hc
  change P.card ≤ (n - 1) / 2
  omega

private def zeroWord (n : ℕ) : Word n := fun _ => 0

private theorem zeroWord_mem (n : ℕ) : zeroWord n ∈ words n := by
  simp [words, IsCatalan, zeroWord]

private theorem zeroWord_no_peaks (n : ℕ) : peaks (zeroWord n) = ∅ := by
  rw [eq_empty_iff_forall_not_mem]
  intro j hj
  have hp := (mem_filter.mp hj).2
  simp [HasPeakAt, letter, zeroWord] at hp

private def alternate (n : ℕ) : Word n := fun i =>
  ⟨i.val % 2, (Nat.mod_le _ _).trans_lt (i.isLt.trans (Nat.lt_succ_self n))⟩

private theorem alternate_mem (n : ℕ) : alternate n ∈ words n := by
  rw [words, mem_filter]
  refine ⟨mem_univ _, ?_⟩
  constructor
  · intro i hi
    simp [alternate, hi]
  · intro i j h
    change j.val % 2 ≤ i.val % 2 + 1
    omega

private theorem alternate_peak_card (n : ℕ) : (peaks (alternate n)).card = rowDegree n := by
  refine le_antisymm (peaks_card_le _) ?_
  have hsub : (range (rowDegree n)).image (fun j => 2 * j) ⊆ peaks (alternate n) := by
    intro p hp
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hp
    have hj' := mem_range.mp hj
    unfold rowDegree at hj'
    have hinside : 2 * j + 2 < n := by omega
    rw [peaks, mem_filter, mem_range]
    refine ⟨by omega, ?_⟩
    have hzero : 2 * j < n := by omega
    have hone : 2 * j + 1 < n := by omega
    simp [HasPeakAt, letter, dif_pos hzero, dif_pos hone, dif_pos hinside, alternate]
    omega
  have hc := card_le_card hsub
  have hinj : Function.Injective (fun j : ℕ => 2 * j) := by
    intro i j hij
    change 2 * i = 2 * j at hij
    omega
  rw [card_image_of_injective _ hinj, card_range] at hc
  exact hc

/-- Coefficients count Catalan words with precisely the corresponding number of peaks. -/
theorem coeff_C (n k : ℕ) :
    (C n).coeff k = ((words n).filter (fun w => (peaks w).card = k)).card := by
  simp only [C, finset_sum_coeff, coeff_X_pow]
  rw [← sum_filter]
  simp [eq_comm]

/-- The strict-peak polynomial has positive constant coefficient. -/
theorem eval_zero_pos (n : ℕ) : 0 < (C n).eval 0 := by
  rw [← coeff_zero_eq_eval_zero, coeff_C]
  exact_mod_cast card_pos.mpr ⟨zeroWord n, mem_filter.mpr
    ⟨zeroWord_mem n, by simp [zeroWord_no_peaks]⟩⟩

private theorem coeff_at_degree_pos (n : ℕ) : 0 < (C n).coeff (rowDegree n) := by
  rw [coeff_C]
  exact_mod_cast card_pos.mpr ⟨alternate n, mem_filter.mpr
    ⟨alternate_mem n, alternate_peak_card n⟩⟩

/-- The strict-peak polynomial has exactly degree floor((n−1)/2). -/
theorem natDegree_C (n : ℕ) : (C n).natDegree = rowDegree n := by
  apply natDegree_eq_of_le_of_coeff_ne_zero _ (coeff_at_degree_pos n).ne'
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [coeff_C]
  have hEmpty : (words n).filter (fun w => (peaks w).card = k) = ∅ := by
    rw [eq_empty_iff_forall_not_mem]
    intro w hw
    have heq := (mem_filter.mp hw).2
    have hle := peaks_card_le w
    omega
  simp [hEmpty]

/-- The exact leading coefficient is positive, including constant rows. -/
theorem leadingCoeff_pos (n : ℕ) : 0 < (C n).leadingCoeff := by
  rw [leadingCoeff, natDegree_C]
  exact coeff_at_degree_pos n

end CatalanStrictPeaks
