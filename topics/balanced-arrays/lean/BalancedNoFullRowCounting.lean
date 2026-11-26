import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi

/-! Counting balanced arrays whose rows each have at least one zero. -/
namespace BalancedNoFullRowCounting

open Finset
open scoped BigOperators

abbrev Holes (n d : ℕ) := Fin d → Finset (Fin n)
abbrev BinaryArray (n d : ℕ) := Fin n → Fin d → Bool

/-- Column supports of zeros, each with the prescribed cardinality. -/
def columns (n d l : ℕ) : Finset (Holes n d) :=
  Fintype.piFinset (fun _ => (univ : Finset (Fin n)).powersetCard l)

/-- Rows missed by every set of zeros are the full rows. -/
def missed {n d : ℕ} (a : Holes n d) : Finset (Fin n) :=
  univ.filter (fun i => ∀ c, i ∉ a c)

def covering (n d l : ℕ) : Finset (Holes n d) :=
  (columns n d l).filter (fun a => missed a = ∅)

private theorem avoid (n d l : ℕ) (J : Finset (Fin n)) :
    ((columns n d l).filter (fun a => J ⊆ missed a)) =
      Fintype.piFinset (fun _ : Fin d => ((univ : Finset (Fin n)) \ J).powersetCard l) := by
  ext a
  simp only [columns, mem_filter, Fintype.mem_piFinset, mem_powersetCard, subset_univ, true_and]
  constructor
  · rintro ⟨hc, hJ⟩ c
    refine ⟨?_, hc c⟩
    intro i hi
    refine mem_sdiff.mpr ⟨mem_univ _, ?_⟩
    intro hij
    exact (mem_filter.mp (hJ hij)).2 c hi
  · intro ha
    refine ⟨fun c => (ha c).2, ?_⟩
    intro i hi
    refine mem_filter.mpr ⟨mem_univ _, ?_⟩
    intro c hc
    exact (mem_sdiff.mp ((ha c).1 hc)).2 hi

/-- Inclusion-exclusion for covers by d labeled, equal-size column supports. -/
theorem covering_card (n d l : ℕ) :
    ((covering n d l).card : ℤ) = ∑ j ∈ range (n+1),
       (-1 : ℤ)^j * (n.choose j : ℤ) * ((n-j).choose l : ℤ)^d := by
  classical
  calc
    ((covering n d l).card : ℤ) = ∑ a ∈ columns n d l,
        if missed a = ∅ then (1:ℤ) else 0 := by
      rw [← sum_filter]
      simp [covering]
    _ = ∑ a ∈ columns n d l, ∑ J ∈ (univ : Finset (Fin n)).powerset,
        if J ⊆ missed a then (-1:ℤ)^J.card else 0 := by
      apply sum_congr rfl
      intro a _
      have h : (univ.powerset.filter (fun J : Finset (Fin n) => J ⊆ missed a)) =
          (missed a).powerset := by ext J; simp
      rw [← sum_filter, h, sum_powerset_neg_one_pow_card]
    _ = ∑ J ∈ (univ : Finset (Fin n)).powerset,
        (-1:ℤ)^J.card * ((n-J.card).choose l : ℤ)^d := by
      rw [sum_comm]
      apply sum_congr rfl
      intro J _
      rw [← sum_filter, sum_const, avoid, Fintype.card_piFinset]
      simp [card_powersetCard, card_sdiff (subset_univ J), nsmul_eq_mul, mul_comm]
    _ = _ := by
      rw [sum_powerset_apply_card (fun j => (-1:ℤ)^j * ((n-j).choose l : ℤ)^d)]
      simp only [card_univ, Fintype.card_fin]
      apply sum_congr rfl
      intro j _
      rw [nsmul_eq_mul]
      ac_rfl

/-- The original matrix constraints, with ones counted in each row and column. -/
def arrays (n d k : ℕ) : Finset (BinaryArray n d) :=
  univ.filter (fun a =>
    (∀ c, (univ.filter (fun i => a i c = true)).card = k) ∧
    ∀ i, (univ.filter (fun c => a i c = true)).card ≤ d-1)

def zeroColumns {n d : ℕ} (a : BinaryArray n d) : Holes n d :=
  fun c => univ.filter (fun i => a i c = false)

def fromColumns {n d : ℕ} (a : Holes n d) : BinaryArray n d :=
  fun i c => decide (i ∉ a c)

private theorem zero_from {n d : ℕ} (a : Holes n d) : zeroColumns (fromColumns a) = a := by
  funext c
  ext i
  simp [zeroColumns, fromColumns]

private theorem from_zero {n d : ℕ} (a : BinaryArray n d) : fromColumns (zeroColumns a) = a := by
  funext i c
  cases e : a i c <;> simp [zeroColumns, fromColumns, e]

private theorem ones_iff {n d k : ℕ} (a : BinaryArray n d) (c : Fin d) (hk : k ≤ n) :
    (univ.filter (fun i => a i c = true)).card = k ↔ (zeroColumns a c).card = n-k := by
  have h : (zeroColumns a c)ᶜ = univ.filter (fun i => a i c = true) := by
    ext i
    cases e : a i c <;> simp [zeroColumns, e]
  rw [← h, card_compl, Fintype.card_fin]
  have hb : (zeroColumns a c).card ≤ n := by simpa using card_le_univ (zeroColumns a c)
  omega

private theorem cap_iff {n d : ℕ} (a : BinaryArray n d) (hd : 0 < d) :
    (∀ i, (univ.filter (fun c => a i c = true)).card ≤ d-1) ↔ missed (zeroColumns a) = ∅ := by
  have h (i : Fin n) :
      (univ.filter (fun c => a i c = true)).card ≤ d-1 ↔ ¬ ∀ c, a i c = true := by
    let S : Finset (Fin d) := univ.filter (fun c => a i c = true)
    have hs : S = univ ↔ ∀ c, a i c = true := by
      constructor
      · intro he c
        have hc : c ∈ S := he.symm ▸ mem_univ c
        exact (mem_filter.mp hc).2
      · intro ha
        ext c
        simp [S, ha c]
    have hc : S.card ≤ d := by simpa using card_le_univ S
    have he : S.card = d ↔ S = univ := by
      simpa only [Fintype.card_fin] using S.card_eq_iff_eq_univ
    change S.card ≤ d-1 ↔ _
    rw [← hs, ← he]
    omega
  rw [show (∀ i, (univ.filter (fun c => a i c = true)).card ≤ d-1) ↔
      ∀ i, ¬ ∀ c, a i c = true from forall_congr' h]
  simp [missed, zeroColumns, filter_eq_empty_iff]

theorem arrays_card (n d k : ℕ) (hd : 0 < d) (hk : k ≤ n) :
    ((arrays n d k).card : ℤ) = ∑ j ∈ range (n+1),
       (-1 : ℤ)^j * (n.choose j : ℤ) * ((n-j).choose (n-k) : ℤ)^d := by
  classical
  have hmem (a : BinaryArray n d) : a ∈ arrays n d k ↔ zeroColumns a ∈ covering n d (n-k) := by
    simp only [arrays, covering, columns, mem_filter, mem_univ, true_and,
      Fintype.mem_piFinset, mem_powersetCard, subset_univ]
    rw [cap_iff a hd]
    exact and_congr_left (fun _ => forall_congr' (fun c => ones_iff a c hk))
  have hcard : (arrays n d k).card = (covering n d (n-k)).card := by
    apply card_bij (fun a _ => zeroColumns a)
    · exact fun a ha => (hmem a).mp ha
    · intro a _ b _ hab
      simpa only [from_zero] using congrArg fromColumns hab
    · intro b hb
      exact ⟨fromColumns b, (hmem _).mpr (by rwa [zero_from]), zero_from b⟩
  rw [hcard, covering_card]

/-- The finite sum in the determinant proof, for the original labeled matrices. -/
theorem array_inclusion_exclusion (n d k : ℕ) (hd : 0 < d) (hk : k ≤ n) :
    ((arrays n d k).card : ℤ) = ∑ j ∈ range (k+1),
       (-1 : ℤ)^j * (n.choose j : ℤ) * ((n-j).choose (k-j) : ℤ)^d := by
  rw [arrays_card n d k hd hk]
  calc
    _ = ∑ j ∈ range (k+1), (-1 : ℤ)^j * (n.choose j : ℤ) * ((n-j).choose (n-k) : ℤ)^d := by
      symm
      apply sum_subset (range_mono (by omega : k + 1 ≤ n + 1))
      intro j hj hjk
      have jle : j ≤ n := Nat.le_of_lt_succ (mem_range.mp hj)
      have jgt : k < j := by
        simp only [mem_range] at hjk
        omega
      rw [Nat.choose_eq_zero_of_lt (by omega : n-j < n-k)]
      simp [zero_pow (Nat.ne_of_gt hd)]
    _ = _ := by
      apply sum_congr rfl
      intro j hj
      have hjk : j ≤ k := Nat.le_of_lt_succ (mem_range.mp hj)
      rw [Nat.choose_symm_of_eq_add (by omega : n-j = (n-k) + (k-j))]

end BalancedNoFullRowCounting
