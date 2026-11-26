import CatalanStrictPeaksRecurrence

/-!
# First return for the strict Catalan peak weight

A nonempty word decomposes as 0, a translated positive block, then a suffix
beginning at the first later zero. The next lemma isolates the change in
the statistic at that split.
-/

namespace CatalanStrictPeaks.FirstReturn

open Polynomial Finset
open scoped BigOperators

/-- Natural-valued word access, extended by zero outside the word. -/
def read {n : ℕ} (w : Word n) (i : ℕ) : ℕ :=
  if h : i < n then (w ⟨i, h⟩).val else 0

@[simp] theorem read_in {n : ℕ} (w : Word n) (i : Fin n) :
    read w i.val = (w i).val := by simp [read, i.isLt]

theorem read_lt_alphabet {n : ℕ} (w : Word n) (i : ℕ) : read w i < n + 1 := by
  unfold read
  split
  · exact (w _).isLt
  · omega

theorem isCatalan_iff_read {n : ℕ} (w : Word n) :
    IsCatalan w ↔ read w 0 = 0 ∧ ∀ i, i + 1 < n → read w (i + 1) ≤ read w i + 1 := by
  constructor
  · intro h
    constructor
    · by_cases hn : 0 < n
      · exact (read_in w ⟨0, hn⟩).trans (h.1 ⟨0, hn⟩ rfl)
      · simp [read, hn]
    · intro i hi
      have hi' : i < n := by omega
      rw [show read w (i + 1) = (w ⟨i + 1, hi⟩).val from read_in w ⟨i + 1, hi⟩,
        show read w i = (w ⟨i, hi'⟩).val from read_in w ⟨i, hi'⟩]
      exact h.2 ⟨i, hi'⟩ ⟨i + 1, hi⟩ rfl
  · intro h
    constructor
    · intro i hi
      rw [← read_in, hi]
      exact h.1
    · intro i j hstep
      rw [← read_in, ← read_in, hstep]
      exact h.2 i.val (hstep ▸ j.isLt)

theorem hasPeak_read {n : ℕ} (w : Word n) (i : ℕ) :
    HasPeakAt w i ↔ i + 2 < n ∧ read w i < read w (i + 1) ∧
      read w (i + 2) < read w (i + 1) := Iff.rfl

private def joinedHeight {n a : ℕ} (u : Word a) (v : Word (n - a)) (i : ℕ) : ℕ :=
  if i = 0 then 0 else if i ≤ a then read u (i - 1) + 1 else read v (i - a - 1)

/-- Form the nonempty word 0 (u+1) v. -/
def join {n a : ℕ} (ha : a ≤ n) (u : Word a) (v : Word (n - a)) : Word (n + 1) := fun i =>
  ⟨joinedHeight u v i.val, by
    unfold joinedHeight
    split
    · omega
    · split
      · have h := read_lt_alphabet u (i.val - 1)
        omega
      · have h := read_lt_alphabet v (i.val - a - 1)
        omega⟩

private theorem read_join {n a : ℕ} (ha : a ≤ n) (u : Word a) (v : Word (n - a))
    (i : ℕ) (hi : i < n + 1) :
    read (join ha u v) i = joinedHeight u v i := read_in (join ha u v) ⟨i, hi⟩

@[simp] theorem read_join_zero {n a : ℕ} (ha : a ≤ n) (u : Word a) (v : Word (n - a)) :
    read (join ha u v) 0 = 0 := by simp [read_join, joinedHeight]

theorem read_join_positive {n a : ℕ} (ha : a ≤ n) (u : Word a) (v : Word (n - a))
    (i : ℕ) (hi : i < a) :
    read (join ha u v) (i + 1) = read u i + 1 := by
  have hin : i + 1 < n + 1 := by omega
  have hib : i + 1 ≤ a := by omega
  simp [read_join ha u v _ hin, joinedHeight, hib]

theorem read_join_suffix {n a : ℕ} (ha : a ≤ n) (u : Word a) (v : Word (n - a))
    (i : ℕ) (hi : i < n - a) :
    read (join ha u v) (a + 1 + i) = read v i := by
  have hin : a + 1 + i < n + 1 := by omega
  have hzero : a + 1 + i ≠ 0 := by omega
  have hbound : ¬ a + 1 + i ≤ a := by omega
  have hidx : a + 1 + i - a - 1 = i := by omega
  simp [read_join ha u v _ hin, joinedHeight, hzero, hbound, hidx]

/-- The first-return join takes two valid Catalan words to a valid word. -/
theorem join_valid {n a : ℕ} (ha : a ≤ n) {u : Word a} {v : Word (n - a)}
    (hu : IsCatalan u) (hv : IsCatalan v) : IsCatalan (join ha u v) := by
  rw [isCatalan_iff_read] at hu hv ⊢
  refine ⟨read_join_zero ha u v, ?_⟩
  intro i hi
  by_cases hlo : i < a
  · by_cases hz : i = 0
    · subst i
      rw [read_join_zero, read_join_positive ha u v 0 hlo, hu.1]
    · let j := i - 1
      have heq : j + 1 = i := by omega
      have hj : j < a := by omega
      have hj₁ : j + 1 < a := by omega
      rw [← heq, read_join_positive ha u v (j + 1) hj₁, read_join_positive ha u v j hj]
      exact Nat.add_le_add_right (hu.2 j hj₁) 1
  · by_cases heq : i = a
    · subst i
      rw [show a + 1 = a + 1 + 0 from rfl,
        read_join_suffix ha u v 0 (by omega), hv.1]
      omega
    · let j := i - a - 1
      have hj : j < n - a := by omega
      have hj₁ : j + 1 < n - a := by omega
      have h₀ : i = a + 1 + j := by omega
      have h₁ : i + 1 = a + 1 + (j + 1) := by omega
      rw [h₁, h₀, read_join_suffix ha u v (j + 1) hj₁, read_join_suffix ha u v j hj]
      exact hv.2 j hj₁

/-- The augmented positive block creates a peak at its end if the suffix
is present and the block is a singleton or ends with a strict rise. -/
def augmentedAscent {a : ℕ} (u : Word a) : Prop :=
  a = 1 ∨ 1 < a ∧ read u (a - 2) < read u (a - 1)

instance {a : ℕ} (u : Word a) : Decidable (augmentedAscent u) := by
  unfold augmentedAscent
  infer_instance

private theorem peak_shift_positive {n a : ℕ} (ha : a ≤ n) (u : Word a) (v : Word (n - a))
    (j : ℕ) (hj : j + 2 < a) :
    HasPeakAt (join ha u v) (j + 1) ↔ HasPeakAt u j := by
  rw [hasPeak_read, hasPeak_read]
  have h₀ : j < a := by omega
  have h₁ : j + 1 < a := by omega
  have h₂ : j + 2 + 1 < n + 1 := by omega
  rw [show j + 1 + 2 = j + 2 + 1 by omega,
    read_join_positive ha u v j h₀, read_join_positive ha u v (j + 1) h₁,
    read_join_positive ha u v (j + 2) hj]
  simp [h₂, hj]

private theorem peak_shift_suffix {n a : ℕ} (ha : a ≤ n) (u : Word a) (v : Word (n - a))
    (j : ℕ) (hj : j + 2 < n - a) :
    HasPeakAt (join ha u v) (a + 1 + j) ↔ HasPeakAt v j := by
  rw [hasPeak_read, hasPeak_read]
  have h₀ : j < n - a := by omega
  have h₁ : j + 1 < n - a := by omega
  have h₂ : a + 1 + (j + 2) < n + 1 := by omega
  rw [show a + 1 + j + 1 = a + 1 + (j + 1) by omega,
    show a + 1 + j + 2 = a + 1 + (j + 2) by omega,
    read_join_suffix ha u v j h₀, read_join_suffix ha u v (j + 1) h₁,
    read_join_suffix ha u v (j + 2) hj]
  simp [h₂, hj]

private theorem exists_return {n : ℕ} (w : Word (n + 1)) :
    ∃ i : ℕ, 0 < i ∧ read w i = 0 :=
  ⟨n + 1, by omega, by simp [read]⟩

/-- First positive index with height zero, or the word length if absent. -/
noncomputable def returnIndex {n : ℕ} (w : Word (n + 1)) : ℕ :=
  Nat.find (exists_return w)

theorem returnIndex_pos {n : ℕ} (w : Word (n + 1)) : 0 < returnIndex w :=
  (Nat.find_spec (exists_return w)).1

theorem read_returnIndex {n : ℕ} (w : Word (n + 1)) : read w (returnIndex w) = 0 :=
  (Nat.find_spec (exists_return w)).2

theorem returnIndex_le {n : ℕ} (w : Word (n + 1)) : returnIndex w ≤ n + 1 :=
  Nat.find_min' (exists_return w) ⟨by omega, by simp [read]⟩

theorem read_pos_before_return {n : ℕ} (w : Word (n + 1)) (i : ℕ)
    (hi₀ : 0 < i) (hi : i < returnIndex w) : 0 < read w i := by
  by_contra hp
  have hz : read w i = 0 := by omega
  have hle : returnIndex w ≤ i := Nat.find_min' (exists_return w) ⟨hi₀, hz⟩
  omega

/-- Length of the translated positive block in the first return. -/
noncomputable def blockLength {n : ℕ} (w : Word (n + 1)) : ℕ := returnIndex w - 1

theorem blockLength_le {n : ℕ} (w : Word (n + 1)) : blockLength w ≤ n := by
  have h := returnIndex_le w
  unfold blockLength
  omega

theorem blockLength_succ {n : ℕ} (w : Word (n + 1)) :
    blockLength w + 1 = returnIndex w := Nat.sub_add_cancel (returnIndex_pos w)

private theorem read_bound {n : ℕ} {w : Word n} (hw : IsCatalan w) (i : ℕ) :
    read w i ≤ i := by
  by_cases hi : i < n
  · rw [show read w i = (w ⟨i, hi⟩).val from read_in w ⟨i, hi⟩]
    exact entry_le_index (fun j => (w j).val) hw.1 hw.2 ⟨i, hi⟩
  · simp [read, hi]

/-- Slice the positive block and translate its heights down by one. -/
noncomputable def leftBlock {n : ℕ} (w : Word (n + 1)) (hw : IsCatalan w) :
    Word (blockLength w) := fun i =>
  ⟨read w (i.val + 1) - 1, by
    have hi := i.isLt
    have h := read_bound hw (i.val + 1)
    omega⟩

private theorem suffix_bound {n : ℕ} {w : Word (n + 1)} (hw : IsCatalan w)
    (i : ℕ) (hi : i < n - blockLength w) :
    read w (blockLength w + 1 + i) ≤ i := by
  have hword := (isCatalan_iff_read w).mp hw
  induction i with
  | zero => simp [blockLength_succ, read_returnIndex]
  | succ i ih =>
    have hstep := hword.2 (blockLength w + 1 + i) (by omega)
    have hprev := ih (by omega)
    change read w (blockLength w + 1 + i + 1) ≤ i + 1
    omega

/-- Slice the suffix beginning at the first later zero. -/
noncomputable def rightBlock {n : ℕ} (w : Word (n + 1)) (hw : IsCatalan w) :
    Word (n - blockLength w) := fun i =>
  ⟨read w (blockLength w + 1 + i.val),
    (suffix_bound hw i.val i.isLt).trans_lt (i.isLt.trans (Nat.lt_succ_self _))⟩

theorem read_leftBlock {n : ℕ} (w : Word (n + 1)) (hw : IsCatalan w) (i : ℕ)
    (hi : i < blockLength w) :
    read (leftBlock w hw) i = read w (i + 1) - 1 :=
  read_in (leftBlock w hw) ⟨i, hi⟩

theorem read_rightBlock {n : ℕ} (w : Word (n + 1)) (hw : IsCatalan w) (i : ℕ)
    (hi : i < n - blockLength w) :
    read (rightBlock w hw) i = read w (blockLength w + 1 + i) :=
  read_in (rightBlock w hw) ⟨i, hi⟩

theorem leftBlock_valid {n : ℕ} (w : Word (n + 1)) (hw : IsCatalan w) :
    IsCatalan (leftBlock w hw) := by
  have orig := (isCatalan_iff_read w).mp hw
  apply (isCatalan_iff_read _).mpr
  constructor
  · by_cases hn : 0 < blockLength w
    · rw [read_leftBlock w hw 0 hn]
      have hlen : 1 < n + 1 := Nat.add_lt_add_right (hn.trans_le (blockLength_le w)) 1
      have ht := orig.2 0 hlen
      rw [orig.1] at ht
      omega
    · simp [read, hn]
  · intro i hi
    rw [read_leftBlock w hw (i + 1) hi, read_leftBlock w hw i (by omega)]
    have ht := orig.2 (i + 1) (by have hh := blockLength_le w; omega)
    omega

theorem rightBlock_valid {n : ℕ} (w : Word (n + 1)) (hw : IsCatalan w) :
    IsCatalan (rightBlock w hw) := by
  have orig := (isCatalan_iff_read w).mp hw
  apply (isCatalan_iff_read _).mpr
  constructor
  · by_cases hn : 0 < n - blockLength w
    · rw [read_rightBlock w hw 0 hn]
      simpa only [Nat.add_zero, blockLength_succ] using read_returnIndex w
    · simp [read, hn]
  · intro i hi
    rw [read_rightBlock w hw (i + 1) hi, read_rightBlock w hw i (by omega)]
    exact orig.2 (blockLength w + 1 + i) (by omega)

/-- The first-return join reconstructs the original Catalan word. -/
theorem join_firstReturn {n : ℕ} (w : Word (n + 1)) (hw : IsCatalan w) :
    join (blockLength_le w) (leftBlock w hw) (rightBlock w hw) = w := by
  funext i
  apply Fin.ext
  rw [← read_in (join (blockLength_le w) (leftBlock w hw) (rightBlock w hw)) i,
      ← read_in w i]
  by_cases hz : i.val = 0
  · rw [hz, read_join_zero, ((isCatalan_iff_read w).mp hw).1]
  · by_cases hs : i.val ≤ blockLength w
    · let j := i.val - 1
      have hj : j < blockLength w := by omega
      have hEq : j + 1 = i.val := by omega
      rw [← hEq, read_join_positive _ _ _ _ hj, read_leftBlock _ _ _ hj]
      have hp := read_pos_before_return w (j + 1) (by omega)
        (by rw [← blockLength_succ w]; omega)
      omega
    · let j := i.val - blockLength w - 1
      have hj : j < n - blockLength w := by have hi := i.isLt; omega
      have hEq : blockLength w + 1 + j = i.val := by omega
      rw [← hEq, read_join_suffix _ _ _ _ hj, read_rightBlock _ _ _ hj]

/-- The first returned zero of a join occurs exactly at the block boundary. -/
theorem returnIndex_join {n a : ℕ} (ha : a ≤ n) (u : Word a) {v : Word (n - a)}
    (hv : IsCatalan v) : returnIndex (join ha u v) = a + 1 := by
  apply le_antisymm
  · apply Nat.find_min' (exists_return _)
    refine ⟨by omega, ?_⟩
    by_cases hs : a < n
    · rw [show a + 1 = a + 1 + 0 from rfl, read_join_suffix ha u v 0 (by omega)]
      exact ((isCatalan_iff_read v).mp hv).1
    · have heq : a = n := by omega
      simp [read, heq]
  · by_contra h
    have hp := returnIndex_pos (join ha u v)
    let i := returnIndex (join ha u v) - 1
    have hi : i < a := by omega
    have heq : i + 1 = returnIndex (join ha u v) := by omega
    have hz := read_returnIndex (join ha u v)
    rw [← heq, read_join_positive ha u v i hi] at hz
    omega

private theorem augmentedAscent_pos {a : ℕ} {u : Word a} (h : augmentedAscent u) : 0 < a := by
  rcases h with h | ⟨h, _⟩ <;> omega

private theorem peak_at_return {n a : ℕ} (ha : a ≤ n) (ha₀ : 0 < a)
    (u : Word a) {v : Word (n - a)} (hv : IsCatalan v) :
    HasPeakAt (join ha u v) (a - 1) ↔ a < n ∧ augmentedAscent u := by
  rw [hasPeak_read]
  by_cases hb : a < n
  · have hlen : a - 1 + 2 < n + 1 := by omega
    have hmid : read (join ha u v) (a - 1 + 1) = read u (a - 1) + 1 :=
      read_join_positive ha u v (a - 1) (by omega)
    have hright : read (join ha u v) (a - 1 + 2) = 0 := by
      rw [show a - 1 + 2 = a + 1 + 0 by omega, read_join_suffix ha u v 0 (by omega)]
      exact ((isCatalan_iff_read v).mp hv).1
    rw [hmid, hright]
    by_cases ha₁ : a = 1
    · have hleft : read (join ha u v) (a - 1) = 0 := by
        rw [show a - 1 = 0 by omega, read_join_zero]
      simp [augmentedAscent, hlen, hb, ha₁, hleft]
      omega
    · have hleft : read (join ha u v) (a - 1) = read u (a - 2) + 1 := by
        rw [show a - 1 = a - 2 + 1 by omega]
        exact read_join_positive ha u v (a - 2) (by omega)
      have ha₂ : 1 < a := by omega
      simp [augmentedAscent, hlen, hb, ha₁, ha₂, hleft]
  · have hlen : ¬ a - 1 + 2 < n + 1 := by omega
    simp [hb, hlen]

private theorem mem_peaks_iff {n : ℕ} (w : Word n) (j : ℕ) :
    j ∈ peaks w ↔ HasPeakAt w j := by
  rw [peaks, mem_filter, mem_range, hasPeak_read]
  constructor
  · exact And.right
  · intro h
    exact ⟨by have hlen := h.1; omega, h⟩

private theorem join_peaks_partition {n a : ℕ} (ha : a ≤ n) {u : Word a} {v : Word (n - a)}
    (hu : IsCatalan u) (hv : IsCatalan v) :
    peaks (join ha u v) =
      (((peaks u).image (fun j => j + 1)) ∪ ((peaks v).image (fun j => a + 1 + j))) ∪
        (if a < n ∧ augmentedAscent u then {a - 1} else ∅) := by
  ext j
  simp only [mem_union, mem_image]
  constructor
  · intro hj
    have hp := (mem_peaks_iff _ j).mp hj
    have hlen := ((hasPeak_read _ _).mp hp).1
    by_cases hright : a + 1 ≤ j
    · let i := j - a - 1
      have heq : a + 1 + i = j := by omega
      have hi : i + 2 < n - a := by omega
      rw [← heq, peak_shift_suffix ha u v i hi] at hp
      exact Or.inl (Or.inr ⟨i, (mem_peaks_iff v i).mpr hp, heq⟩)
    · by_cases haEq : j = a
      · have hfirst : read (join ha u v) (j + 1) = 0 := by
          rw [haEq, show a + 1 = a + 1 + 0 from rfl, read_join_suffix ha u v 0 (by omega)]
          exact ((isCatalan_iff_read v).mp hv).1
        have hrise := ((hasPeak_read _ _).mp hp).2.1
        rw [hfirst] at hrise
        omega
      · by_cases hboundary : j = a - 1
        · have ha₀ : 0 < a := by omega
          have hcond := (peak_at_return ha ha₀ u hv).mp (hboundary ▸ hp)
          exact Or.inr (by simp [hcond, hboundary])
        · by_cases hz : j = 0
          · have ha₂ : 1 < a := by omega
            have hfirst : read (join ha u v) (j + 1) = 1 := by
              rw [hz, read_join_positive ha u v 0 (by omega), ((isCatalan_iff_read u).mp hu).1]
            have hsecond : read (join ha u v) (j + 2) = read u 1 + 1 := by
              rw [hz, show 0 + 2 = 1 + 1 from rfl, read_join_positive ha u v 1 ha₂]
            have hdrop := ((hasPeak_read _ _).mp hp).2.2
            rw [hfirst, hsecond] at hdrop
            omega
          · let i := j - 1
            have heq : i + 1 = j := by omega
            have hi : i + 2 < a := by omega
            rw [← heq, peak_shift_positive ha u v i hi] at hp
            exact Or.inl (Or.inl ⟨i, (mem_peaks_iff u i).mpr hp, heq⟩)
  · rintro ((⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩) | h)
    · have hp := (mem_peaks_iff u i).mp hi
      have hlen := ((hasPeak_read _ _).mp hp).1
      exact (mem_peaks_iff _ _).mpr ((peak_shift_positive ha u v i hlen).mpr hp)
    · have hp := (mem_peaks_iff v i).mp hi
      have hlen := ((hasPeak_read _ _).mp hp).1
      exact (mem_peaks_iff _ _).mpr ((peak_shift_suffix ha u v i hlen).mpr hp)
    · by_cases hcond : a < n ∧ augmentedAscent u
      · have hindex : j = a - 1 := by simpa [hcond] using h
        rw [hindex]
        exact (mem_peaks_iff _ _).mpr
          ((peak_at_return ha (augmentedAscent_pos hcond.2) u hv).mpr hcond)
      · simp [hcond] at h

/-- At first return the internal peak counts add, with one extra peak exactly
when the positive block has an augmented final ascent and the suffix is nonempty. -/
theorem peaks_card_join {n a : ℕ} (ha : a ≤ n) {u : Word a} {v : Word (n - a)}
    (hu : IsCatalan u) (hv : IsCatalan v) :
    (peaks (join ha u v)).card =
      (peaks u).card + (peaks v).card + if a < n ∧ augmentedAscent u then 1 else 0 := by
  let A := (peaks u).image (fun j => j + 1)
  let B := (peaks v).image (fun j => a + 1 + j)
  have hA (j : ℕ) (hj : j ∈ A) : j + 2 ≤ a := by
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hj
    have hlen := (hasPeak_read _ _).mp ((mem_peaks_iff u i).mp hi)
    omega
  have hB (j : ℕ) (hj : j ∈ B) : a + 1 ≤ j := by
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hj
    omega
  have hdisj : Disjoint A B := disjoint_left.mpr (fun j ha' hb' => by
    have h₁ := hA j ha'
    have h₂ := hB j hb'
    omega)
  have hcardA : A.card = (peaks u).card :=
    card_image_of_injective _ (fun j k h => by change j + 1 = k + 1 at h; omega)
  have hcardB : B.card = (peaks v).card :=
    card_image_of_injective _ (fun j k h => by change a + 1 + j = a + 1 + k at h; omega)
  rw [join_peaks_partition ha hu hv]
  change ((A ∪ B) ∪ (if a < n ∧ augmentedAscent u then {a - 1} else ∅)).card = _
  by_cases hcond : a < n ∧ augmentedAscent u
  · have ha₀ := augmentedAscent_pos hcond.2
    have hdisjLast : Disjoint (A ∪ B) {a - 1} := by
      refine disjoint_left.mpr (fun j hj hlast => ?_)
      have heq : j = a - 1 := mem_singleton.mp hlast
      rcases mem_union.mp hj with hjA | hjB
      · have hh := hA j hjA
        omega
      · have hh := hB j hjB
        omega
    rw [if_pos hcond, if_pos hcond, card_union_of_disjoint hdisjLast,
      card_union_of_disjoint hdisj, hcardA, hcardB, card_singleton]
  · rw [if_neg hcond, if_neg hcond, union_empty, card_union_of_disjoint hdisj, hcardA, hcardB,
      Nat.add_zero]

private abbrev Split (n : ℕ) :=
  Σ a : Fin (n + 1), Word a.val × Word (n - a.val)

private def splits (n : ℕ) : Finset (Split n) :=
  univ.sigma (fun a : Fin (n + 1) => (words a.val) ×ˢ words (n - a.val))

private def composeSplit {n : ℕ} (s : Split n) : Word (n + 1) :=
  join (Nat.le_of_lt_succ s.1.isLt) s.2.1 s.2.2

private theorem split_valid {n : ℕ} {s : Split n} (hs : s ∈ splits n) :
    IsCatalan s.2.1 ∧ IsCatalan s.2.2 := by
  have h := (mem_sigma.mp hs).2
  have hw := mem_product.mp h
  exact ⟨(mem_filter.mp hw.1).2, (mem_filter.mp hw.2).2⟩

private theorem composeSplit_mem {n : ℕ} (s : Split n) (hs : s ∈ splits n) :
    composeSplit s ∈ words (n + 1) :=
  mem_filter.mpr ⟨mem_univ _, join_valid (Nat.le_of_lt_succ s.1.isLt)
    (split_valid hs).1 (split_valid hs).2⟩

private theorem composeSplit_injective {n : ℕ} {s t : Split n}
    (hs : s ∈ splits n) (ht : t ∈ splits n) (heq : composeSplit s = composeSplit t) :
    s = t := by
  rcases s with ⟨a, u, v⟩
  rcases t with ⟨b, u', v'⟩
  have hreturn := congrArg returnIndex heq
  change returnIndex (join (Nat.le_of_lt_succ a.isLt) u v) =
    returnIndex (join (Nat.le_of_lt_succ b.isLt) u' v') at hreturn
  rw [returnIndex_join _ _ (split_valid hs).2,
    returnIndex_join _ _ (split_valid ht).2] at hreturn
  change a.val + 1 = b.val + 1 at hreturn
  have hab : a = b := Fin.ext (by omega)
  subst b
  have hleft : u = u' := by
    funext i
    apply Fin.ext
    have hr := congrArg (fun w => read w (i.val + 1)) heq
    change read (join (Nat.le_of_lt_succ a.isLt) u v) (i.val + 1) =
      read (join (Nat.le_of_lt_succ a.isLt) u' v') (i.val + 1) at hr
    rw [read_join_positive _ _ _ _ i.isLt, read_join_positive _ _ _ _ i.isLt,
      read_in u i, read_in u' i] at hr
    omega
  have hright : v = v' := by
    funext i
    apply Fin.ext
    have hr := congrArg (fun w => read w (a.val + 1 + i.val)) heq
    change read (join (Nat.le_of_lt_succ a.isLt) u v) (a.val + 1 + i.val) =
      read (join (Nat.le_of_lt_succ a.isLt) u' v') (a.val + 1 + i.val) at hr
    rw [read_join_suffix _ _ _ _ i.isLt, read_join_suffix _ _ _ _ i.isLt,
      read_in v i, read_in v' i] at hr
    exact hr
  simp [hleft, hright]

private theorem composeSplit_surjective {n : ℕ} (w : Word (n + 1))
    (hw : w ∈ words (n + 1)) :
    ∃ s ∈ splits n, composeSplit s = w := by
  have h := (mem_filter.mp hw).2
  let a : Fin (n + 1) := ⟨blockLength w, Nat.lt_succ_of_le (blockLength_le w)⟩
  let s : Split n := ⟨a, leftBlock w h, rightBlock w h⟩
  refine ⟨s, mem_sigma.mpr ⟨mem_univ _, mem_product.mpr ⟨?_, ?_⟩⟩, ?_⟩
  · exact mem_filter.mpr ⟨mem_univ _, leftBlock_valid w h⟩
  · exact mem_filter.mpr ⟨mem_univ _, rightBlock_valid w h⟩
  · exact join_firstReturn w h

/-- The polynomial weight of augmented-ascent words. -/
noncomputable def A (n : ℕ) : ℝ[X] :=
  ∑ u ∈ (words n).filter augmentedAscent, X ^ (peaks u).card

theorem A_zero : A 0 = 0 := by
  have h : (words 0).filter augmentedAscent = ∅ := by
    ext u
    simp [augmentedAscent]
  simp [A, h]

private theorem C_zero : C 0 = 1 := (Recurrence.enumerate_X_eq_C 0).symm

private theorem C_one : C 1 = 1 := by
  rw [← Recurrence.enumerate_X_eq_C 1]
  simp [Recurrence.enumerate, Recurrence.rows, Fintype.sum_prod_type, Fintype.sum_bool,
    Fin.sum_univ_two]

private theorem augmentedAscent_iff_ascent {n : ℕ} (hn : 0 < n) (w : Word (n + 1)) :
    augmentedAscent w ↔ Recurrence.ascent w = true := by
  have h₀ : n + 1 ≠ 1 := by omega
  have h₁ : 1 < n + 1 := by omega
  have h₂ : n + 1 - 2 = n - 1 := by omega
  simp only [augmentedAscent, h₀, h₁, h₂, Nat.add_sub_cancel, false_or, true_and]
  have hPrev := read_in w ⟨n - 1, by omega⟩
  rw [hPrev, show read w n = (w (Fin.last n)).val from read_in w (Fin.last n)]
  simp [Recurrence.ascent, Recurrence.lastHeight]

private def riseLetter {n : ℕ} (w : Word (n + 1)) : Fin (n + 3) :=
  ⟨Recurrence.lastHeight w + 1, by
    have h := (w (Fin.last n)).isLt
    unfold Recurrence.lastHeight
    omega⟩

private def appendRise {n : ℕ} (w : Word (n + 1)) : Word (n + 2) :=
  Recurrence.append w (riseLetter w)

private theorem appendRise_mem {n : ℕ} (w : Word (n + 1)) (hw : w ∈ words (n + 1)) :
    appendRise w ∈ (words (n + 2)).filter augmentedAscent := by
  have hv := Recurrence.append_valid w (riseLetter w) (mem_filter.mp hw).2 (by rfl)
  refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, hv⟩, ?_⟩
  rw [augmentedAscent_iff_ascent (Nat.succ_pos _), appendRise, Recurrence.ascent_append]
  simp [riseLetter]

private theorem appendRise_injective {n : ℕ} : Function.Injective (@appendRise n) := by
  intro w v hwv
  funext i
  apply Fin.ext
  have heq := congrArg (fun z : Word (n + 2) => (z i.castSucc).val) hwv
  simpa only [appendRise, Recurrence.append_castSucc, Fin.coe_castSucc] using heq

private theorem appendRise_surjective {n : ℕ} (v : Word (n + 2))
    (hv : v ∈ (words (n + 2)).filter augmentedAscent) :
    ∃ w ∈ words (n + 1), appendRise w = v := by
  have hvalid : IsCatalan v := (mem_filter.mp (mem_filter.mp hv).1).2
  have hAsc := (augmentedAscent_iff_ascent (Nat.succ_pos n) v).mp (mem_filter.mp hv).2
  let w := Recurrence.truncate v hvalid
  let x := v (Fin.last (n + 1))
  have hApp : Recurrence.append w x = v := Recurrence.append_truncate v hvalid
  have hRise : Recurrence.lastHeight w < x.val := by
    rw [← hApp, Recurrence.ascent_append] at hAsc
    exact of_decide_eq_true hAsc
  have hBound : x.val ≤ Recurrence.lastHeight w + 1 := Recurrence.truncate_boundary v hvalid
  have hx : x = riseLetter w := by
    apply Fin.ext
    change x.val = Recurrence.lastHeight w + 1
    omega
  refine ⟨w, mem_filter.mpr ⟨mem_univ _, Recurrence.truncate_valid v hvalid⟩, ?_⟩
  change Recurrence.append w (riseLetter w) = v
  rw [← hx]
  exact hApp

/-- The augmented-ascent family is a peak-preserving final rise applied to
an arbitrary word one letter shorter, with the singleton coming from empty. -/
theorem A_succ (n : ℕ) : A (n + 1) = C n := by
  cases n with
  | zero =>
    rw [C_zero, ← C_one]
    have h : (words 1).filter augmentedAscent = words 1 := by
      ext u
      simp [augmentedAscent]
    simp [A, C, h]
  | succ n =>
    unfold A C
    symm
    refine sum_bij (fun w _ => appendRise w) appendRise_mem ?_ ?_ ?_
    · intro v hv w hw h
      exact appendRise_injective h
    · intro v hv
      obtain ⟨w, hw, heq⟩ := appendRise_surjective v hv
      exact ⟨w, hw, heq⟩
    · intro w _
      change (X : ℝ[X]) ^ (peaks w).card =
        X ^ (peaks (Recurrence.append w (riseLetter w))).card
      rw [Recurrence.peaks_card_append]
      simp [Recurrence.peakIncrement, riseLetter]

private theorem split_weighted_sum {n a : ℕ} (ha : a ≤ n) :
    (∑ p ∈ (words a) ×ˢ words (n - a), (X : ℝ[X]) ^ (peaks (join ha p.1 p.2)).card) =
      C a * C (n - a) + (X - 1) * A a * (if a < n then C (n - a) else 0) := by
  rw [sum_product]
  let bump (u : Word a) : ℝ[X] := if a < n ∧ augmentedAscent u then X else 1
  have hver (u : Word a) (hu : u ∈ words a) :
      (∑ v ∈ words (n - a), (X : ℝ[X]) ^ (peaks (join ha u v)).card) =
        X ^ (peaks u).card * bump u * C (n - a) := by
    rw [C, mul_sum]
    apply sum_congr rfl
    intro v hv
    rw [peaks_card_join ha (mem_filter.mp hu).2 (mem_filter.mp hv).2, pow_add, pow_add]
    have hFactor : (X : ℝ[X]) ^ (if a < n ∧ augmentedAscent u then 1 else 0 : ℕ) =
        bump u := by
      by_cases h : a < n ∧ augmentedAscent u <;> simp [h, bump]
    rw [hFactor]
    ac_rfl
  have hfactor :
      (∑ u ∈ words a, (X : ℝ[X]) ^ (peaks u).card * bump u) =
        C a + if a < n then (X - 1) * A a else 0 := by
    calc
      _ = ∑ u ∈ words a, ((X : ℝ[X]) ^ (peaks u).card +
          if a < n ∧ augmentedAscent u then (X - 1) * X ^ (peaks u).card else 0) := by
        apply sum_congr rfl
        intro u _
        by_cases h : a < n ∧ augmentedAscent u
        · simp only [bump, if_pos h]
          ring
        · simp [bump, h]
      _ = _ := by
        rw [sum_add_distrib]
        change C a + (_ : ℝ[X]) = _
        congr 1
        by_cases hb : a < n
        · simp only [hb, true_and, if_true]
          rw [← sum_filter, A, mul_sum]
        · simp [hb]
  calc
    _ = ∑ u ∈ words a, (X : ℝ[X]) ^ (peaks u).card * bump u * C (n - a) :=
      sum_congr rfl hver
    _ = _ := by
      rw [← sum_mul, hfactor, add_mul]
      by_cases hb : a < n <;> simp [hb]

/-- The first return gives a coefficient-level convolution before eliminating
the augmented-ascent family. -/
theorem C_succ_split (n : ℕ) :
    C (n + 1) = ∑ a ∈ range (n + 1),
      (C a * C (n - a) + (X - 1) * A a * (if a < n then C (n - a) else 0)) := by
  calc
    C (n + 1) = ∑ s ∈ splits n, (X : ℝ[X]) ^ (peaks (composeSplit s)).card := by
      unfold C
      symm
      refine sum_bij (fun s _ => composeSplit s) composeSplit_mem ?_ ?_ ?_
      · intro s hs t ht h
        exact composeSplit_injective hs ht h
      · intro w hw
        obtain ⟨s, hs, heq⟩ := composeSplit_surjective w hw
        exact ⟨s, hs, heq⟩
      · intro s _
        rfl
    _ = ∑ a : Fin (n + 1),
        (C a.val * C (n - a.val) + (X - 1) * A a.val *
          (if a.val < n then C (n - a.val) else 0)) := by
      unfold splits
      rw [sum_sigma]
      apply sum_congr rfl
      intro a _
      exact split_weighted_sum (Nat.le_of_lt_succ a.isLt)
    _ = _ := Fin.sum_univ_eq_sum_range
      (fun a : ℕ => C a * C (n - a) + (X - 1) * A a * (if a < n then C (n - a) else 0)) (n + 1)

end CatalanStrictPeaks.FirstReturn
