import PrismDimensions
import PrismFamilyTop

/-! The infinite family in the finite-coordinate model of the prism slices. -/

namespace PrismFamily

open PrismSplit
open scoped BigOperators

def beforeFinCaps (b : Nat) : Fin (2 * b + 1) → Nat :=
  Fin.append (fun _ : Fin (2 * b) => 1) (fun _ : Fin 1 => 2)

def afterFinCaps (b : Nat) : Fin (2 * b + 2) → Nat :=
  fun _ => 1

theorem beforeFinCaps_list (b : Nat) : List.ofFn (beforeFinCaps b) = beforeCaps b := by
  unfold beforeFinCaps
  rw [List.ofFn_fin_append, List.ofFn_const, List.ofFn_const]
  rfl

theorem afterFinCaps_list (b : Nat) : List.ofFn (afterFinCaps b) = afterCaps b := by
  exact List.ofFn_const _ _

theorem familySplitBounds (b : Nat) :
    (List.ofFn (beforeFinCaps b)).getLast? = some 2 ∧
    List.ofFn (afterFinCaps b) = (List.ofFn (beforeFinCaps b)).dropLast ++ [1, 1] := by
  rw [beforeFinCaps_list, afterFinCaps_list]
  simp [beforeCaps, afterCaps, List.replicate_add]

private theorem beforeFinCaps_positive (b : Nat) : ∀ i, 0 < beforeFinCaps b i := by
  intro i
  refine Fin.addCases (motive := fun j => 0 < beforeFinCaps b j) ?_ ?_ i
  · intro j
    simp [beforeFinCaps, Fin.append_left]
  · intro j
    simp [beforeFinCaps, Fin.append_right]

private theorem beforeFinCaps_sum (b : Nat) : (∑ i, beforeFinCaps b i) = 2 * (b + 1) := by
  rw [← List.sum_ofFn, beforeFinCaps_list, beforeCaps, List.sum_append, List.sum_replicate]
  simp
  omega

private theorem afterFinCaps_sum (b : Nat) : (∑ i, afterFinCaps b i) = 2 * (b + 1) := by
  rw [← List.sum_ofFn, afterFinCaps_list, afterCaps, List.sum_replicate]
  simp
  omega

private theorem finSlice_nonempty_of_sum {n : Nat} (caps : Fin n → Nat) (total : Nat)
    (hsum : (∑ i, caps i) = 2 * total) : (realFinSlice caps total).Nonempty := by
  have hh := realSliceNonempty_of_double_sum (List.ofFn caps) total (by
    simpa only [List.sum_ofFn] using hsum)
  rw [← ofFn_image_realFinSlice] at hh
  obtain ⟨_, p, hp, _⟩ := hh
  exact ⟨p, hp⟩

theorem beforeFinNonempty (b : Nat) : (realFinSlice (beforeFinCaps b) (b + 1)).Nonempty :=
  finSlice_nonempty_of_sum _ _ (beforeFinCaps_sum b)

theorem afterFinNonempty (b : Nat) : (realFinSlice (afterFinCaps b) (b + 1)).Nonempty :=
  finSlice_nonempty_of_sum _ _ (afterFinCaps_sum b)

theorem beforeAffineDimension (b : Nat) :
    Module.finrank ℝ (affineSpan ℝ (realFinSlice (beforeFinCaps b) (b + 1))).direction = 2 * b :=
  affineDimension_realFinSlice _ _ (beforeFinCaps_positive b) (beforeFinCaps_sum b)

theorem afterAffineDimension (b : Nat) :
    Module.finrank ℝ (affineSpan ℝ (realFinSlice (afterFinCaps b) (b + 1))).direction = 2 * b + 1 :=
  affineDimension_realFinSlice _ _ (by simp [afterFinCaps]) (afterFinCaps_sum b)

theorem beforeFinSeries (b : Nat) (hb : 2 ≤ b) :
    (beforeNumerator b : PowerSeries Int) = normalizedCountSeries
      (Module.finrank ℝ (affineSpan ℝ (realFinSlice (beforeFinCaps b) (b + 1))).direction)
      (fun q => (finLatticeCount (beforeFinCaps b) (b + 1) q (beforeFinNonempty b) : Int)) := by
  rw [beforeAffineDimension]
  simpa only [finLatticeCount_eq, beforeFinCaps_list, beforeCounts] using beforeNumeratorSeries b hb

theorem afterFinSeries (b : Nat) :
    (afterNumerator b : PowerSeries Int) = normalizedCountSeries
      (Module.finrank ℝ (affineSpan ℝ (realFinSlice (afterFinCaps b) (b + 1))).direction)
      (fun q => (finLatticeCount (afterFinCaps b) (b + 1) q (afterFinNonempty b) : Int)) := by
  rw [afterAffineDimension]
  simpa only [finLatticeCount_eq, afterFinCaps_list, afterCounts] using afterNumeratorSeries b

#print axioms beforeAffineDimension
#print axioms afterAffineDimension
#print axioms beforeFinSeries
#print axioms afterFinSeries

end PrismFamily
