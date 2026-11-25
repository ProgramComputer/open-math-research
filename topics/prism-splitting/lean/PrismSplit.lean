import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Data.List.Forall2
import Mathlib.Data.List.Nodup

/-!
Exact certificate for the prism-slice split at (6,6).
The geometric Ehrhart interpretation of the bounded composition formula is
given in the accompanying mathematical argument.
-/

namespace PrismSplit

set_option maxRecDepth 6000
set_option maxHeartbeats 1200000

/-- The falling-factorial product divided by the factorial, with the usual zero convention. -/
def binom (n k : Nat) : Nat :=
  if n < k then 0
  else ((List.range k).foldl (fun acc i => acc * (n - i)) 1) /
      ((List.range k).foldl (fun acc i => acc * (i + 1)) 1)

def starsBars (effect : Int) (d : Nat) : Int :=
  if effect < 0 then 0 else Int.ofNat (binom (effect.toNat + d) d)

def alternating (j : Nat) : Int := if j % 2 = 0 then 1 else -1

/-- Inclusion–exclusion for the slice with ten unit bounds and one bound of size two. -/
def unsplitLattice (q : Nat) : Int :=
  ((List.range 11).map fun j =>
    alternating j * Int.ofNat (binom 10 j) *
      (starsBars (6 * (q : Int) - Int.ofNat (j * (q + 1))) 10 -
       starsBars (6 * (q : Int) - Int.ofNat (j * (q + 1) + 2 * q + 1)) 10)).sum

/-- Inclusion–exclusion for the ordinary sixth hypersimplex in twelve coordinates. -/
def splitLattice (q : Nat) : Int :=
  ((List.range 13).map fun j =>
    alternating j * Int.ofNat (binom 12 j) *
      starsBars (6 * (q : Int) - Int.ofNat (j * (q + 1))) 11).sum

/-- Enumerate the vectors with entrywise upper bounds and prescribed sum. -/
def boundedCompositions : List Nat → Nat → List (List Nat)
  | [], t => if t = 0 then [[]] else []
  | c :: cs, t =>
    (List.range (min c t + 1)).flatMap fun x =>
      (boundedCompositions cs (t - x)).map (List.cons x)

theorem mem_boundedCompositions {cs : List Nat} {t : Nat} {v : List Nat} :
    v ∈ boundedCompositions cs t ↔ List.Forall₂ (· ≤ ·) v cs ∧ v.sum = t := by
  induction cs generalizing t v with
  | nil =>
    cases v <;> by_cases h : t = 0 <;> simp_all [boundedCompositions, eq_comm]
  | cons c cs ih =>
    rw [boundedCompositions, List.mem_flatMap]
    constructor
    · rintro ⟨x, hx, hv⟩
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
      obtain ⟨hb, hs⟩ := ih.mp hw
      have hxt : x ≤ min c t := Nat.le_of_lt_succ (List.mem_range.mp hx)
      refine ⟨List.Forall₂.cons (hxt.trans (min_le_left _ _)) hb, ?_⟩
      rw [List.sum_cons, hs, Nat.add_sub_of_le (hxt.trans (min_le_right _ _))]
    · rintro ⟨hb, hs⟩
      cases hb with
      | cons h hb =>
        rename_i x w
        have hx : x ≤ t := by
          rw [← hs, List.sum_cons]
          exact Nat.le_add_right _ _
        refine ⟨x, List.mem_range.mpr (Nat.lt_succ_of_le (le_min h hx)), ?_⟩
        refine List.mem_map.mpr ⟨w, ih.mpr ⟨hb, ?_⟩, rfl⟩
        rw [← hs, List.sum_cons, Nat.add_sub_cancel_left]

theorem boundedCompositions_nodup (cs : List Nat) (t : Nat) :
    (boundedCompositions cs t).Nodup := by
  induction cs generalizing t with
  | nil =>
    by_cases h : t = 0 <;> simp [boundedCompositions, h]
  | cons c cs ih =>
    rw [boundedCompositions, List.nodup_flatMap]
    refine ⟨fun x _ => (ih (t - x)).map (fun _ _ h => List.cons.inj h |>.2), ?_⟩
    apply (List.nodup_range : (List.range (min c t + 1)).Nodup).imp
    intro x y hxy v hvx hvy
    obtain ⟨w, _, rfl⟩ := List.mem_map.mp hvx
    obtain ⟨u, _, hu⟩ := List.mem_map.mp hvy
    exact hxy ((List.cons.inj hu).1.symm)

def baseTable (m : Nat) : List Nat :=
  (List.range (m + 1)).map fun t => if t = 0 then 1 else 0

def extendTable (m c : Nat) (previous : List Nat) : List Nat :=
  (List.range (m + 1)).map fun t =>
    ((List.range (min c t + 1)).map fun x => previous.getD (t - x) 0).sum

/-- Dynamic programming table, keeping enough entries for all sums through m. -/
def countTable : List Nat → Nat → List Nat
  | [], m => baseTable m
  | c :: cs, m => extendTable m c (countTable cs m)

theorem countTable_correct (cs : List Nat) (m t : Nat) (ht : t ≤ m) :
    (countTable cs m).getD t 0 = (boundedCompositions cs t).length := by
  induction cs generalizing t with
  | nil =>
    simp only [countTable, baseTable, extendTable, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (Nat.lt_succ_of_le ht), Option.map_some, Option.getD_some]
    by_cases hz : t = 0 <;> simp [boundedCompositions, hz]
  | cons c cs ih =>
    simp only [countTable, baseTable, extendTable, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (Nat.lt_succ_of_le ht), Option.map_some, Option.getD_some,
      boundedCompositions, List.length_flatMap, List.length_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro x _
    exact ih (t - x) ((Nat.sub_le _ _).trans ht)

def boundedCount (cs : List Nat) (t : Nat) : Nat :=
  (countTable cs t).getD t 0

theorem boundedCount_eq_length (cs : List Nat) (t : Nat) :
    boundedCount cs t = (boundedCompositions cs t).length :=
  countTable_correct cs t t (Nat.le_refl _)

def unsplitByCompositions (q : Nat) : Int :=
  Int.ofNat (boundedCount (List.replicate 10 q ++ [2 * q]) (6 * q))

def splitByCompositions (q : Nat) : Int :=
  Int.ofNat (boundedCount (List.replicate 12 q) (6 * q))

/-- Coefficients after multiplying the count series by the Ehrhart denominator. -/
def ehrhartNumerator (d : Nat) (lattice : Nat → Int) : List Int :=
  (List.range (d + 1)).map fun k =>
    ((List.range (k + 1)).map fun j =>
      alternating j * Int.ofNat (binom (d + 1) j) * lattice (k - j)).sum

def unsplitCoefficients : List Int :=
  [1, 661, 31846, 312146, 927706, 960774, 347986, 38686, 901, 1, 0]

def splitCoefficients : List Int :=
  [1, 912, 62767, 878932, 3834832, 6169360, 3834832, 878932, 62767, 912, 1, 0]

theorem unsplitEhrhartCertificate :
    ehrhartNumerator 10 unsplitLattice = unsplitCoefficients := by decide

theorem splitEhrhartCertificate :
    ehrhartNumerator 11 splitLattice = splitCoefficients := by decide

theorem unsplitFirstCounts :
    [unsplitByCompositions 0, unsplitByCompositions 1, unsplitByCompositions 2] =
      [1, 672, 39183] := by decide

theorem splitFirstCounts :
    [splitByCompositions 0, splitByCompositions 1, splitByCompositions 2] =
      [1, 924, 73789] := by decide

def evalAsc : List Int → ℝ → ℝ
  | [], _ => 0
  | c :: cs, x => (c : ℝ) + x * evalAsc cs x

def unsplit (x : ℝ) : ℝ := evalAsc unsplitCoefficients x
def split (x : ℝ) : ℝ := evalAsc splitCoefficients x

theorem continuous_evalAsc (cs : List Int) : Continuous (evalAsc cs) := by
  induction cs with
  | nil =>
      exact continuous_const
  | cons c cs ih =>
      exact continuous_const.add (continuous_id.mul ih)

theorem unsplit_negative_at_left : unsplit (-1000) < 0 := by
  norm_num [unsplit, evalAsc, unsplitCoefficients]

theorem unsplit_positive_at_right : 0 < unsplit (-850) := by
  norm_num [unsplit, evalAsc, unsplitCoefficients]

theorem split_positive_shift (y : ℝ) (hy : 0 ≤ y) : 0 < split (-850 - y) := by
  have h : split (-850 - y) =
      2462840223865789630433882301 +
      238230301785310449829592988 * y +
      2391558152901238905506167 * y^2 +
      11120172153189576549868 * y^3 +
      30489016491580854832 * y^4 +
      53974260402703840 * y^5 +
      63838975099432 * y^6 +
      50399816668 * y^7 +
      25598467 * y^8 +
      7588 * y^9 +
      y^10 := by
    unfold split splitCoefficients
    simp only [evalAsc]
    push_cast
    ring
  rw [h]
  positivity

theorem split_has_no_left_root {x : ℝ} (hx : x ≤ -850) : split x ≠ 0 := by
  have h : 0 ≤ -850 - x := sub_nonneg.mpr hx
  have ht := split_positive_shift (-850 - x) h
  have heq : -850 - (-850 - x) = x := by ring
  rw [heq] at ht
  exact ne_of_gt ht

theorem unsplit_has_left_root : ∃ x : ℝ, x ≤ -850 ∧ unsplit x = 0 := by
  have hc : Continuous unsplit := continuous_evalAsc unsplitCoefficients
  have hle : (-1000 : ℝ) ≤ -850 := by norm_num
  have hmem : (0 : ℝ) ∈ Set.Icc (unsplit (-1000)) (unsplit (-850)) :=
    ⟨unsplit_negative_at_left.le, unsplit_positive_at_right.le⟩
  have hs := intermediate_value_Icc hle hc.continuousOn hmem
  obtain ⟨x, hx, hz⟩ := hs
  exact ⟨x, hx.2, hz⟩

/-- One more root in the higher-degree split row would require a split root to the
left of every unsplit root. This necessary condition fails. -/
theorem splitCounterexample :
    ¬ (∀ x : ℝ, unsplit x = 0 → ∃ y : ℝ, split y = 0 ∧ y ≤ x) := by
  intro h
  obtain ⟨x, hx, hroot⟩ := unsplit_has_left_root
  obtain ⟨y, hy, hyx⟩ := h x hroot
  exact split_has_no_left_root (hyx.trans hx) hy

/-- Weak alternation of roots listed from the left when the second list has one extra root. -/
def alternatingRoots : List ℝ → List ℝ → Prop
  | [], [_] => True
  | p :: ps, q :: r :: qs => q ≤ p ∧ p ≤ r ∧ alternatingRoots ps (r :: qs)
  | _, _ => False

theorem lower_root_has_predecessor {ps qs : List ℝ} (h : alternatingRoots ps qs)
    {x : ℝ} (hx : x ∈ ps) : ∃ y ∈ qs, y ≤ x := by
  induction ps generalizing qs with
  | nil =>
    simp at hx
  | cons p ps ih =>
    cases qs with
    | nil => simp [alternatingRoots] at h
    | cons q qs =>
      cases qs with
      | nil => simp [alternatingRoots] at h
      | cons r qs =>
        rcases h with ⟨hqp, _, ha⟩
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨q, List.mem_cons_self, hqp⟩
        · obtain ⟨y, hy, hle⟩ := ih ha hx
          exact ⟨y, List.mem_cons_of_mem q hy, hle⟩

/-- Complete root lists of the two computed rows cannot alternate. -/
theorem no_alternating_root_lists :
    ¬ ∃ ps qs : List ℝ,
      (∀ x : ℝ, x ∈ ps ↔ unsplit x = 0) ∧
      (∀ x : ℝ, x ∈ qs ↔ split x = 0) ∧ alternatingRoots ps qs := by
  rintro ⟨ps, qs, hp, hq, h⟩
  apply splitCounterexample
  intro x hx
  obtain ⟨y, hy, hle⟩ := lower_root_has_predecessor h ((hp x).mpr hx)
  exact ⟨y, (hq y).mp hy, hle⟩

/-- The obstruction applied directly to evaluations of the computed integer rows. -/
theorem computedRowsDoNotInterlace :
    ¬ ∃ ps qs : List ℝ,
      (∀ x : ℝ, x ∈ ps ↔ evalAsc (ehrhartNumerator 10 unsplitLattice) x = 0) ∧
      (∀ x : ℝ, x ∈ qs ↔ evalAsc (ehrhartNumerator 11 splitLattice) x = 0) ∧
      alternatingRoots ps qs := by
  rw [unsplitEhrhartCertificate, splitEhrhartCertificate]
  exact no_alternating_root_lists

#print axioms unsplitEhrhartCertificate
#print axioms splitEhrhartCertificate
#print axioms mem_boundedCompositions
#print axioms boundedCompositions_nodup
#print axioms boundedCount_eq_length
#print axioms unsplitFirstCounts
#print axioms splitFirstCounts
#print axioms splitCounterexample
#print axioms computedRowsDoNotInterlace

end PrismSplit
