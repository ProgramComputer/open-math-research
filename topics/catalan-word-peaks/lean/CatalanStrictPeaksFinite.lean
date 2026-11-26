import CatalanStrictPeaksInterlacing
import CatalanStrictPeaksRecurrence

/-!
# Exact isolating intervals for strict Catalan peak polynomials

The certificate lists intervals in increasing modulus, on a common rational
grid. Endpoint signs are checked by homogeneous integer evaluation of the
coefficients computed from the strict Catalan word recurrence.
-/

namespace CatalanStrictPeaks.Finite

open Polynomial Finset OpenMathResearch.OrientedNegativeInterlace

/-- For a list of length `k`, compute `b^k` times its polynomial at `a / b`. -/
def homogeneousEval (a : ℤ) (b : ℕ) : List ℕ → ℤ
  | [] => 0
  | c :: cs => (c : ℤ) * (b : ℤ) ^ (cs.length + 1) + a * homogeneousEval a b cs

private theorem homogeneousEval_spec (a : ℤ) {b : ℕ} (hb : 0 < b) (cs : List ℕ) :
    (homogeneousEval a b cs : ℝ) = (b : ℝ) ^ cs.length *
      ∑ k ∈ range cs.length, (cs[k]?.getD 0 : ℝ) * ((a : ℝ) / (b : ℝ)) ^ k := by
  induction cs with
  | nil => simp [homogeneousEval]
  | cons c cs ih =>
    rw [homogeneousEval, Int.cast_add, Int.cast_mul, Int.cast_mul, Int.cast_pow,
      Int.cast_natCast, Int.cast_natCast, ih, List.length_cons, sum_range_succ']
    simp only [List.getElem?_cons_zero, Option.getD_some, List.getElem?_cons_succ,
      pow_succ, pow_zero, mul_one]
    have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
    simp_rw [← mul_assoc, ← sum_mul]
    field_simp
    ring

private theorem homogeneousEval_coefficients (n : ℕ) (a : ℤ) {b : ℕ} (hb : 0 < b) :
    (homogeneousEval a b (Recurrence.coefficients n) : ℝ) = (b : ℝ) ^ (rowDegree n + 1) *
      (C n).eval ((a : ℝ) / (b : ℝ)) := by
  rw [homogeneousEval_spec a hb, eval_eq_sum_range, natDegree_C,
    show (Recurrence.coefficients n).length = rowDegree n + 1 by simp [Recurrence.coefficients]]
  congr 1
  apply sum_congr rfl
  intro k hk
  have hk' := mem_range.mp hk
  have hlist : k < (Recurrence.coefficients n).length := by simpa [Recurrence.coefficients] using hk'
  rw [List.getElem?_eq_getElem hlist, Option.getD_some]
  rw [Recurrence.coefficients_get_eq_C n ⟨k, hk'⟩]

/-- Evaluate the positive and negative terms separately at `-a / b`,
with the same positive scale as `homogeneousEval`. -/
private def positiveNegative (a b : ℕ) : List ℕ → ℕ × ℕ
  | [] => (0, 0)
  | c :: cs =>
    let (pos, neg) := positiveNegative a b cs
    (c * b ^ (cs.length + 1) + a * neg, a * pos)

private theorem positiveNegative_spec (a b : ℕ) (cs : List ℕ) :
    homogeneousEval (-(a : ℤ)) b cs =
      ((positiveNegative a b cs).1 : ℤ) - ((positiveNegative a b cs).2 : ℤ) := by
  induction cs with
  | nil => simp [homogeneousEval, positiveNegative]
  | cons c cs ih =>
    rw [homogeneousEval, ih, positiveNegative]
    cases positiveNegative a b cs
    push_cast
    ring

private def sign (a b : ℕ) (coefficients : List ℕ) : Ordering :=
  let (pos, neg) := positiveNegative a b coefficients
  compare pos neg

private def opposite : Ordering → Ordering → Bool
  | .lt, .gt | .gt, .lt => true
  | _, _ => false

private theorem opposite_sound {p q : ℕ × ℕ}
    (h : opposite (compare p.1 p.2) (compare q.1 q.2) = true) :
    ((p.1 : ℤ) - (p.2 : ℤ)) * ((q.1 : ℤ) - (q.2 : ℤ)) < 0 := by
  cases hp : compare p.1 p.2 <;> cases hq : compare q.1 q.2 <;> simp [opposite, hp, hq] at h
  · have hp' := compare_lt_iff_lt.mp hp
    have hq' := compare_gt_iff_gt.mp hq
    exact mul_neg_of_neg_of_pos (sub_neg.mpr (by exact_mod_cast hp'))
      (sub_pos.mpr (by exact_mod_cast hq'))
  · have hp' := compare_gt_iff_gt.mp hp
    have hq' := compare_lt_iff_lt.mp hq
    exact mul_neg_of_pos_of_neg (sub_pos.mpr (by exact_mod_cast hp'))
      (sub_neg.mpr (by exact_mod_cast hq'))

private theorem opposite_signs {l u b : ℕ} {coefficients : List ℕ}
    (h : opposite (sign l b coefficients) (sign u b coefficients) = true) :
    homogeneousEval (-(l : ℤ)) b coefficients *
      homogeneousEval (-(u : ℤ)) b coefficients < 0 := by
  rw [positiveNegative_spec, positiveNegative_spec]
  apply opposite_sound
  cases hl : positiveNegative l b coefficients
  cases hu : positiveNegative u b coefficients
  simpa only [sign, hl, hu] using h

/-- Natural endpoint numerators on a grid with denominator `b`. -/
abbrev Boxes := Array (ℕ × ℕ)

def box (boxes : Boxes) (i : ℕ) : ℕ × ℕ := boxes[i]?.getD (0, 0)

noncomputable def boxLower (b : ℕ) (boxes : Boxes) (i : ℕ) : ℝ :=
  (box boxes i).1 / (b : ℝ)

noncomputable def boxUpper (b : ℕ) (boxes : Boxes) (i : ℕ) : ℝ :=
  (box boxes i).2 / (b : ℝ)

/-- Verify the interval widths, separation, and signs for an exact row. -/
def checkRowWithCoefficients (b n : ℕ) (coefficients : List ℕ) (boxes : Boxes) : Bool :=
  (List.range (rowDegree n)).all (fun i =>
    let l := (box boxes i).1
    let u := (box boxes i).2
    decide (l < u) && opposite (sign l b coefficients) (sign u b coefficients)) &&
  (List.range (rowDegree n - 1)).all (fun i =>
    decide ((box boxes i).2 ≤ (box boxes (i + 1)).1))

/-- Verify the isolating intervals from the executable word recurrence. -/
def checkRow (b n : ℕ) (boxes : Boxes) : Bool :=
  checkRowWithCoefficients b n (Recurrence.coefficients n) boxes

/-- Verify that the old and new isolating intervals have the oriented order. -/
def checkPair (n : ℕ) (old new : Boxes) : Bool :=
  (List.range (rowDegree n)).all (fun i => decide ((box new i).2 ≤ (box old i).1)) &&
    (List.range (min (rowDegree n) (rowDegree (n + 1) - 1))).all (fun i =>
      decide ((box old i).2 ≤ (box new (i + 1)).1))

private theorem boolAt {f : ℕ → Bool} {k : ℕ} (h : (List.range k).all f = true)
    (i : Fin k) : f i = true :=
  List.all_eq_true.mp h i (List.mem_range.mpr i.isLt)

/-- A successful row check certifies every root and isolates its modulus. -/
theorem checkRow_sound {b n : ℕ} (hb : 0 < b) {boxes : Boxes}
    (h : checkRow b n boxes = true) :
    ∃ r : Fin (rowDegree n) → ℝ, CompleteNegativeRoots (C n) r ∧
      ∀ i : Fin (rowDegree n), boxLower b boxes i < r i ∧ r i < boxUpper b boxes i := by
  have hb' : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  obtain ⟨hboxes, hsep⟩ := Bool.and_eq_true_iff.mp h
  have hbox (i : Fin (rowDegree n)) := Bool.and_eq_true_iff.mp (boolAt hboxes i)
  have hne : C n ≠ 0 := leadingCoeff_ne_zero.mp (leadingCoeff_pos n).ne'
  refine roots_of_disjoint_intervals (fun i => boxLower b boxes i) (fun i => boxUpper b boxes i)
    (natDegree_C n) hne ?_ ?_ ?_ ?_
  · intro i
    exact div_nonneg (Nat.cast_nonneg _) hb'.le
  · intro i
    have hw : (box boxes i).1 < (box boxes i).2 := of_decide_eq_true (hbox i).1
    exact div_lt_div_of_pos_right (by exact_mod_cast hw) hb'
  · intro i
    have hs := of_decide_eq_true (boolAt hsep i)
    exact div_le_div_of_nonneg_right (by exact_mod_cast hs) hb'.le
  · intro i
    let l := (box boxes i).1
    let u := (box boxes i).2
    have hs : homogeneousEval (-(l : ℤ)) b (Recurrence.coefficients n) *
        homogeneousEval (-(u : ℤ)) b (Recurrence.coefficients n) < 0 :=
      opposite_signs (hbox i).2
    have hs' : (homogeneousEval (-(l : ℤ)) b (Recurrence.coefficients n) : ℝ) *
        (homogeneousEval (-(u : ℤ)) b (Recurrence.coefficients n) : ℝ) < 0 := by
      exact_mod_cast hs
    rw [homogeneousEval_coefficients _ _ hb, homogeneousEval_coefficients _ _ hb] at hs'
    push_cast at hs'
    simp only [neg_div] at hs'
    change (C n).eval (-((l : ℝ) / b)) * (C n).eval (-((u : ℝ) / b)) < 0
    rw [show (b : ℝ) ^ (rowDegree n + 1) * (C n).eval (-((l : ℝ) / b)) *
        ((b : ℝ) ^ (rowDegree n + 1) * (C n).eval (-((u : ℝ) / b))) =
        ((b : ℝ) ^ (rowDegree n + 1)) ^ 2 *
          ((C n).eval (-((l : ℝ) / b)) * (C n).eval (-((u : ℝ) / b))) by ring] at hs'
    exact neg_of_mul_neg_right hs' (by positivity)

/-- Successful row and pair checks give strict interlacing for the original word counts. -/
theorem checkPair_sound {b n : ℕ} (hb : 0 < b) {old new : Boxes}
    (ho : checkRow b n old = true) (hn : checkRow b (n + 1) new = true)
    (hp : checkPair n old new = true) : StrictlyInterlaces n := by
  have hb' : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  obtain ⟨o, horoot, hobounds⟩ := checkRow_sound hb ho
  obtain ⟨v, hvroot, hvbounds⟩ := checkRow_sound hb hn
  obtain ⟨hleft, hright⟩ := Bool.and_eq_true_iff.mp hp
  refine ⟨o, v, horoot, hvroot, ?_, ?_⟩
  · intro i j hj
    have hs : (box new j).2 ≤ (box old i).1 := by
      rw [hj]
      exact of_decide_eq_true (boolAt hleft i)
    have hs' : boxUpper b new j ≤ boxLower b old i :=
      div_le_div_of_nonneg_right (by exact_mod_cast hs) hb'.le
    exact (hvbounds j).2.trans (hs'.trans_lt (hobounds i).1)
  · intro i j hj
    have hi : i.val < min (rowDegree n) (rowDegree (n + 1) - 1) := by
      have hi := i.isLt
      have hj' := j.isLt
      omega
    have hs : (box old i).2 ≤ (box new j).1 := by
      rw [hj]
      exact of_decide_eq_true (boolAt hright ⟨i, hi⟩)
    have hs' : boxUpper b old i ≤ boxLower b new j :=
      div_le_div_of_nonneg_right (by exact_mod_cast hs) hb'.le
    exact (hobounds i).2.trans (hs'.trans_lt (hvbounds j).1)

end CatalanStrictPeaks.Finite
