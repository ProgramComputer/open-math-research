import CatalanStrictPeaks
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# A transfer recurrence for strict Catalan peak polynomials

The state remembers the last height and whether the preceding step ascended.
Appending a smaller height after an ascent creates precisely one strict peak.
-/

namespace CatalanStrictPeaks.Recurrence

open Polynomial Finset
open scoped BigOperators

/-- Last height of a nonempty word. -/
def lastHeight {n : ℕ} (w : Word (n + 1)) : ℕ :=
  (w (Fin.last n)).val

/-- Whether the final step ascended. The length-one state has value false. -/
def ascent {n : ℕ} (w : Word (n + 1)) : Bool :=
  decide ((w ⟨n - 1, by omega⟩).val < lastHeight w)

/-- Append one bounded letter, expanding the alphabet of the old word by one. -/
def append {n : ℕ} (w : Word (n + 1)) (x : Fin (n + 3)) : Word (n + 2) :=
  fun i => if h : i.val < n + 1 then (w ⟨i.val, h⟩).castSucc else x

@[simp] theorem append_castSucc {n : ℕ} (w : Word (n + 1)) (x : Fin (n + 3))
    (i : Fin (n + 1)) : append w x i.castSucc = (w i).castSucc := by
  simp [append, i.isLt]

@[simp] theorem append_last {n : ℕ} (w : Word (n + 1)) (x : Fin (n + 3)) :
    append w x (Fin.last (n + 1)) = x := by simp [append]

@[simp] theorem lastHeight_append {n : ℕ} (w : Word (n + 1)) (x : Fin (n + 3)) :
    lastHeight (append w x) = x.val := by simp [lastHeight]

@[simp] theorem ascent_append {n : ℕ} (w : Word (n + 1)) (x : Fin (n + 3)) :
    ascent (append w x) = decide (lastHeight w < x.val) := by
  unfold ascent
  change decide ((append w x ⟨(n + 1) - 1, _⟩).val < lastHeight (append w x)) = _
  have hi : (⟨(n + 1) - 1, by omega⟩ : Fin (n + 2)) = (Fin.last n).castSucc :=
    Fin.ext (by simp)
  rw [hi, append_castSucc, lastHeight_append]
  rfl

/-- The old word obtained by deleting the last entry of a valid new word. -/
def truncate {n : ℕ} (w : Word (n + 2)) (hw : IsCatalan w) : Word (n + 1) :=
  fun i => ⟨(w i.castSucc).val, by
    have hi := entry_le_index (fun j => (w j).val) hw.1 hw.2 i.castSucc
    exact hi.trans_lt (i.isLt.trans (Nat.lt_succ_self (n + 1)))⟩

theorem truncate_valid {n : ℕ} (w : Word (n + 2)) (hw : IsCatalan w) :
    IsCatalan (truncate w hw) := by
  constructor
  · intro i hi
    exact hw.1 i.castSucc hi
  · intro i j hij
    exact hw.2 i.castSucc j.castSucc hij

theorem truncate_boundary {n : ℕ} (w : Word (n + 2)) (hw : IsCatalan w) :
    (w (Fin.last (n + 1))).val ≤ lastHeight (truncate w hw) + 1 :=
  hw.2 (Fin.last n).castSucc (Fin.last (n + 1)) rfl

theorem append_truncate {n : ℕ} (w : Word (n + 2)) (hw : IsCatalan w) :
    append (truncate w hw) (w (Fin.last (n + 1))) = w := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · exact append_last _ _
  · rw [append_castSucc]
    exact Fin.ext rfl

theorem append_valid {n : ℕ} (w : Word (n + 1)) (x : Fin (n + 3))
    (hw : IsCatalan w) (hx : x.val ≤ lastHeight w + 1) :
    IsCatalan (append w x) := by
  constructor
  · intro i hi
    have h : i.val < n + 1 := by omega
    simpa only [append, dif_pos h, Fin.coe_castSucc] using hw.1 ⟨i.val, h⟩ hi
  · intro i j hij
    by_cases hj : j.val < n + 1
    · have hi : i.val < n + 1 := by omega
      simpa only [append, dif_pos hi, dif_pos hj, Fin.coe_castSucc] using
        hw.2 ⟨i.val, hi⟩ ⟨j.val, hj⟩ hij
    · have hj' : j = Fin.last (n + 1) := Fin.ext (by
        have hJ := j.isLt
        change j.val = n + 1
        omega)
      have hi' : i = (Fin.last n).castSucc := Fin.ext (by
        have hJ := j.isLt
        change i.val = n
        omega)
      simpa only [hj', hi', append_castSucc, append_last, Fin.coe_castSucc, lastHeight] using hx

/-- Appending after an ascent adds a peak exactly when the new height is smaller. -/
def peakIncrement (up : Bool) (h x : ℕ) : ℕ :=
  if up = true ∧ x < h then 1 else 0

private theorem peak_iff {N : ℕ} (w : Word N) (j : ℕ) (hj : j + 2 < N) :
    HasPeakAt w j ↔
      (w ⟨j, by omega⟩).val < (w ⟨j + 1, by omega⟩).val ∧
      (w ⟨j + 2, hj⟩).val < (w ⟨j + 1, by omega⟩).val := by
  have h₀ : j < N := by omega
  have h₁ : j + 1 < N := by omega
  change (j + 2 < N ∧
      (if h : j < N then (w ⟨j, h⟩).val else 0) <
        (if h : j + 1 < N then (w ⟨j + 1, h⟩).val else 0) ∧
      (if h : j + 2 < N then (w ⟨j + 2, h⟩).val else 0) <
        (if h : j + 1 < N then (w ⟨j + 1, h⟩).val else 0)) ↔ _
  simp [hj, h₀, h₁]

private theorem peak_append_old {n : ℕ} (w : Word (n + 1)) (x : Fin (n + 3))
    (j : ℕ) (hj : j + 2 < n + 1) :
    HasPeakAt (append w x) j ↔ HasPeakAt w j := by
  rw [peak_iff _ j (by omega), peak_iff _ j hj]
  have h₀ : j < n + 1 := by omega
  have h₁ : j + 1 < n + 1 := by omega
  simp [append, h₀, h₁, hj]

private theorem peak_append_last {n : ℕ} (hn : 0 < n) (w : Word (n + 1))
    (x : Fin (n + 3)) :
    HasPeakAt (append w x) (n - 1) ↔ ascent w = true ∧ x.val < lastHeight w := by
  rw [peak_iff _ (n - 1) (by omega)]
  have h₁ : (⟨n - 1, by omega⟩ : Fin (n + 2)) =
      (⟨n - 1, by omega⟩ : Fin (n + 1)).castSucc := Fin.ext rfl
  have h₂ : (⟨n - 1 + 1, by omega⟩ : Fin (n + 2)) = (Fin.last n).castSucc :=
    Fin.ext (by change n - 1 + 1 = n; omega)
  have h₃ : (⟨n - 1 + 2, by omega⟩ : Fin (n + 2)) = Fin.last (n + 1) :=
    Fin.ext (by change n - 1 + 2 = n + 1; omega)
  rw [h₁, h₂, h₃, append_castSucc, append_castSucc, append_last]
  simp [ascent, lastHeight]

/-- Exact local update of the peak count for every extension. -/
theorem peaks_card_append {n : ℕ} (w : Word (n + 1)) (x : Fin (n + 3)) :
    (peaks (append w x)).card = (peaks w).card + peakIncrement (ascent w) (lastHeight w) x.val := by
  by_cases hn : 0 < n
  · have hRange : n + 2 - 2 = (n + 1 - 2) + 1 := by omega
    have hf : ((range (n + 1 - 2)).filter (HasPeakAt (append w x))) = peaks w := by
      refine filter_congr ?_
      intro j hj
      apply peak_append_old
      have h := mem_range.mp hj
      omega
    have hlast : n + 1 - 2 = n - 1 := by omega
    unfold peaks at ⊢
    rw [hRange, range_succ, filter_insert, hf, hlast]
    by_cases hb : ascent w = true ∧ x.val < lastHeight w
    · have hl := (peak_append_last hn w x).2 hb
      have hnot : n - 1 ∉ peaks w := by
        intro h
        have h' := mem_range.mp (mem_filter.mp h).1
        omega
      change (if HasPeakAt (append w x) (n - 1) then insert (n - 1) (peaks w) else peaks w).card =
        (peaks w).card + peakIncrement (ascent w) (lastHeight w) x.val
      rw [if_pos hl, card_insert_of_not_mem hnot]
      simp [peakIncrement, hb]
    · have hl : ¬ HasPeakAt (append w x) (n - 1) := fun h => hb ((peak_append_last hn w x).1 h)
      simp [hl, peakIncrement, hb, peaks]
  · have hz : n = 0 := by omega
    subst n
    have hw₀ : (peaks w).card = 0 := Nat.eq_zero_of_le_zero (peaks_card_le w)
    have happ₀ : (peaks (append w x)).card = 0 := Nat.eq_zero_of_le_zero (peaks_card_le (append w x))
    have hAscent : ascent w = false := by
      simp [ascent, lastHeight, show (⟨0 - 1, by omega⟩ : Fin (0 + 1)) = Fin.last 0 from Fin.ext rfl]
    simp [hw₀, happ₀, peakIncrement, hAscent]

section Transfer

variable {R : Type*} [Semiring R]

/-- State space for words of length n+1. -/
abbrev State (n : ℕ) := Fin (n + 2) × Bool

/-- Height and preceding ascent of a word. -/
def stateOf {n : ℕ} (w : Word (n + 1)) : State n :=
  (w (Fin.last n), ascent w)

/-- The new height is permitted and the ascent flag records the actual step. -/
def canPush {n : ℕ} (s : State n) (t : State (n + 1)) : Prop :=
  t.1.val ≤ s.1.val + 1 ∧ decide (s.1.val < t.1.val) = t.2

instance {n : ℕ} (s : State n) (t : State (n + 1)) : Decidable (canPush s t) := by
  unfold canPush
  infer_instance

/-- The contribution of one old state to a new state. -/
def transitionWeight {n : ℕ} (q : R) (s : State n) (t : State (n + 1)) : R :=
  if canPush s t then q ^ peakIncrement s.2 s.1.val t.1.val else 0

/-- One transfer step, using only the preceding state's weighted counts. -/
def step {n : ℕ} (q : R) (prior : State n → R) (t : State (n + 1)) : R :=
  ∑ s : State n, prior s * transitionWeight q s t

/-- The weighted sum over actual Catalan words having a specified state. -/
def byState {n : ℕ} (q : R) (s : State n) : R :=
  ∑ w ∈ (words (n + 1)).filter (fun w => stateOf w = s), q ^ (peaks w).card

private theorem append_injective {n : ℕ} (x : Fin (n + 3)) :
    Function.Injective (fun w : Word (n + 1) => append w x) := by
  intro v w h
  funext i
  have heq : (v i).castSucc = (w i).castSucc := by
    simpa only [append_castSucc] using congrFun h i.castSucc
  exact Fin.ext (congrArg (fun a : Fin (n + 3) => a.val) heq)

private theorem byState_append_sum {n : ℕ} (q : R) (t : State (n + 1)) :
    byState q t =
      ∑ w ∈ (words (n + 1)).filter (fun w => canPush (stateOf w) t),
        q ^ (peaks w).card * q ^ peakIncrement (ascent w) (lastHeight w) t.1.val := by
  unfold byState
  symm
  refine sum_bij (fun w _ => append w t.1) ?_ ?_ ?_ ?_
  · intro w hw
    obtain ⟨hword, hpush⟩ := mem_filter.mp hw
    have hv : IsCatalan w := (mem_filter.mp hword).2
    have hwApp := append_valid w t.1 hv hpush.1
    refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, hwApp⟩, ?_⟩
    apply Prod.ext
    · exact append_last w t.1
    · exact (ascent_append w t.1).trans hpush.2
  · intro v hv w hw h
    exact append_injective t.1 h
  · intro v hv
    obtain ⟨hword, hs⟩ := mem_filter.mp hv
    have hvCat : IsCatalan v := (mem_filter.mp hword).2
    let w := truncate v hvCat
    have hx : v (Fin.last (n + 1)) = t.1 := congrArg Prod.fst hs
    have happ : append w t.1 = v := hx ▸ append_truncate v hvCat
    have hpush : canPush (stateOf w) t := by
      constructor
      · exact hx ▸ truncate_boundary v hvCat
      · exact (ascent_append w t.1).symm.trans
          (happ ▸ (congrArg Prod.snd hs : ascent v = t.2))
    exact ⟨w, mem_filter.mpr
      ⟨mem_filter.mpr ⟨mem_univ _, truncate_valid v hvCat⟩, hpush⟩, happ⟩
  · intro w _
    rw [peaks_card_append, pow_add]

private theorem sum_state_fibers {n : ℕ} (q : R) (f : State n → R) :
    (∑ s : State n, byState q s * f s) =
      ∑ w ∈ words (n + 1), q ^ (peaks w).card * f (stateOf w) := by
  rw [← sum_fiberwise (words (n + 1)) stateOf]
  apply sum_congr rfl
  intro s _
  rw [byState, sum_mul]
  apply sum_congr rfl
  intro w hw
  rw [(mem_filter.mp hw).2]

/-- The transfer reproduces the word enumeration in every state. -/
theorem byState_step {n : ℕ} (q : R) (t : State (n + 1)) :
    byState q t = step q (byState q) t := by
  rw [byState_append_sum, step, sum_state_fibers, sum_filter]
  apply sum_congr rfl
  intro w _
  by_cases h : canPush (stateOf w) t
  · simp [transitionWeight, h, stateOf, lastHeight]
  · simp [transitionWeight, h]

/-- Store the false and true ascent states at each height. -/
abbrev Table (R : Type*) (n : ℕ) := Vector (R × R) (n + 2)

/-- Look up a count in the materialized table. -/
def tableGet {n : ℕ} (table : Table R n) (s : State n) : R :=
  let pair := table[s.1.val]
  if s.2 then pair.2 else pair.1

/-- Materialize a table once, before advancing to the subsequent length. -/
def pack {n : ℕ} (f : State n → R) : Table R n :=
  Vector.ofFn (fun h => (f (h, false), f (h, true)))

omit [Semiring R] in
@[simp] theorem tableGet_pack {n : ℕ} (f : State n → R) (s : State n) :
    tableGet (pack f) s = f s := by
  rcases s with ⟨h, b⟩
  cases b <;> simp [tableGet, pack]

/-- Materialized state rows for lengths n+1, starting at the word 0. -/
def rows (q : R) : (n : ℕ) → Table R n
  | 0 => pack (fun s => if s = (0, false) then 1 else 0)
  | n + 1 =>
      let prior := rows q n
      pack (step q (tableGet prior))

private theorem byState_zero (q : R) (s : State 0) :
    byState q s = if s = (0, false) then 1 else 0 := by
  let w₀ : Word 1 := fun _ => 0
  have hwords : words 1 = {w₀} := by
    ext w
    simp only [words, mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · intro hw
      funext i
      apply Fin.ext
      have hi : i.val = 0 := by have h := i.isLt; omega
      exact hw.1 i hi
    · rintro rfl
      simp [w₀, IsCatalan]
  have hstate : stateOf w₀ = (0, false) := by
    simp [stateOf, ascent, lastHeight, w₀]
  have hp : (peaks w₀).card = 0 := Nat.eq_zero_of_le_zero (peaks_card_le w₀)
  by_cases hs : s = (0, false)
  · simp [byState, hwords, filter_singleton, hstate, hp, hs]
  · have hne : (0, false) ≠ s := Ne.symm hs
    simp [byState, hwords, filter_singleton, hstate, hp, hs, hne]

/-- The computed table equals the word enumeration state by state. -/
theorem rows_get_eq_byState (q : R) (n : ℕ) (s : State n) :
    tableGet (rows q n) s = byState q s := by
  induction n with
  | zero => simpa only [rows, tableGet_pack] using (byState_zero q s).symm
  | succ n ih =>
    rw [rows, tableGet_pack, byState_step]
    unfold step
    apply sum_congr rfl
    intro u _
    rw [ih u]

/-- Aggregate the states at a given word length. The empty word weighs one. -/
def enumerate (q : R) : ℕ → R
  | 0 => 1
  | n + 1 => ∑ s : State n, tableGet (rows q n) s

/-- The transfer computes the weight sum for all lengths and semirings. -/
theorem enumerate_eq_sum_words (q : R) (n : ℕ) :
    enumerate q n = ∑ w ∈ words n, q ^ (peaks w).card := by
  cases n with
  | zero =>
    let w₀ : Word 0 := fun i => Fin.elim0 i
    have hwords : words 0 = {w₀} := by
      ext w
      simp only [words, mem_filter, mem_univ, true_and, mem_singleton]
      constructor
      · intro _
        funext i
        exact Fin.elim0 i
      · intro _
        exact ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
    have hp : (peaks w₀).card = 0 := Nat.eq_zero_of_le_zero (peaks_card_le w₀)
    simp [enumerate, hwords, hp]
  | succ n =>
    simp only [enumerate, rows_get_eq_byState]
    simpa only [mul_one] using sum_state_fibers q (fun _ : State n => 1)

end Transfer

/-- Specializing the transfer to the real polynomial variable recovers the actual row. -/
theorem enumerate_X_eq_C (n : ℕ) : enumerate (X : ℝ[X]) n = C n :=
  enumerate_eq_sum_words X n

/-- The natural number counted by an original coefficient. -/
def coefficientCount (n k : ℕ) : ℕ :=
  ((words n).filter (fun w => (peaks w).card = k)).card

/-- A base larger than every coefficient, from the size of the ambient alphabet. -/
def encodingBase (n : ℕ) : ℕ := (n + 1) ^ n + 1

private theorem coefficientCount_lt_base (n k : ℕ) :
    coefficientCount n k < encodingBase n := by
  have h := card_le_univ ((words n).filter (fun w => (peaks w).card = k))
  simpa only [encodingBase, coefficientCount, Fintype.card_fun, Fintype.card_fin,
    Nat.lt_succ_iff] using h

private theorem enumerate_eq_sum_coefficients (q n : ℕ) :
    enumerate q n =
      ∑ k ∈ range (rowDegree n + 1), coefficientCount n k * q ^ k := by
  rw [enumerate_eq_sum_words]
  have hmap : ∀ w ∈ words n, (peaks w).card ∈ range (rowDegree n + 1) := by
    intro w _
    exact mem_range.mpr (Nat.lt_succ_of_le (peaks_card_le w))
  rw [← sum_fiberwise_of_maps_to' hmap (fun k => q ^ k)]
  simp only [sum_const, nsmul_eq_mul, Nat.cast_id, coefficientCount]

private theorem recover_digit {b : ℕ} (hb : 0 < b) (m : ℕ) (a : ℕ → ℕ)
    (ha : ∀ i < m, a i < b) (k : ℕ) (hk : k < m) :
    (∑ i ∈ range m, a i * b ^ i) / b ^ k % b = a k := by
  induction m generalizing a k with
  | zero => omega
  | succ m ih =>
    have hsum : (∑ i ∈ range (m + 1), a i * b ^ i) =
        a 0 + b * ∑ i ∈ range m, a (i + 1) * b ^ i := by
      rw [sum_range_succ', mul_sum]
      simp only [pow_zero, mul_one]
      rw [add_comm]
      congr 1
      apply sum_congr rfl
      intro i _
      rw [pow_succ]
      ac_rfl
    cases k with
    | zero =>
      rw [hsum, pow_zero, Nat.div_one, Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt (ha 0 (by omega))
    | succ k =>
      rw [hsum, pow_succ', ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ hb,
        Nat.div_eq_of_lt (ha 0 (by omega)), zero_add]
      exact ih (fun i => a (i + 1)) (fun i hi => ha (i + 1) (by omega)) k (by omega)

/-- Compute all coefficients by one natural-valued run of the state recurrence.
The digits are listed in increasing power order. -/
def coefficients (n : ℕ) : List ℕ :=
  let b := encodingBase n
  let value := enumerate b n
  List.ofFn (fun k : Fin (rowDegree n + 1) => value / b ^ k.val % b)

/-- The executable coefficients agree with the real strict-peak polynomial. -/
theorem coefficients_get_eq_C (n : ℕ) (k : Fin (rowDegree n + 1)) :
    ((coefficients n)[k.val]'(by simp [coefficients, k.isLt]) : ℝ) = (C n).coeff k.val := by
  rw [coeff_C]
  have hdigit : enumerate (encodingBase n) n / encodingBase n ^ k.val % encodingBase n =
      coefficientCount n k.val := by
    rw [enumerate_eq_sum_coefficients]
    exact recover_digit (by simp [encodingBase]) (rowDegree n + 1) (coefficientCount n)
      (fun i _ => coefficientCount_lt_base n i) k.val k.isLt
  simpa only [coefficients, List.getElem_ofFn] using congrArg (fun a : ℕ => (a : ℝ)) hdigit

/-- A base exceeding the word count recovers all coefficients from the same
evaluation, so it can be shared across a whole prefix. -/
theorem digits_eq_coefficients (b n : ℕ) (hb : (words n).card < b) :
    (List.ofFn fun k : Fin (rowDegree n + 1) => enumerate b n / b ^ k.val % b) =
      coefficients n := by
  have ha (k : ℕ) : coefficientCount n k < b := (card_filter_le _ _).trans_lt hb
  have hb' : 0 < b := Nat.zero_lt_of_lt hb
  simp only [coefficients, List.ofFn_inj]
  funext k
  rw [enumerate_eq_sum_coefficients b n, enumerate_eq_sum_coefficients (encodingBase n) n,
    recover_digit hb' (rowDegree n + 1) (coefficientCount n) (fun i _ => ha i) k.val k.isLt,
    recover_digit (by simp [encodingBase]) (rowDegree n + 1) (coefficientCount n)
      (fun i _ => coefficientCount_lt_base n i) k.val k.isLt]

end CatalanStrictPeaks.Recurrence
