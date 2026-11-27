import CompactRowModel
import Mathlib.Data.Nat.Choose.Basic

namespace OpenMathResearch.LongCycleExcedances.PackedShard
open Finset TruncatedRows

def width : ℕ := 50

/-- A stored row is padded by zeros beyond its advertised width. -/
def readWord (row : List ℕ) (i : ℕ) : ℕ := (row[i]?).getD 0

def readCount (row : List ℕ) (i : ℕ) : ℕ := decode 48 (readWord row i)

def weightRow : List ℕ :=
  [1, 4083, 478271, 10187685, 66318474, 162512286, 162512286,
    66318474, 10187685, 478271, 4083, 1]

def weight (i : ℕ) : ℕ := readWord weightRow i

def shortSum (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => shortSum f n + f n

theorem shortSum_eq (f : ℕ → ℕ) (n : ℕ) : shortSum f n = ∑ j ∈ range n, f j := by
  induction n with
  | zero => simp [shortSum]
  | succ n ih => rw [shortSum, ih, sum_range_succ]

theorem weight_zero {j : ℕ} (hj : 12 ≤ j) : weight j = 0 := by
  unfold weight readWord
  have h : weightRow.length ≤ j := by simpa [weightRow] using hj
  rw [List.getElem?_eq_none h]
  rfl

def fastValue (n : ℕ) (prior lag : List ℕ) : ℕ → ℕ
  | 0 => readCount prior 0
  | i + 1 =>
      (i + 2) * readCount prior (i+1) + (n-(i+1)) * readCount prior i +
        Nat.fast_choose n 12 *
          shortSum (fun j => weight j * readCount lag (i-j)) (min (i+1) 12)

/-- Check the recorded shift using two powers of two. Kernel reduction
does not have to compute logarithms of the large coefficient literals. -/
def wordOK (x word : ℕ) : Bool :=
  let shift := word / 2^48
  decide (word < 2^64 ∧ x / 2^shift = word % 2^48 ∧
    (shift = 0 ∨ 2^(47+shift) ≤ x))

theorem wordOK_sound {x word : ℕ} (h : wordOK x word = true) :
    decode 48 word = chop 48 x := by
  obtain ⟨_, hq, hlow⟩ := of_decide_eq_true (show wordOK x word = true from h)
  let shift := word / 2^48
  change x / 2^shift = word % 2^48 at hq
  change shift = 0 ∨ 2^(47+shift) ≤ x at hlow
  have hquot : x / 2^shift < 2^48 :=
    hq.trans_lt (Nat.mod_lt _ (by decide))
  have hu : x < 2^(48+shift) := by
    rw [pow_add]
    exact (Nat.div_lt_iff_lt_mul (by positivity)).mp hquot
  have he : x.log2 + 1 - 48 = shift := by
    by_cases hz : x = 0
    · have hs : shift = 0 := by
        rcases hlow with h0 | hl
        · exact h0
        · have hp : 0 < 2^(47+shift) := by positivity
          omega
      simp [hz, hs]
    have habove := (Nat.log2_lt hz).mpr hu
    rcases hlow with hzero | hpos
    · omega
    · have hbelow := (Nat.le_log2 hz).mpr hpos
      omega
  change word % 2^48 * 2^shift = x / 2^(x.log2 + 1 - 48) * 2^(x.log2 + 1 - 48)
  rw [he, hq]

def rowMatches (values : ℕ → ℕ) (row : List ℕ) : Bool :=
  (List.range width).all fun i => wordOK (values i) (readWord row i)

theorem readCount_of_rowMatches {values : ℕ → ℕ} {row : List ℕ}
    (h : rowMatches values row = true) {i : ℕ} (hi : i < width) :
    readCount row i = chop 48 (values i) :=
  wordOK_sound (List.all_eq_true.mp h i (List.mem_range.mpr hi))

theorem fastValue_eq {a p r : ℕ → ℕ} {n i : ℕ} {prior lag : List ℕ}
    (hi : i < width)
    (ha : ∀ j, j < width → weight j = a j)
    (hp : ∀ j, j < width → readCount prior j = p j)
    (hr : ∀ j, j < width → readCount lag j = r j) :
    fastValue n prior lag i = positiveStep 13 n a p r i := by
  cases i with
  | zero => simpa [fastValue, positiveStep] using hp 0 hi
  | succ i =>
      have hi' : i < width := by omega
      simp only [fastValue, positiveStep, hp (i+1) hi, hp i hi', shortSum_eq]
      rw [Nat.fast_choose, ← Nat.choose_eq_descFactorial_div_factorial]
      have hsum : (∑ j ∈ range (min (i+1) 12), weight j * readCount lag (i-j)) =
          ∑ j ∈ range (i+1), a j * r (i-j) := by
        have hsub : range (min (i+1) 12) ⊆ range (i+1) := by
          intro j hj
          exact mem_range.mpr ((mem_range.mp hj).trans_le (min_le_left ..))
        calc
          _ = ∑ j ∈ range (i+1), weight j * readCount lag (i-j) := by
            apply sum_subset hsub
            intro j hj hnot
            have hlt := mem_range.mp hj
            have hout : ¬ j < min (i+1) 12 := fun h => hnot (mem_range.mpr h)
            have h12 : 12 ≤ j := by omega
            rw [weight_zero h12, zero_mul]
          _ = _ := by
            apply sum_congr rfl
            intro j hj
            have hlt := mem_range.mp hj
            rw [ha j (by omega), hr (i-j) (by omega)]
      rw [hsum]

/-- Small ground Boolean certificates identify every packed word with the
verified rounded recurrence. The induction needs no computation of that recurrence. -/
theorem packedTable_sound (table : ℕ → List ℕ) (a : ℕ → ℕ) (limit : ℕ)
    (ha : ∀ j, j < width → weight j = a j)
    (hshort : ∀ n, n < 13 → table n = [])
    (hseed : rowMatches weight (table 13) = true)
    (hstep : ∀ n, 13 ≤ n → n < limit →
      rowMatches (fastValue n (table n) (table (n+1-13))) (table (n+1)) = true) :
    ∀ n, n ≤ limit → ∀ i, i < width →
      readCount (table n) i = lowerRows 48 13 (by decide) a n i := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hn i hi
      by_cases hshorter : n < 13
      · rw [hshort n hshorter, lowerRows_short (by decide) hshorter]
        simp [readCount, readWord, decode]
      by_cases hcutoff : n = 13
      · subst n
        rw [readCount_of_rowMatches hseed hi, lowerRows_seed (by decide), ha _ hi]
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
      rw [readCount_of_rowMatches (hstep m (by omega) (by omega)) hi,
        lowerRows_succ (by decide) (by omega),
        fastValue_eq hi ha (ih m (by omega) (by omega)) (ih (m+1-13) (by omega) (by omega))]

#print axioms wordOK_sound
#print axioms fastValue_eq
#print axioms packedTable_sound
end OpenMathResearch.LongCycleExcedances.PackedShard
