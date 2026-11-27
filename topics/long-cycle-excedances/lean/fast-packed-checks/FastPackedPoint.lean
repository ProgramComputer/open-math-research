import CompactRowModel
import CoarseCheck

namespace OpenMathResearch.LongCycleExcedances.IntegerSign
open TruncatedRows

def naturalPow2 (b : ℕ) : ℕ := (1 : ℕ) <<< b

theorem naturalPow2_eq (b : ℕ) : naturalPow2 b = 2^b := by
  simp [naturalPow2, Nat.shiftLeft_eq]

def pow2Shift (b : ℕ) : ℤ := naturalPow2 b

theorem pow2Shift_eq (b : ℕ) : pow2Shift b = (2 : ℤ)^b := by
  simp [pow2Shift, naturalPow2_eq, Int.natCast_pow]

/-- Decode the same word through shifts, without constructing its power of two. -/
def decodeFast (word : ℕ) : ℕ := (word % (1 <<< 48)) <<< (word >>> 48)

theorem decodeFast_eq (word : ℕ) : decodeFast word = decode 48 word := by
  simp [decodeFast, decode, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]

/-- One walk of the row computes the signed floor and unsigned ceiling Horner values. -/
def pairedHorner (p : ℤ) (bits : ℕ) : List ℤ → ℤ × ℤ
  | [] => (0, 0)
  | a :: tail =>
      let v := pairedHorner p bits tail
      (a - ((p * v.1) >>> bits), a - ((-(p * v.2)) >>> bits))

theorem pairedHorner_eq (p : ℤ) (bits : ℕ) (cs : List ℤ) :
    pairedHorner p bits cs = (roundedRatio p (2^bits) cs, upperHorner p (2^bits) cs) := by
  induction cs with
  | nil => rfl
  | cons a cs ih =>
    rw [pairedHorner, ih]
    simp only [Int.shiftRight_eq_div_pow, roundedRatio, upperHorner]

theorem firstCoeffs_decode (words : List ℕ) (w : ℕ) (hlen : w ≤ words.length) :
    firstCoeffs ((fun i => (decode 48 (words[i]?.getD 0) : ℤ))) w =
      (words.take w).map fun x => (decode 48 x : ℤ) := by
  induction w generalizing words with
  | zero => rfl
  | succ w ih =>
    cases words with
    | nil => simp at hlen
    | cons x words =>
      simp only [List.length_cons, Nat.succ_le_succ_iff] at hlen
      simp only [firstCoeffs, List.take_succ_cons, List.map_cons,
        List.getElem?_cons_zero, Option.getD_some,
        List.getElem?_cons_succ]
      exact congrArg (List.cons (decode 48 x : ℤ)) (ih words hlen)

/-- The coarse integer sign checker at a dyadic endpoint.
The supplied radius level is checked by the first tail comparison. -/
def fastCoarseCheck (n level bits : ℕ) (words : List ℕ) (p s : ℤ) : Bool :=
  let w := words.length
  let cs := words.map fun word => (decodeFast word : ℤ)
  let values := pairedHorner p bits cs
  let M := s * values.1 - 2 + ((-values.2) >>> 36)
  let U := ((w : ℤ) + 1)^n
  let V := ((w : ℤ) + 2)^n
  let D := pow2Shift bits
  decide (0 < naturalPow2 bits ∧ 0 ≤ p ∧ 2*p ≤ D ∧ (s=1 ∨ s= -1) ∧
    p * pow2Shift level ≤ D ∧ 2*V ≤ pow2Shift level * U ∧ ((2*U) >>> (level*w)) < M)

theorem fastCoarseCheck_eq (n level bits : ℕ) (words : List ℕ) (p s : ℤ) :
    fastCoarseCheck n level bits words p s =
      coarsePointCheck n words.length level ((fun i => (decode 48 (words[i]?.getD 0) : ℤ))) p
        (2^bits) s := by
  have hcs := firstCoeffs_decode words words.length le_rfl
  rw [List.take_length] at hcs
  simp only [fastCoarseCheck, coarsePointCheck, pairedHorner_eq, decodeFast_eq, hcs,
    Int.shiftRight_eq_div_pow, Int.natCast_pow, Int.cast_ofNat_Int, Prod.fst, Prod.snd,
    naturalPow2_eq, uncertainty, sub_neg_eq_add, pow2Shift_eq]
  congr 1
  simp only [Int.ediv_lt_iff_lt_mul (by positivity : 0 < (2:ℤ)^(level*words.length))]

#print axioms pairedHorner_eq
#print axioms fastCoarseCheck_eq
end OpenMathResearch.LongCycleExcedances.IntegerSign
