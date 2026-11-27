import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Cast.Order

namespace WitnessLedger

structure Dyadic where
  num : ℕ
  bits : ℕ
  deriving DecidableEq

def Dyadic.value (a : Dyadic) : ℚ := (a.num : ℚ) / (2 : ℚ)^a.bits

def dyadicLT (a b : Dyadic) : Bool :=
  decide (a.num * 2^b.bits < b.num * 2^a.bits)

theorem dyadicLT_sound {a b : Dyadic} (h : dyadicLT a b = true) :
    a.value < b.value := by
  have hi : a.num * 2^b.bits < b.num * 2^a.bits := of_decide_eq_true h
  unfold Dyadic.value
  rw [div_lt_div_iff₀ (pow_pos (by decide) _) (pow_pos (by decide) _)]
  exact_mod_cast hi

structure Gap where
  n : ℕ
  k : ℕ
  rank : ℕ
  a : Dyadic
  b : Dyadic
  deriving DecidableEq

def Gap.key (r : Gap) : ℕ × ℕ × ℕ := (r.k, r.n, r.rank)

def samePair (r s : Gap) : Bool :=
  decide (r.k = s.k ∧ r.n = s.n)

def wellFormed (r : Gap) : Bool :=
  decide (0 < r.a.num ∧ r.b.num < 2^r.b.bits) && dyadicLT r.a r.b

def ordered (r s : Gap) : Bool :=
  !samePair r s || dyadicLT r.b s.a

def check (expected : List (ℕ × ℕ × ℕ)) (rows : List Gap) : Bool :=
  decide (rows.map Gap.key = expected ∧ expected.Nodup) &&
  rows.all wellFormed &&
  (rows.zip rows.tail).all (fun (r,s) => ordered r s)

theorem wellFormed_sound {r : Gap} (h : wellFormed r = true) :
    0 < r.a.value ∧ r.a.value < r.b.value ∧ r.b.value < 1 := by
  have hh := Bool.and_eq_true_iff.mp h
  have hi : 0 < r.a.num ∧ r.b.num < 2^r.b.bits := of_decide_eq_true hh.1
  refine ⟨?_, dyadicLT_sound hh.2, ?_⟩
  · unfold Dyadic.value
    exact div_pos (by exact_mod_cast hi.1) (pow_pos (by decide) _)
  · unfold Dyadic.value
    rw [div_lt_iff₀ (pow_pos (by decide) _), one_mul]
    exact_mod_cast hi.2

theorem ordered_sound {r s : Gap} (h : ordered r s = true)
    (hk : r.k = s.k) (hn : r.n = s.n) : r.b.value < s.a.value := by
  have hl : dyadicLT r.b s.a = true := by
    simpa [ordered, samePair, hk, hn] using h
  exact dyadicLT_sound hl

theorem check_sound {expected : List (ℕ × ℕ × ℕ)} {rows : List Gap}
    (h : check expected rows = true) :
    rows.map Gap.key = expected ∧ (rows.map Gap.key).Nodup ∧
    (∀ r ∈ rows, 0 < r.a.value ∧ r.a.value < r.b.value ∧ r.b.value < 1) ∧
    (∀ r s, (r,s) ∈ rows.zip rows.tail → r.k = s.k → r.n = s.n →
      r.b.value < s.a.value) := by
  have ho := Bool.and_eq_true_iff.mp h
  have hi := Bool.and_eq_true_iff.mp ho.1
  have he : rows.map Gap.key = expected ∧ expected.Nodup := of_decide_eq_true hi.1
  refine ⟨he.1, he.1.symm ▸ he.2, ?_, ?_⟩
  · intro r hr
    exact wellFormed_sound ((List.all_eq_true.mp hi.2) r hr)
  · intro r s hrs hk hn
    exact ordered_sound ((List.all_eq_true.mp ho.2) (r,s) hrs) hk hn

#print axioms dyadicLT_sound
#print axioms check_sound

end WitnessLedger
