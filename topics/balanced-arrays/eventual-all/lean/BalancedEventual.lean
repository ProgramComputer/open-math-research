import BalancedNoFullRowCounting
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.ModEq

namespace BalancedEventual

open Finset Polynomial

abbrev BinaryArray := BalancedNoFullRowCounting.BinaryArray

/-- Interpret a cell as zero or one. -/
def bit (value : Bool) : ℕ := if value then 1 else 0

def rowSum {n d : ℕ} (A : BinaryArray n d) (i : Fin n) : ℕ :=
  ∑ j, bit (A i j)

def colSum {n d : ℕ} (A : BinaryArray n d) (j : Fin d) : ℕ :=
  ∑ i, bit (A i j)

def IsBalanced {n d : ℕ} (A : BinaryArray n d) (r k : ℕ) : Prop :=
  (∀ j, colSum A j = k) ∧ (∀ i, rowSum A i ≤ r)

instance {n d : ℕ} (A : BinaryArray n d) (r k : ℕ) : Decidable (IsBalanced A r k) :=
  inferInstanceAs (Decidable ((∀ j, colSum A j = k) ∧ (∀ i, rowSum A i ≤ r)))

def arrays (n d r k : ℕ) : Finset (BinaryArray n d) :=
  univ.filter (fun A => IsBalanced A r k)

def arrayCount (n d r k : ℕ) : ℕ := (arrays n d r k).card

/-- Sum over all potentially nonzero powers. Rank and dimension constraints
are supplied by the statements below. -/
noncomputable def arrayPolynomial (n d r : ℕ) : ℂ[X] :=
  ∑ k ∈ range (n + 1), C (arrayCount n d r k : ℂ) * X ^ k

/-- The real-rootedness statement in Per Alexandersson's SymCat entry. -/
def OriginalClaim : Prop :=
  ∀ n d r : ℕ, 1 ≤ r → r ≤ d →
    ∀ z : ℂ, (arrayPolynomial n d r).IsRoot z → z.im = 0

/-- Exactly `m` complex roots, all negative real and simple. The derivative
condition expresses simplicity, including independently of the root enumeration. -/
def HasSimpleNegativeRoots (p : ℂ[X]) (m : ℕ) : Prop :=
  ∃ roots : Fin m → ℂ, Function.Injective roots ∧
    (∀ i, (roots i).im = 0 ∧ (roots i).re < 0 ∧ p.derivative.eval (roots i) ≠ 0) ∧
    (∀ z, p.IsRoot z ↔ ∃ i, roots i = z)

/-- The reviewed eventual theorem, with one row threshold for all ranks
and all dimensions at least two, and the dimension-one identity. -/
def EventualClaim : Prop :=
  (∃ N : ℕ, ∀ n d r : ℕ, N ≤ n → 2 ≤ d → 1 ≤ r → r ≤ d →
    HasSimpleNegativeRoots (arrayPolynomial n d r) (n * r / d)) ∧
  (∀ n : ℕ, arrayPolynomial n 1 1 = (1 + X) ^ n)

theorem mul_le_row_cap {n d r k : ℕ} {A : BinaryArray n d}
    (h : IsBalanced A r k) : k * d ≤ n * r := by
  calc
    k * d = ∑ j : Fin d, colSum A j := by
      simp [h.1, Nat.mul_comm]
    _ = ∑ i : Fin n, rowSum A i := by
      exact Finset.sum_comm
    _ ≤ ∑ i : Fin n, r := Finset.sum_le_sum (fun i _ => h.2 i)
    _ = n * r := by simp

theorem arrayCount_eq_zero_of_degree_lt {n d r k : ℕ}
    (hd : 0 < d) (hk : n * r / d < k) :
    arrayCount n d r k = 0 := by
  have hempty : arrays n d r k = ∅ := by
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro A hA
    have hcap := mul_le_row_cap (Finset.mem_filter.mp hA).2
    exact (not_le_of_gt hk) ((Nat.le_div_iff_mul_le hd).mpr hcap)
  simp [arrayCount, hempty]

def support {ι : Type*} [Fintype ι] (f : ι → Bool) : Finset ι :=
  univ.filter (fun i => f i = true)

theorem sum_bit_eq_card_support {ι : Type*} [Fintype ι] (f : ι → Bool) :
    ∑ i, bit (f i) = (support f).card :=
  Finset.sum_boole (fun i => f i = true) univ

theorem arrays_corank_one (n d k : ℕ) :
    arrays n d (d - 1) k = BalancedNoFullRowCounting.arrays n d k := by
  classical
  ext A
  simp only [arrays, BalancedNoFullRowCounting.arrays, IsBalanced, Finset.mem_filter,
    Finset.mem_univ, true_and, rowSum, colSum, sum_bit_eq_card_support, support]

/-- In column `j`, use the next `k` positions in the cyclic list of rows. -/
def cyclicArray (n d k : ℕ) : BinaryArray n d :=
  fun i j => decide (∃ l : Fin k, (j.val * k + l.val) % n = i.val)

theorem cyclicArray_isBalanced {n d r k : ℕ} (hn : 0 < n)
    (hkn : k ≤ n) (hcap : d * k ≤ n * r) :
    IsBalanced (cyclicArray n d k) r k := by
  classical
  constructor
  · intro j
    let index (l : Fin k) : Fin n :=
      ⟨(j.val * k + l.val) % n, Nat.mod_lt _ hn⟩
    have hinj : Function.Injective index := by
      intro l l' h
      have hmod : j.val * k + l.val ≡ j.val * k + l'.val [MOD n] :=
        congrArg Fin.val h
      have hsmall := Nat.ModEq.add_left_cancel' (j.val * k) hmod
      apply Fin.ext
      simpa [Nat.ModEq, Nat.mod_eq_of_lt (l.isLt.trans_le hkn),
        Nat.mod_eq_of_lt (l'.isLt.trans_le hkn)] using hsmall
    have hs : support (fun i => cyclicArray n d k i j) = univ.image index := by
      ext i
      simp [support, cyclicArray, index, Fin.ext_iff]
    rw [colSum, sum_bit_eq_card_support, hs, Finset.card_image_of_injective _ hinj]
    simp
  · intro i
    let valid (j : Fin d) := ∃ l : Fin k, (j.val * k + l.val) % n = i.val
    let position (j : Fin d) : ℕ :=
      if h : valid j then j.val * k + (Classical.choose h).val else 0
    have hposition (j : Fin d) (h : valid j) :
        position j = j.val * k + (Classical.choose h).val := dif_pos h
    have hvalid (j : Fin d) (hj : j ∈ support (cyclicArray n d k i)) : valid j := by
      simpa [support, cyclicArray, valid] using hj
    rw [rowSum, sum_bit_eq_card_support]
    calc
      _ ≤ ((range r) : Finset ℕ).card := by
        apply Finset.card_le_card_of_injOn (fun j => position j / n)
        · intro j hj
          have h := hvalid j hj
          have hl := (Classical.choose h).isLt
          apply Finset.mem_range.mpr
          apply (Nat.div_lt_iff_lt_mul hn).mpr
          rw [hposition j h, Nat.mul_comm r n]
          calc
            _ < j.val * k + k := Nat.add_lt_add_left hl _
            _ = (j.val + 1) * k := by rw [Nat.add_mul, Nat.one_mul]
            _ ≤ d * k := Nat.mul_le_mul_right k (Nat.succ_le_of_lt j.isLt)
            _ ≤ n * r := hcap
        · intro j hj j' hj' heq
          change position j / n = position j' / n at heq
          have h := hvalid j hj
          have h' := hvalid j' hj'
          have hp (a : Fin d) (ha : valid a) : position a % n = i.val := by
            rw [hposition a ha]
            exact Classical.choose_spec ha
          have heqp : position j = position j' := calc
            position j = position j % n + n * (position j / n) :=
              (Nat.mod_add_div _ _).symm
            _ = position j' % n + n * (position j' / n) := by
              rw [hp j h, hp j' h', heq]
            _ = position j' := Nat.mod_add_div _ _
          have hk : 0 < k := Nat.zero_lt_of_lt (Classical.choose h).isLt
          have hdiv (a : Fin d) (ha : valid a) : position a / k = a.val := by
            rw [hposition a ha]
            let l := Classical.choose ha
            change (a.val * k + l.val) / k = a.val
            rw [Nat.mul_comm a.val k, Nat.mul_add_div hk,
              Nat.div_eq_of_lt l.isLt, Nat.add_zero]
          apply Fin.ext
          rw [← hdiv j h, ← hdiv j' h', heqp]
      _ = r := card_range r

theorem arrayCount_pos_of_le_degree {n d r k : ℕ}
    (hd : 0 < d) (hr : r ≤ d) (hk : k ≤ n * r / d) :
    0 < arrayCount n d r k := by
  apply Finset.card_pos.mpr
  have hcap := (Nat.le_div_iff_mul_le hd).mp hk
  have hkn : k ≤ n := by
    apply Nat.le_of_mul_le_mul_right _ hd
    exact hcap.trans (Nat.mul_le_mul_left n hr)
  by_cases hn : 0 < n
  · refine ⟨cyclicArray n d k, Finset.mem_filter.mpr ⟨mem_univ _, ?_⟩⟩
    exact cyclicArray_isBalanced hn hkn (by simpa [Nat.mul_comm d k] using hcap)
  · have hzero : n = 0 := by omega
    subst n
    have hkzero : k = 0 := by omega
    subst k
    refine ⟨fun _ _ => false, Finset.mem_filter.mpr ⟨mem_univ _, ?_⟩⟩
    simp [IsBalanced, colSum]

theorem coeff_arrayPolynomial {n d r k : ℕ} (hd : 0 < d) (hr : r ≤ d) :
    (arrayPolynomial n d r).coeff k = arrayCount n d r k := by
  classical
  rw [arrayPolynomial, Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  by_cases hkn : k ≤ n
  · simp [Finset.mem_range, Nat.lt_succ_iff, hkn, eq_comm]
  · have hdeg : n * r / d ≤ n :=
      (Nat.div_le_iff_le_mul hd).mpr (by
        have := Nat.mul_le_mul_left n hr
        omega)
    rw [arrayCount_eq_zero_of_degree_lt hd (lt_of_le_of_lt hdeg (Nat.lt_of_not_ge hkn))]
    simp [Finset.mem_range, Nat.lt_succ_iff, hkn, eq_comm]

theorem natDegree_arrayPolynomial {n d r : ℕ} (hd : 0 < d) (hr : r ≤ d) :
    (arrayPolynomial n d r).natDegree = n * r / d := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    rw [coeff_arrayPolynomial hd hr, arrayCount_eq_zero_of_degree_lt hd hk, Nat.cast_zero]
  · rw [coeff_arrayPolynomial hd hr]
    exact_mod_cast (ne_of_gt (arrayCount_pos_of_le_degree hd hr le_rfl))

theorem arrayCount_one_column (n k : ℕ) :
    arrayCount n 1 1 k = n.choose k := by
  classical
  let takeSupport (A : BinaryArray n 1) := support (fun i => A i 0)
  let toArray (S : Finset (Fin n)) : BinaryArray n 1 := fun i _ => decide (i ∈ S)
  have htake (S : Finset (Fin n)) : takeSupport (toArray S) = S := by
    ext i
    simp [takeSupport, toArray, support]
  have hcol (A : BinaryArray n 1) : colSum A 0 = (takeSupport A).card :=
    sum_bit_eq_card_support _
  have hc : (arrays n 1 1 k).card = ((univ : Finset (Fin n)).powersetCard k).card := by
    apply Finset.card_bij' (fun A _ => takeSupport A) (fun S _ => toArray S)
    · intro A hA
      have h := (Finset.mem_filter.mp hA).2
      exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, (hcol A).symm.trans (h.1 0)⟩
    · intro S hS
      apply Finset.mem_filter.mpr
      refine ⟨mem_univ _, ?_, ?_⟩
      · intro j
        have hj : j = 0 := Subsingleton.elim _ _
        rw [hj, hcol, htake]
        exact (Finset.mem_powersetCard.mp hS).2
      · intro i
        simp only [rowSum, Fin.sum_univ_one, bit]
        split <;> decide
    · intro A hA
      funext i j
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      cases h : A i 0 <;> simp [takeSupport, toArray, support, h]
    · intro S _
      exact htake S
  rw [arrayCount, hc, Finset.card_powersetCard]
  simp

theorem arrayPolynomial_one_column (n : ℕ) :
    arrayPolynomial n 1 1 = (1 + X) ^ n := by
  ext k
  rw [coeff_arrayPolynomial (by decide) le_rfl, arrayCount_one_column, coeff_one_add_X_pow]

#print axioms arrays_corank_one
#print axioms mul_le_row_cap
#print axioms arrayCount_eq_zero_of_degree_lt
#print axioms cyclicArray_isBalanced
#print axioms arrayCount_pos_of_le_degree
#print axioms coeff_arrayPolynomial
#print axioms natDegree_arrayPolynomial
#print axioms arrayCount_one_column
#print axioms arrayPolynomial_one_column

end BalancedEventual
