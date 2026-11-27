import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic

namespace OpenMathResearch.LongCycleExcedances.InsertionTable
open Polynomial Finset

/-- Return the row at each preceding size, newest first. The lag of an early
row is clipped to size zero, as in the insertion recurrence on naturals. -/
def history {α : Type u} (k : ℕ) (seed : α) (step : ℕ → α → α → α) : ℕ → List α
  | 0 => [seed]
  | n+1 =>
    let prior := history k seed step n
    step n (prior.getD 0 seed) (prior.getD (min n (k-1)) seed) :: prior

theorem history_sound {α : Type u} {β : Type v} (k : ℕ) (seed : α)
    (step : ℕ → α → α → α) (f : ℕ → β) (rel : α → β → Prop)
    (init : rel seed (f 0))
    (advance : ∀ n p q, rel p (f n) → rel q (f (n - (k-1))) →
      rel (step n p q) (f (n+1))) :
    ∀ n i, i ≤ n → rel ((history k seed step n).getD i seed) (f (n-i)) := by
  intro n
  induction n with
  | zero =>
    intro i hi
    have : i=0 := by omega
    subst i
    simpa [history] using init
  | succ n ih =>
    intro i hi
    cases i with
    | zero =>
      simp only [history, List.getD_cons_zero, Nat.sub_zero]
      apply advance
      · simpa using ih 0 (Nat.zero_le _)
      · have h := ih (min n (k-1)) (min_le_left _ _)
        have e : n - min n (k-1) = n - (k-1) := by omega
        simpa only [e] using h
    | succ i =>
      have h := ih i (by omega)
      simpa only [history, List.getD_cons_succ, Nat.succ_sub_succ_eq_sub] using h

/-- Coefficient of the original-row recurrence at strictly positive index. -/
theorem insertion_coeff {n : ℕ} (p q a r : ℝ[X]) (b : ℝ)
    (h : q = C (n : ℝ)*X*p + X*(1-X)*derivative p + C b*(X*a)*r) (i : ℕ) :
    q.coeff (i+1) = ((i:ℝ)+1)*p.coeff (i+1) +
      ((n:ℝ)-(i:ℝ))*p.coeff i + b*∑ l ∈ range (i+1), a.coeff l*r.coeff (i-l) := by
  have eq : q = C (n : ℝ)*(X*p) + X*(derivative p-X*derivative p) + C b*(X*(a*r)) := by
    rw [h]
    ring
  have conv : (a*r).coeff i = ∑ l ∈ range (i+1), a.coeff l*r.coeff (i-l) := by
    rw [coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ (fun l h => a.coeff l*r.coeff h)]
  rw [eq]
  simp only [coeff_add, coeff_C_mul, coeff_X_mul, coeff_sub, coeff_derivative, conv]
  cases i with
  | zero =>
    simp only [coeff_X_mul_zero, Nat.cast_zero, Nat.zero_add, sub_zero]
    ring
  | succ i =>
    rw [coeff_X_mul, coeff_derivative]
    push_cast
    ring

#print axioms history_sound
#print axioms insertion_coeff

def entry (r : List ℤ) (i : ℕ) : ℤ := r[i]?.getD 0

def rowOf (w : ℕ) (c : ℕ → ℤ) : List ℤ := (List.range w).map c

theorem entry_rowOf (w i : ℕ) (c : ℕ → ℤ) (hi : i < w) :
    entry (rowOf w c) i = c i := by
  simp [entry, rowOf, List.getElem?_map, List.getElem?_range hi]

def start (w : ℕ) : List ℤ := rowOf w fun i => if i=0 then 1 else 0

/-- Coefficient convolution stops when the Eulerian prefix ends. -/
def convolution : List ℤ → List ℤ → ℕ → ℤ
  | [], _, _ => 0
  | a :: _, r, 0 => a * entry r 0
  | a :: rest, r, i+1 => a * entry r (i+1) + convolution rest r i

theorem convolution_eq (a r : List ℤ) (i : ℕ) :
    convolution a r i = ∑ j ∈ range (i+1), entry a j * entry r (i-j) := by
  induction i generalizing a with
  | zero => cases a <;> simp [convolution,entry]
  | succ i ih =>
    cases a with
    | nil => simp [convolution,entry]
    | cons v rest =>
      rw [convolution, ih]
      conv_rhs => rw [sum_range_succ']
      simp only [entry, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
        Nat.sub_zero, Nat.succ_sub_succ_eq_sub]
      exact add_comm _ _

def next (w k : ℕ) (a : List ℤ) (n : ℕ) (p r : List ℤ) : List ℤ :=
  rowOf w fun
  | 0 => 0
  | i+1 =>
    ((i : ℤ)+1) * entry p (i+1) + ((n : ℤ)-(i : ℤ)) * entry p i +
      ((n.descFactorial (k-1) / (k-1).factorial : ℕ) : ℤ) * convolution a r i

def agrees (w : ℕ) (r : List ℤ) (p : ℝ[X]) : Prop :=
  ∀ i, i<w → (entry r i : ℝ)=p.coeff i

theorem next_agrees (w k n : ℕ) (a p r : List ℤ) (A P R Q : ℝ[X])
    (ha : agrees w a A) (hp : agrees w p P) (hr : agrees w r R)
    (h : Q = C (n : ℝ)*X*P + X*(1-X)*derivative P +
      C (n.choose (k-1) : ℝ)*(X*A)*R) :
    agrees w (next w k a n p r) Q := by
  intro i hi
  rw [next, entry_rowOf _ _ _ hi]
  cases i with
  | zero =>
    have heq : Q = X*(C (n : ℝ)*P + (1-X)*derivative P + C (n.choose (k-1) : ℝ)*A*R) := by
      rw [h]
      ring
    simp [heq]
  | succ i =>
    dsimp only
    rw [insertion_coeff P Q A R _ h i, convolution_eq, ← Nat.choose_eq_descFactorial_div_factorial]
    simp only [Int.cast_add, Int.cast_mul, Int.cast_sub, Int.cast_natCast, Int.cast_one,
      Int.cast_sum]
    rw [hp (i+1) hi, hp i (by omega)]
    congr 1
    congr 1
    apply sum_congr rfl
    intro l hl
    have hl' := mem_range.mp hl
    rw [ha l (by omega), hr (i-l) (by omega)]

theorem table_agrees (w k : ℕ) (hk : 2 ≤ k) (a : List ℤ) (A : ℝ[X])
    (E : ℕ → ℝ[X]) (ha : agrees w a A) (h0 : E 0 = 1)
    (hs : ∀ n, E (n+1) = C (n : ℝ)*X*E n + X*(1-X)*derivative (E n) +
      C (n.choose (k-1) : ℝ)*(X*A)*E (n+1-k)) (n : ℕ) :
    agrees w ((history k (start w) (next w k a) n).getD 0 (start w)) (E n) := by
  have init : agrees w (start w) (E 0) := by
    intro i hi
    rw [start, entry_rowOf _ _ _ hi, h0, coeff_one]
    split <;> norm_num
  have step : ∀ m p r, agrees w p (E m) → agrees w r (E (m - (k-1))) →
      agrees w (next w k a m p r) (E (m+1)) := by
    intro m p r hp hr
    have e : m - (k-1) = m+1-k := by omega
    rw [e] at hr
    exact next_agrees w k m a p r A _ _ _ ha hp hr (hs m)
  simpa using history_sound k (start w) (next w k a) E (agrees w) init step n 0 (Nat.zero_le _)

#print axioms convolution_eq
#print axioms table_agrees

end OpenMathResearch.LongCycleExcedances.InsertionTable
