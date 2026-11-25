import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The binomial coefficient obstruction in the infinite prism-splitting family.
The geometric interpretation of the two integer expressions uses Ehrhart reciprocity.
This file proves their ordering for every parameter and the incompatible ordering
of sums for alternating negative real roots. -/
namespace PrismFamily

private theorem choose_gap (b : ℕ) (hb : 6 ≤ b) :
    (2*b).choose b < 2 * (2*b).choose (b+2) := by
  let A := (2*b).choose b
  let B := (2*b).choose (b+1)
  let C := (2*b).choose (b+2)
  have h1 : B*(b+1) = A*b := by
    dsimp [A,B]
    simpa only [show 2*b-b=b by omega] using Nat.choose_succ_right_eq (2*b) b
  have h2 : C*(b+2) = B*(b-1) := by
    dsimp [B,C]
    simpa only [show 2*b-(b+1)=b-1 by omega] using Nat.choose_succ_right_eq (2*b) (b+1)
  have hprod : C*((b+2)*(b+1)) = A*(b*(b-1)) := by
    calc
      _ = C*(b+2)*(b+1) := by ring
      _ = B*(b-1)*(b+1) := by rw [h2]
      _ = B*(b+1)*(b-1) := by ring
      _ = A*(b*(b-1)) := by rw [h1]; ring
  have hab : (b+2)*(b+1) < 2*(b*(b-1)) := by
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hb
    simp only [show 6+t-1=5+t by omega]
    nlinarith [Nat.zero_le (t*t)]
  have hp : 0 < A := Nat.choose_pos (by omega)
  change A < 2*C
  by_contra! h
  have hh := Nat.mul_le_mul_right ((b+2)*(b+1)) h
  have hh' := Nat.mul_lt_mul_of_pos_left hab hp
  nlinarith only [hh,hh',hprod]

private theorem central_two_steps (b : ℕ) :
    (2*b+2).choose (b+1) = 2*(2*b).choose b + 2*(2*b).choose (b+1) := by
  rw [Nat.choose_succ_succ']
  have hsym : (2*b+1).choose b = (2*b+1).choose (b+1) := by
    have h := Nat.choose_symm (n := 2*b+1) (k := b) (by omega)
    simpa only [show 2*b+1-b=b+1 by omega] using h.symm
  rw [hsym, Nat.choose_succ_succ']
  ring

/-- The number of third-dilation interior points, minus the denominator exponent
(one plus dimension), for the two slices. -/
def before (b : ℕ) : ℤ :=
  ((2*b).choose b : ℤ) + 2*((2*b).choose (b+1) : ℤ) +
    2*((2*b).choose (b+2) : ℤ) - (2*(b : ℤ)+1)

def after (b : ℕ) : ℤ :=
  ((2*b+2).choose (b+1) : ℤ) - (2*(b : ℤ)+2)

theorem coefficient_gap (b : ℕ) (hb : 6 ≤ b) : after b < before b := by
  unfold before after
  rw [central_two_steps]
  push_cast
  have h : ((2*b).choose b : ℤ) < 2*((2*b).choose (b+2) : ℤ) := by
    exact_mod_cast choose_gap b hb
  linarith

theorem coefficient_gap_beyond_one (b : ℕ) (hb : 6 ≤ b) : after b + 1 < before b := by
  unfold before after
  rw [central_two_steps]
  push_cast
  have h : ((2*b).choose b : ℤ) < 2*((2*b).choose (b+2) : ℤ) := by
    exact_mod_cast choose_gap b hb
  linarith

/-- Weakly alternating negative roots, in increasing order with one extra
root on the second side. -/
inductive AlternatingNegative : List ℝ → List ℝ → Prop
  | last (z : ℝ) (hz : z < 0) : AlternatingNegative [] [z]
  | step {x y z : ℝ} {xs zs : List ℝ}
      (left : y ≤ x) (right : x ≤ z) (tail : AlternatingNegative xs (z :: zs)) :
      AlternatingNegative (x :: xs) (y :: z :: zs)

theorem vieta_order {xs ys : List ℝ} (h : AlternatingNegative xs ys) :
    -xs.sum < -ys.sum := by
  induction h with
  | last z hz => simpa using hz
  | @step x y z xs zs left right tail ih =>
    simp only [List.sum_cons] at ih ⊢
    linarith

theorem no_family_interlacing (b : ℕ) (hb : 6 ≤ b) :
    ¬ ∃ xs ys : List ℝ, AlternatingNegative xs ys ∧
      -xs.sum = (before b : ℝ) ∧ -ys.sum = (after b : ℝ) := by
  rintro ⟨xs,ys,h,hx,hy⟩
  have hlt := vieta_order h
  rw [hx,hy] at hlt
  have hrev : (after b : ℝ) < (before b : ℝ) := by exact_mod_cast coefficient_gap b hb
  exact (not_lt_of_ge hrev.le) hlt

/-- Actual polynomial version. The two next-coefficient hypotheses are
identified with the slice numerators by Ehrhart reciprocity in the paper. -/
theorem polynomial_obstruction (b : ℕ) (hb : 6 ≤ b) (p q : Polynomial ℝ)
    (hp : p.Monic) (hq : q.Monic)
    (sp : p.Splits (RingHom.id ℝ)) (sq : q.Splits (RingHom.id ℝ))
    (cp : p.nextCoeff = (before b : ℝ)) (cq : q.nextCoeff = (after b : ℝ)) :
    ¬ ∃ xs ys : List ℝ, (xs : Multiset ℝ) = p.roots ∧
      (ys : Multiset ℝ) = q.roots ∧ AlternatingNegative xs ys := by
  rintro ⟨xs,ys,hx,hy,h⟩
  apply no_family_interlacing b hb
  refine ⟨xs,ys,h,?_,?_⟩
  · rw [← cp, Polynomial.sum_roots_eq_nextCoeff_of_monic_of_split hp sp, ← hx]
    rfl
  · rw [← cq, Polynomial.sum_roots_eq_nextCoeff_of_monic_of_split hq sq, ← hy]
    rfl

#print axioms polynomial_obstruction
#print axioms coefficient_gap
#print axioms coefficient_gap_beyond_one
#print axioms no_family_interlacing
end PrismFamily
