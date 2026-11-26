import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Combinatorics.Matroid.Circuit
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Nat.Choose.Basic

/-!
# Source-facing specification of Alexandersson's ribbon conjecture

A path is a word in east and north steps, with north represented by `true`.
Bases are the sets of north-step positions of intermediate paths. The ribbon
hypothesis uses the cells between the east steps in each column. The
conclusion gives every Narayana coefficient and asserts that each complex
zero has zero imaginary part.
-/

open scoped Polynomial

namespace Ribbon.Source

abbrev Path (n : ℕ) := Fin n → Bool

/-- The number of north steps among the first `t` steps. -/
def prefixNorth {n : ℕ} (p : Path n) (t : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin n)).filter fun i => i.val < t ∧ p i = true).card

/-- Count the selected step positions among the first `t` steps. -/
noncomputable def prefixBase {n : ℕ} (B : Set (Fin n)) (t : ℕ) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Fin n)).filter fun i => i.val < t ∧ i ∈ B).card

/-- The east step in column `x` has lower endpoint at height `y`. -/
def eastLevel {n : ℕ} (p : Path n) (x y : ℕ) : Prop :=
  ∃ i : Fin n, p i = false ∧ prefixNorth p i.val = y ∧ i.val = x + y

/-- The unit square with lower left corner `(x,y)` lies in the strip. -/
def cell {n : ℕ} (lower upper : Path n) (x y : ℕ) : Prop :=
  ∃ l u : ℕ, eastLevel lower x l ∧ eastLevel upper x u ∧ l ≤ y ∧ y < u

/-- The standard boundary-path description of a nonempty connected ribbon matroid. -/
structure IsRibbonPresentation {n : ℕ} (M : Matroid (Fin n)) (r : ℕ)
    (lower upper : Path n) : Prop where
  ground_eq : M.E = Set.univ
  connected : ∀ e f : Fin n, e ≠ f → ∃ C, M.IsCircuit C ∧ e ∈ C ∧ f ∈ C
  endpoint_lower : prefixNorth lower n = r
  endpoint_upper : prefixNorth upper n = r
  ordered : ∀ t ≤ n, prefixNorth lower t ≤ prefixNorth upper t
  nonempty : ∃ x y, cell lower upper x y
  no_square : ∀ x y, ¬(cell lower upper x y ∧ cell lower upper (x + 1) y ∧
    cell lower upper x (y + 1) ∧ cell lower upper (x + 1) (y + 1))
  bases (B : Set (Fin n)) : M.IsBase B ↔ ∀ t ≤ n,
    prefixNorth lower t ≤ prefixBase B t ∧ prefixBase B t ≤ prefixNorth upper t

theorem prefixBase_length {n : ℕ} (B : Set (Fin n)) : prefixBase B n = B.ncard := by
  classical
  letI : Fintype B := Fintype.ofFinite _
  rw [Set.ncard_eq_toFinset_card' B, prefixBase]
  congr 1
  ext i
  simp [i.isLt]

/-- The endpoint height is the ordinary matroid rank. -/
theorem IsRibbonPresentation.rank_eq {n r : ℕ} {M : Matroid (Fin n)} {lower upper : Path n}
    (h : IsRibbonPresentation M r lower upper) : M.eRank.toNat = r := by
  obtain ⟨B, hB⟩ := M.exists_isBase
  have hr := (h.bases B).mp hB n le_rfl
  rw [h.endpoint_lower, h.endpoint_upper, prefixBase_length] at hr
  rw [← hB.encard_eq_eRank, ← Set.ncard_def]
  exact le_antisymm hr.2 hr.1

/-- The original conjecture, with `Z` to be instantiated by the matroid invariant.
The coefficient equality is multiplied through by the positive integer `r + 1`. -/
def NarayanaClaim (Z : ∀ n, Matroid (Fin n) → ℤ[X]) : Prop :=
  ∀ (n r : ℕ) (M : Matroid (Fin n)) (lower upper : Path n),
    IsRibbonPresentation M r lower upper →
      (∀ k : ℕ, ((r + 1 : ℕ) : ℤ) * (Z n M).coeff k =
        ((r + 1).choose k : ℤ) * ((r + 1).choose (k + 1) : ℤ)) ∧
      (∀ z : ℂ, (Z n M).eval₂ (Int.castRingHom ℂ) z = 0 → z.im = 0)

#print axioms IsRibbonPresentation.rank_eq

end Ribbon.Source
