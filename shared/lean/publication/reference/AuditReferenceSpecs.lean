import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Pi

/-!
Source-level specifications extracted independently of target proof modules.
-/
namespace AuditReference

open Polynomial Finset
open scoped BigOperators

/-- A sorted list accounts for every root, including multiplicity. -/
def RealRoots (p : ℝ[X]) (xs : List ℝ) : Prop :=
  p ≠ 0 ∧ xs.Pairwise (· ≤ ·) ∧
    p = Polynomial.C p.leadingCoeff * (xs.map fun x => X - Polynomial.C x).prod

/-- Oriented weak interleaving used by the original Catalan source. -/
def Interleaves (xs ys : List ℝ) : Prop :=
  (xs.length = ys.length ∧
    (∀ i < xs.length, xs.getD i 0 ≤ ys.getD i 0) ∧
    (∀ i, i+1 < xs.length → ys.getD i 0 ≤ xs.getD (i+1) 0)) ∨
  (xs.length+1 = ys.length ∧
    ∀ i < xs.length, ys.getD i 0 ≤ xs.getD i 0 ∧ xs.getD i 0 ≤ ys.getD (i+1) 0)

/-- Strict version for the stronger public Catalan conclusion. -/
def StrictInterleaves (xs ys : List ℝ) : Prop :=
  (xs.length = ys.length ∧
    (∀ i < xs.length, xs.getD i 0 < ys.getD i 0) ∧
    (∀ i, i+1 < xs.length → ys.getD i 0 < xs.getD (i+1) 0)) ∨
  (xs.length+1 = ys.length ∧
    ∀ i < xs.length, ys.getD i 0 < xs.getD i 0 ∧ xs.getD i 0 < ys.getD (i+1) 0)

abbrev BoundedWord (n : ℕ) := Fin n → Fin (n+1)

def IsCatalan {n : ℕ} (w : BoundedWord n) : Prop :=
  (∀ h : 0<n, (w ⟨0,h⟩).val = 0) ∧
    ∀ i : ℕ, ∀ h : i+1<n,
      (w ⟨i+1,h⟩).val ≤ (w ⟨i, lt_trans (Nat.lt_succ_self i) h⟩).val + 1

noncomputable def peakCount {n : ℕ} (w : BoundedWord n) : ℕ := by
  classical
  exact ((range n).filter fun i =>
    if h : i+2<n then
      (w ⟨i, lt_trans (Nat.lt_succ_self i) (lt_trans (Nat.lt_succ_self (i+1)) h)⟩).val <
        (w ⟨i+1, lt_trans (Nat.lt_succ_self (i+1)) h⟩).val ∧
      (w ⟨i+2,h⟩).val < (w ⟨i+1, lt_trans (Nat.lt_succ_self (i+1)) h⟩).val
    else False).card

/-- The original word enumerator, with no recurrence or coefficient identity assumed. -/
noncomputable def catalanPolynomial (n : ℕ) : ℝ[X] := by
  classical
  exact ∑ w ∈ univ.filter IsCatalan, X ^ peakCount (n := n) w

def CatalanOriginal : Prop :=
  ∀ n, ∃ xs ys : List ℝ,
    RealRoots (catalanPolynomial n) xs ∧ RealRoots (catalanPolynomial (n+1)) ys ∧
    Interleaves xs ys

def CatalanPublished : Prop :=
  ∀ n, ∃ xs ys : List ℝ,
    RealRoots (catalanPolynomial n) xs ∧ RealRoots (catalanPolynomial (n+1)) ys ∧
    xs.Pairwise (· < ·) ∧ ys.Pairwise (· < ·) ∧
    (∀ x ∈ xs, x < 0) ∧ (∀ y ∈ ys, y < 0) ∧ StrictInterleaves xs ys

/-- Count bounded tuples at dilation m directly. Each coordinate is at most mk. -/
noncomputable def prismCount (c : List ℕ) (k m : ℕ) : ℕ := by
  classical
  exact (univ.filter fun x : Fin c.length → Fin (m*k+1) =>
    (∀ i : Fin c.length, (x i).val ≤ m*(c.get i)) ∧
      ∑ i : Fin c.length, (x i).val = m*k).card

/-- Coefficientwise version of Eq. (5.3) in the version of record. -/
def IsPrismNumerator (c : List ℕ) (k : ℕ) (p : ℝ[X]) : Prop :=
  ∀ j : ℕ, p.coeff j = ∑ i ∈ range (j+1),
    (-1 : ℝ)^i * (c.length.choose i : ℝ) * (prismCount c k (j-i) : ℝ)

def InterleavingPolynomials (p q : ℝ[X]) : Prop :=
  ∃ xs ys, RealRoots p xs ∧ RealRoots q ys ∧
    (Interleaves xs ys ∨ Interleaves ys xs)

abbrev originalBounds (a : ℕ) : List ℕ := List.replicate (2*a-2) 1 ++ [2]
abbrev splitBounds (a : ℕ) : List ℕ := List.replicate (2*a) 1

def PrismPublished : Prop :=
  ∀ a : ℕ, 6 ≤ a → ∃ p q : ℝ[X],
    IsPrismNumerator (originalBounds a) a p ∧
    IsPrismNumerator (splitBounds a) a q ∧ ¬ InterleavingPolynomials p q

end AuditReference
