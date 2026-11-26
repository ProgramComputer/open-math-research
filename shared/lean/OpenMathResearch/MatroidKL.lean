import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Int.Basic

/-!
# Kazhdan–Lusztig coefficients from ranked upper intervals

Proudfoot–Xu–Young, Proposition 2.3, characterizes the Kazhdan–Lusztig family
by the degree bound and palindromicity of the corresponding Z-polynomials.
Here we construct and prove uniqueness of the coefficients with this
characterization on a finite poset with top and a strictly increasing rank.
-/

open scoped BigOperators

noncomputable section

namespace OpenMathResearch.MatroidKL

variable {α : Type*} [PartialOrder α] [OrderTop α]

/-- The rank difference from an element to the top. -/
def height (rank : α → ℕ) (a : α) : ℕ := rank ⊤ - rank a

private theorem height_lt (rank : α → ℕ) (hRank : StrictMono rank)
    {a b : α} (hab : a < b) : height rank b < height rank a := by
  have h₁ := hRank hab
  have h₂ := hRank.monotone (le_top : b ≤ ⊤)
  unfold height
  omega

variable [Fintype α]

/-- The coefficient of the Z-sum arising from the elements strictly above `a`. -/
def upperTail (rank : α → ℕ) (a : α) (p : {b : α // a < b} → ℕ → ℤ)
    (i : ℕ) : ℤ := by
  classical
  exact ∑ b, if rank b.val - rank a ≤ i then p b (i - (rank b.val - rank a)) else 0

/-- The Z coefficient on the upper interval starting at `a`. -/
def zCoeff (rank : α → ℕ) (p : α → ℕ → ℤ) (a : α) (i : ℕ) : ℤ :=
  p a i + upperTail rank a (fun b => p b.val) i

/-- The degree conditions and the lower half of the palindromicity relations. -/
structure IsKLFamily (rank : α → ℕ) (p : α → ℕ → ℤ) : Prop where
  rank_zero (a : α) (h : height rank a = 0) (i : ℕ) : p a i = if i = 0 then 1 else 0
  high_coeff (a : α) (i : ℕ) (hPos : 0 < height rank a) (hHigh : height rank a ≤ 2 * i) :
    p a i = 0
  palindrome (a : α) (i : ℕ) (hLow : 2 * i < height rank a) :
    zCoeff rank p a i = zCoeff rank p a (height rank a - i)

/-- Construct the lower half from the upper half of the Z-sum, by corank. -/
def klCoeff (rank : α → ℕ) (hRank : StrictMono rank) (a : α) (i : ℕ) : ℤ :=
  if height rank a = 0 then
    if i = 0 then 1 else 0
  else if 2 * i < height rank a then
    let tail := upperTail rank a (fun b j => klCoeff rank hRank b.val j)
    tail (height rank a - i) - tail i
  else 0
termination_by height rank a
decreasing_by
  exact height_lt rank hRank b.property

private theorem klCoeff_eq_zero_of_high (rank : α → ℕ) (hRank : StrictMono rank)
    (a : α) (i : ℕ) (hPos : 0 < height rank a) (hHigh : height rank a ≤ 2 * i) :
    klCoeff rank hRank a i = 0 := by
  rw [klCoeff]
  simp [ne_of_gt hPos, not_lt_of_ge hHigh]

theorem klCoeff_isKLFamily (rank : α → ℕ) (hRank : StrictMono rank) :
    IsKLFamily rank (klCoeff rank hRank) := by
  constructor
  · intro a h i
    rw [klCoeff]
    simp [h]
  · exact klCoeff_eq_zero_of_high rank hRank
  · intro a i hLow
    have hPos : 0 < height rank a := by omega
    have hHigh : height rank a ≤ 2 * (height rank a - i) := by omega
    unfold zCoeff
    rw [klCoeff_eq_zero_of_high rank hRank a _ hPos hHigh, zero_add]
    conv_lhs =>
      arg 1
      rw [klCoeff]
    simp [ne_of_gt hPos, hLow]

theorem IsKLFamily.eq_klCoeff (rank : α → ℕ) (hRank : StrictMono rank)
    {p : α → ℕ → ℤ} (hp : IsKLFamily rank p) : p = klCoeff rank hRank := by
  have hKL := klCoeff_isKLFamily rank hRank
  suffices h : ∀ a : α, ∀ i, p a i = klCoeff rank hRank a i by
    exact funext fun a => funext (h a)
  intro a
  induction a using (measure (height rank)).wf.induction with
  | h a ih =>
    intro i
    by_cases hZero : height rank a = 0
    · rw [hp.rank_zero a hZero i, hKL.rank_zero a hZero i]
    have hPos : 0 < height rank a := Nat.pos_of_ne_zero hZero
    by_cases hLow : 2 * i < height rank a
    · have hHigh : height rank a ≤ 2 * (height rank a - i) := by omega
      have ep := hp.palindrome a i hLow
      have ek := hKL.palindrome a i hLow
      unfold zCoeff at ep ek
      rw [hp.high_coeff a _ hPos hHigh, zero_add] at ep
      rw [hKL.high_coeff a _ hPos hHigh, zero_add] at ek
      have eTail (j : ℕ) : upperTail rank a (fun b => p b.val) j =
          upperTail rank a (fun b => klCoeff rank hRank b.val) j := by
        congr 1
        funext b k
        exact ih b.val (height_lt rank hRank b.property) k
      rw [eTail i, eTail (height rank a - i)] at ep
      omega
    · rw [hp.high_coeff a i hPos (by omega), hKL.high_coeff a i hPos (by omega)]

/-- The two halves of the Z-sum agree at every degree up to the interval rank. -/
theorem IsKLFamily.zCoeff_palindrome (rank : α → ℕ) {p : α → ℕ → ℤ}
    (hp : IsKLFamily rank p) (a : α) {i : ℕ} (hi : i ≤ height rank a) :
    zCoeff rank p a i = zCoeff rank p a (height rank a - i) := by
  by_cases hLow : 2 * i < height rank a
  · exact hp.palindrome a i hLow
  by_cases hHigh : height rank a < 2 * i
  · have h := hp.palindrome a (height rank a - i) (by omega)
    have e : height rank a - (height rank a - i) = i := by omega
    rw [e] at h
    exact h.symm
  · have e : height rank a - i = i := by omega
    rw [e]

theorem IsKLFamily.coeff_eq_zero_of_height_lt (rank : α → ℕ) {p : α → ℕ → ℤ}
    (hp : IsKLFamily rank p) (a : α) {i : ℕ} (hi : height rank a < i) : p a i = 0 := by
  by_cases hZero : height rank a = 0
  · have hi' : i ≠ 0 := by omega
    simp [hp.rank_zero a hZero i, hi']
  · exact hp.high_coeff a i (by omega) (by omega)

/-- The Z-sum has no coefficients above the interval rank. -/
theorem IsKLFamily.zCoeff_eq_zero_of_height_lt (rank : α → ℕ) (hRank : StrictMono rank)
    {p : α → ℕ → ℤ} (hp : IsKLFamily rank p) (a : α) {i : ℕ} (hi : height rank a < i) :
    zCoeff rank p a i = 0 := by
  classical
  rw [zCoeff, hp.coeff_eq_zero_of_height_lt rank a hi, zero_add, upperTail]
  apply Finset.sum_eq_zero
  intro b _
  split
  · apply hp.coeff_eq_zero_of_height_lt rank b.val
    have hab := hRank b.property
    have hTop := hRank.monotone (le_top : b.val ≤ ⊤)
    unfold height at hi ⊢
    omega
  · rfl

theorem IsKLFamily.zCoeff_of_rank_zero (rank : α → ℕ) (hRank : StrictMono rank)
    {p : α → ℕ → ℤ} (hp : IsKLFamily rank p) (a : α) (hZero : height rank a = 0) (i : ℕ) :
    zCoeff rank p a i = if i = 0 then 1 else 0 := by
  classical
  have hTail : upperTail rank a (fun b => p b.val) i = 0 := by
    rw [upperTail]
    apply Finset.sum_eq_zero
    intro b _
    have h := height_lt rank hRank b.property
    omega
  rw [zCoeff, hTail, add_zero, hp.rank_zero a hZero i]

#print axioms klCoeff_isKLFamily
#print axioms IsKLFamily.eq_klCoeff
#print axioms IsKLFamily.zCoeff_palindrome
#print axioms IsKLFamily.zCoeff_eq_zero_of_height_lt
#print axioms IsKLFamily.zCoeff_of_rank_zero

end OpenMathResearch.MatroidKL
