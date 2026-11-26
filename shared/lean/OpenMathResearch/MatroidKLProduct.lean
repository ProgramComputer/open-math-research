import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import OpenMathResearch.MatroidKLRecurrence

/-!
# Kazhdan–Lusztig multiplicativity for products of ranked intervals

For a product of two ranked intervals, the rank-shifted sum factors.
Rank-additivity and multiplicativity of reflection give the required
rank-zero, degree and palindromicity conditions for the product of the
two Kazhdan–Lusztig families.
-/

open Finset Polynomial
open scoped BigOperators Polynomial

noncomputable section

namespace OpenMathResearch.MatroidKL

variable {α β : Type*} [PartialOrder α] [PartialOrder β] [OrderTop α] [OrderTop β]

/-- The sum of ranks on a product of posets. -/
def productRank (rank₁ : α → ℕ) (rank₂ : β → ℕ) (a : α × β) : ℕ :=
  rank₁ a.1 + rank₂ a.2

private theorem height_productRank (rank₁ : α → ℕ) (rank₂ : β → ℕ)
    (h₁ : Monotone rank₁) (h₂ : Monotone rank₂) (a : α × β) :
    height (productRank rank₁ rank₂) a = height rank₁ a.1 + height rank₂ a.2 := by
  have ha := h₁ (le_top : a.1 ≤ ⊤)
  have hb := h₂ (le_top : a.2 ≤ ⊤)
  change rank₁ ⊤ + rank₂ ⊤ - (rank₁ a.1 + rank₂ a.2) = _
  unfold height
  omega

variable [LocallyFiniteOrder α] [LocallyFiniteOrder β] [LocallyFiniteOrder (α × β)]

theorem shiftedSum_product (rank₁ : α → ℕ) (rank₂ : β → ℕ)
    (h₁ : Monotone rank₁) (h₂ : Monotone rank₂) (p : α → ℤ[X]) (q : β → ℤ[X]) (a : α × β) :
    shiftedSum (productRank rank₁ rank₂) (fun b => p b.1 * q b.2) a =
      shiftedSum rank₁ p a.1 * shiftedSum rank₂ q a.2 := by
  classical
  have hInterval : Finset.Icc a ⊤ = (Finset.Icc a.1 ⊤) ×ˢ (Finset.Icc a.2 ⊤) := by
    ext b
    simp [Prod.le_def]
  simp only [shiftedSum_apply]
  rw [hInterval, Finset.sum_product, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  have hab := h₁ (Finset.mem_Icc.mp hb).1
  have hac := h₂ (Finset.mem_Icc.mp hc).1
  have he : productRank rank₁ rank₂ (b, c) - productRank rank₁ rank₂ a =
      (rank₁ b - rank₁ a.1) + (rank₂ c - rank₂ a.2) := by
    unfold productRank
    dsimp
    omega
  rw [he, pow_add]
  ac_rfl

variable [Fintype α] [Fintype β]

private theorem isKLFamily_eq_one_of_rank_zero {γ : Type*} [Fintype γ] [PartialOrder γ] [OrderTop γ]
    (rank : γ → ℕ) (p : γ → ℤ[X]) (hp : IsKLFamily rank (fun a i => (p a).coeff i))
    (a : γ) (ha : height rank a = 0) : p a = 1 := by
  ext i
  rw [hp.rank_zero a ha i]
  simp [Polynomial.coeff_one]

theorem IsKLFamily.twice_natDegree_lt {γ : Type*} [Fintype γ] [PartialOrder γ] [OrderTop γ]
    (rank : γ → ℕ) (p : γ → ℤ[X]) (hp : IsKLFamily rank (fun a i => (p a).coeff i))
    (a : γ) (ha : 0 < height rank a) : 2 * (p a).natDegree < height rank a := by
  by_cases hZero : p a = 0
  · simpa [hZero] using ha
  · by_contra! hHigh
    exact (Polynomial.leadingCoeff_ne_zero.mpr hZero) (hp.high_coeff a _ ha hHigh)

private theorem shiftedSum_natDegree_le {γ : Type*} [Fintype γ] [PartialOrder γ] [OrderTop γ]
    [LocallyFiniteOrder γ] (rank : γ → ℕ) (hRank : StrictMono rank) (p : γ → ℤ[X])
    (hp : IsKLFamily rank (fun a i => (p a).coeff i)) (a : γ) :
    (shiftedSum rank p a).natDegree ≤ height rank a := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  rw [coeff_shiftedSum]
  exact hp.zCoeff_eq_zero_of_height_lt rank hRank a hi

/-- Products of the two coefficient families satisfy the KL conditions on the product poset. -/
theorem IsKLFamily.product (rank₁ : α → ℕ) (rank₂ : β → ℕ)
    (h₁ : StrictMono rank₁) (h₂ : StrictMono rank₂) (p : α → ℤ[X]) (q : β → ℤ[X])
    (hp : IsKLFamily rank₁ (fun a i => (p a).coeff i))
    (hq : IsKLFamily rank₂ (fun b i => (q b).coeff i)) :
    IsKLFamily (productRank rank₁ rank₂) (fun a i => (p a.1 * q a.2).coeff i) := by
  have hHeight := height_productRank rank₁ rank₂ h₁.monotone h₂.monotone
  constructor
  · intro a ha i
    rw [hHeight a] at ha
    rw [isKLFamily_eq_one_of_rank_zero rank₁ p hp a.1 (by omega),
      isKLFamily_eq_one_of_rank_zero rank₂ q hq a.2 (by omega), one_mul]
    simp [Polynomial.coeff_one]
  · intro a i hPos hHigh
    rw [hHeight a] at hPos hHigh
    have hDeg : (p a.1 * q a.2).natDegree ≤ (p a.1).natDegree + (q a.2).natDegree :=
      Polynomial.natDegree_mul_le
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    by_cases ha : height rank₁ a.1 = 0
    · have hq' := hq.twice_natDegree_lt rank₂ q a.2 (by omega)
      rw [isKLFamily_eq_one_of_rank_zero rank₁ p hp a.1 ha, one_mul]
      omega
    · have hp' := hp.twice_natDegree_lt rank₁ p a.1 (by omega)
      by_cases hb : height rank₂ a.2 = 0
      · rw [isKLFamily_eq_one_of_rank_zero rank₂ q hq a.2 hb, mul_one]
        omega
      · have hq' := hq.twice_natDegree_lt rank₂ q a.2 (by omega)
        omega
  · intro a i hi
    let r := productRank rank₁ rank₂
    let P : α × β → ℤ[X] := fun b => p b.1 * q b.2
    have hReflect : (shiftedSum r P a).reflect (height r a) = shiftedSum r P a := by
      dsimp only [r, P]
      rw [shiftedSum_product rank₁ rank₂ h₁.monotone h₂.monotone, hHeight a,
        reflect_mul _ _ (shiftedSum_natDegree_le rank₁ h₁ p hp a.1)
          (shiftedSum_natDegree_le rank₂ h₂ q hq a.2),
        shiftedSum_reflect_of_isKLFamily rank₁ p hp a.1,
        shiftedSum_reflect_of_isKLFamily rank₂ q hq a.2]
    have hCoeff := congrArg (fun f : ℤ[X] => f.coeff i) hReflect
    change zCoeff r (fun b j => (P b).coeff j) a i = zCoeff r (fun b j => (P b).coeff j) a (height r a - i)
    simpa only [coeff_reflect, revAt_le (show i ≤ height r a by dsimp only [r]; omega),
      coeff_shiftedSum] using hCoeff.symm

#print axioms shiftedSum_product
#print axioms IsKLFamily.product
#print axioms IsKLFamily.twice_natDegree_lt

end OpenMathResearch.MatroidKL
