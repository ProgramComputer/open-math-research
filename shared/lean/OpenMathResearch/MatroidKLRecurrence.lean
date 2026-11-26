import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra
import OpenMathResearch.MatroidKL

/-!
# Characteristic-polynomial recurrence on ranked intervals

Write the characteristic polynomial of an interval as the convolution of
its Möbius function with the rank monomials. Multiplication by the zeta
function cancels the Möbius function. Reflection takes each rank-shifted
summand in the Z-polynomial to the reflected polynomial of its upper
interval. These two identities relate the original Kazhdan–Lusztig
recurrence to palindromicity of Z.
-/

open Finset IncidenceAlgebra Polynomial
open scoped BigOperators Polynomial

noncomputable section

namespace OpenMathResearch.MatroidKL

variable {α : Type*} [PartialOrder α]

/-- The rank monomial of an interval. -/
def rankMonomials (rank : α → ℕ) : IncidenceAlgebra ℤ[X] α := by
  classical
  refine ⟨fun a b => if a ≤ b then X ^ (rank b - rank a) else 0, ?_⟩
  intro a b h
  simp [h]

private theorem rankMonomials_apply (rank : α → ℕ) {a b : α} (h : a ≤ b) :
    rankMonomials rank a b = X ^ (rank b - rank a) := by
  simp [rankMonomials, coe_mk, h]

variable [LocallyFiniteOrder α]

private def polynomialMu [DecidableEq α] : IncidenceAlgebra ℤ[X] α := by
  refine ⟨fun a b => C (mu ℤ a b), ?_⟩
  intro a b h
  simp [apply_eq_zero_of_not_le h]

private theorem polynomialMu_apply [DecidableEq α] (a b : α) :
    (polynomialMu : IncidenceAlgebra ℤ[X] α) a b = C (mu ℤ a b) := rfl

private theorem polynomialMu_mul_zeta [DecidableLE α] [DecidableEq α] :
    (polynomialMu * zeta ℤ[X] : IncidenceAlgebra ℤ[X] α) = 1 := by
  classical
  apply IncidenceAlgebra.ext
  intro a b _
  rw [IncidenceAlgebra.mul_apply, IncidenceAlgebra.one_apply]
  calc
    (∑ c ∈ Icc a b, polynomialMu a c * zeta ℤ[X] c b) = ∑ c ∈ Icc a b, C (mu ℤ a c) := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [polynomialMu_apply, zeta_of_le (Finset.mem_Icc.mp hc).2, mul_one]
    _ = _ := by
      rw [← map_sum, sum_Icc_mu_right]
      split_ifs <;> simp

private theorem zeta_mul_polynomialMu [DecidableLE α] [DecidableEq α] :
    (zeta ℤ[X] * polynomialMu : IncidenceAlgebra ℤ[X] α) = 1 := by
  classical
  apply IncidenceAlgebra.ext
  intro a b _
  rw [IncidenceAlgebra.mul_apply, IncidenceAlgebra.one_apply]
  calc
    (∑ c ∈ Icc a b, zeta ℤ[X] a c * polynomialMu c b) = ∑ c ∈ Icc a b, C (mu ℤ c b) := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [polynomialMu_apply, zeta_of_le (Finset.mem_Icc.mp hc).1, one_mul]
    _ = _ := by
      rw [← map_sum, sum_Icc_mu_left]
      split_ifs <;> simp

/-- The characteristic polynomial kernel, with its values given by the interval Möbius sums. -/
def intervalCharacteristic (rank : α → ℕ) : IncidenceAlgebra ℤ[X] α := by
  classical
  exact polynomialMu * rankMonomials rank

theorem intervalCharacteristic_apply (rank : α → ℕ) (a b : α) :
    intervalCharacteristic rank a b = by
      classical
      exact ∑ c ∈ Icc a b, C (mu ℤ a c) * X ^ (rank b - rank c) := by
  classical
  rw [intervalCharacteristic, IncidenceAlgebra.mul_apply]
  apply Finset.sum_congr rfl
  intro c hc
  rw [polynomialMu_apply, rankMonomials_apply rank (Finset.mem_Icc.mp hc).2]

variable [OrderTop α]

/-- A polynomial family encoded in the top column of the incidence algebra. -/
private def topColumn (p : α → ℤ[X]) : IncidenceAlgebra ℤ[X] α := by
  classical
  refine ⟨fun a b => if b = ⊤ then p a else 0, ?_⟩
  intro a b hab
  have hb : b ≠ ⊤ := fun h => hab (h ▸ le_top)
  simp [hb]

omit [LocallyFiniteOrder α] in
private theorem topColumn_apply (p : α → ℤ[X]) (a b : α) :
    topColumn p a b = by classical exact if b = ⊤ then p a else 0 := rfl

private theorem mul_topColumn (f : IncidenceAlgebra ℤ[X] α) (p : α → ℤ[X]) (a : α) :
    (f * topColumn p) a ⊤ = ∑ b ∈ Icc a ⊤, f a b * p b := by
  rw [IncidenceAlgebra.mul_apply]
  simp [topColumn_apply]

/-- The Z-polynomial of the interval starting at `a` for the polynomial family `p`. -/
def shiftedSum (rank : α → ℕ) (p : α → ℤ[X]) (a : α) : ℤ[X] :=
  (rankMonomials rank * topColumn p) a ⊤

theorem shiftedSum_apply (rank : α → ℕ) (p : α → ℤ[X]) (a : α) :
    shiftedSum rank p a = ∑ b ∈ Icc a ⊤, X ^ (rank b - rank a) * p b := by
  rw [shiftedSum, mul_topColumn]
  apply Finset.sum_congr rfl
  intro b hb
  rw [rankMonomials_apply rank (Finset.mem_Icc.mp hb).1]

private theorem reflect_shiftedSum (rank : α → ℕ) (hRank : Monotone rank) (p : α → ℤ[X])
    (hp : ∀ a, (p a).natDegree ≤ height rank a) (a : α) :
    (shiftedSum rank p a).reflect (height rank a) =
      ∑ b ∈ Icc a ⊤, (p b).reflect (height rank b) := by
  rw [shiftedSum_apply]
  have hsum : ∀ (s : Finset α) (f : α → ℤ[X]), (∑ b ∈ s, f b).reflect (height rank a) =
      ∑ b ∈ s, (f b).reflect (height rank a) := by
    intro s f
    ext i
    simp only [coeff_reflect, finsetSum_coeff]
  rw [hsum]
  apply Finset.sum_congr rfl
  intro b hb
  have hab := hRank (Finset.mem_Icc.mp hb).1
  have hbt := hRank (le_top : b ≤ ⊤)
  have h : height rank a = rank b - rank a + height rank b := by
    unfold height
    omega
  rw [h, reflect_mul _ _ (natDegree_X_pow_le _) (hp b)]
  simp [revAt_le]

/-- For any family with the required support, Z-palindromicity is equivalent to the
original characteristic-polynomial recurrence on every upper interval. -/
theorem palindrome_iff_characteristicRecurrence (rank : α → ℕ) (hRank : Monotone rank)
    (p : α → ℤ[X]) (hp : ∀ a, (p a).natDegree ≤ height rank a) :
    (∀ a, (shiftedSum rank p a).reflect (height rank a) = shiftedSum rank p a) ↔
      ∀ a, (p a).reflect (height rank a) =
        ∑ b ∈ Icc a ⊤, intervalCharacteristic rank a b * p b := by
  classical
  let reflFamily : α → ℤ[X] := fun a => (p a).reflect (height rank a)
  have hcolumn (f g : IncidenceAlgebra ℤ[X] α) (v w : α → ℤ[X]) :
      (∀ a, (f * topColumn v) a ⊤ = (g * topColumn w) a ⊤) ↔
        f * topColumn v = g * topColumn w := by
    constructor
    · intro h
      apply IncidenceAlgebra.ext
      intro a b _
      by_cases hb : b = ⊤
      · simpa only [hb] using h a
      · simp [IncidenceAlgebra.mul_apply, topColumn_apply, hb]
    · intro h a
      rw [h]
  have hcol (f : IncidenceAlgebra ℤ[X] α) (v w : α → ℤ[X]) :
      (∀ a, v a = (f * topColumn w) a ⊤) ↔ topColumn v = f * topColumn w := by
    simpa [one_mul, topColumn_apply] using hcolumn 1 f v w
  let ζ : IncidenceAlgebra ℤ[X] α := zeta ℤ[X]
  have hzeta (a : α) : (ζ * topColumn reflFamily) a ⊤ =
      ∑ b ∈ Icc a ⊤, reflFamily b := by
    rw [mul_topColumn]
    apply Finset.sum_congr rfl
    intro b hb
    dsimp only [ζ]
    rw [zeta_of_le (Finset.mem_Icc.mp hb).1, one_mul]
  have hpal : (∀ a, (shiftedSum rank p a).reflect (height rank a) = shiftedSum rank p a) ↔
      ζ * topColumn reflFamily = rankMonomials rank * topColumn p := by
    rw [← hcolumn ζ (rankMonomials rank) reflFamily p]
    simp_rw [hzeta, reflect_shiftedSum rank hRank p hp, shiftedSum]
    rfl
  have hrec : (∀ a, (p a).reflect (height rank a) =
      ∑ b ∈ Icc a ⊤, intervalCharacteristic rank a b * p b) ↔
      topColumn reflFamily = intervalCharacteristic rank * topColumn p := by
    rw [← hcol (intervalCharacteristic rank) reflFamily p]
    simp_rw [mul_topColumn]
    rfl
  rw [hpal, hrec]
  constructor
  · intro h
    have he := congrArg (fun f => polynomialMu * f) h
    simpa only [ζ, ← mul_assoc, polynomialMu_mul_zeta, one_mul, intervalCharacteristic] using he
  · intro h
    have he := congrArg (fun f => ζ * f) h
    simpa only [ζ, ← mul_assoc, intervalCharacteristic, zeta_mul_polynomialMu, one_mul] using he

theorem coeff_shiftedSum [Fintype α] (rank : α → ℕ) (p : α → ℤ[X]) (a : α) (i : ℕ) :
    (shiftedSum rank p a).coeff i = zCoeff rank (fun b j => (p b).coeff j) a i := by
  classical
  rw [shiftedSum_apply, finsetSum_coeff, Finset.Icc_eq_cons_Ioc (le_top : a ≤ ⊤),
    Finset.sum_cons, zCoeff, upperTail]
  simp only [Nat.sub_self, pow_zero, one_mul, coeff_X_pow_mul']
  congr 1
  exact Finset.sum_subtype _ (fun _ => by simp) _

theorem shiftedSum_reflect_of_isKLFamily [Fintype α] (rank : α → ℕ) (p : α → ℤ[X])
    (hp : IsKLFamily rank (fun a i => (p a).coeff i)) (a : α) :
    (shiftedSum rank p a).reflect (height rank a) = shiftedSum rank p a := by
  ext i
  rw [coeff_reflect, coeff_shiftedSum, coeff_shiftedSum]
  by_cases hi : i ≤ height rank a
  · rw [revAt_le hi, hp.zCoeff_palindrome rank a hi]
  · rw [revAt_eq_self_of_lt (Nat.lt_of_not_ge hi)]

#print axioms intervalCharacteristic_apply
#print axioms palindrome_iff_characteristicRecurrence
#print axioms coeff_shiftedSum
#print axioms shiftedSum_reflect_of_isKLFamily

end OpenMathResearch.MatroidKL
