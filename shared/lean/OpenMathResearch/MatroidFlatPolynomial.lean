import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.Fintype.Powerset
import OpenMathResearch.MatroidKLRecurrence

/-!
# Rank and polynomial coefficients on Mathlib matroid flats

The flat rank is the natural-valued rank of Mathlib's finite matroid. The
bottom flat, which contains exactly the loops, has rank zero. The starting
flat in the recurrence can be any flat, so the same family also represents
the upper intervals needed for contraction.
-/

open Finset Polynomial
open scoped BigOperators Polynomial

noncomputable section

namespace OpenMathResearch.MatroidKL

variable {α : Type*}

/-- The finite poset of Mathlib matroid flats, ordered by inclusion. -/
abbrev Flat (M : Matroid α) := {F : Set α // M.IsFlat F}

instance instOrderTopFlat (M : Matroid α) : OrderTop (Flat M) where
  top := ⟨M.E, M.ground_isFlat⟩
  le_top F := F.property.subset_ground

instance instOrderBotFlat (M : Matroid α) : OrderBot (Flat M) where
  bot := ⟨M.closure ∅, M.isFlat_closure (X := ∅)⟩
  bot_le F := by
    change M.closure ∅ ⊆ F.val
    rw [← F.property.closure]
    exact M.closure_mono (Set.empty_subset _)

instance instFintypeFlat [Finite α] (M : Matroid α) : Fintype (Flat M) :=
  Fintype.ofFinite _

instance instLocallyFiniteOrderFlat [Finite α] (M : Matroid α) : LocallyFiniteOrder (Flat M) :=
  LocallyFiniteOrder.ofFiniteIcc fun _ _ => Set.toFinite _

/-- The natural-valued rank of a flat of a finite matroid. -/
def flatRank (M : Matroid α) (F : Flat M) : ℕ := (M.eRk F.val).toNat

@[simp] theorem flatRank_top (M : Matroid α) : flatRank M ⊤ = M.eRank.toNat := by
  change (M.eRk M.E).toNat = M.eRank.toNat
  rw [M.eRk_ground]

@[simp] theorem flatRank_bot (M : Matroid α) : flatRank M ⊥ = 0 := by
  change (M.eRk (M.closure ∅)).toNat = 0
  rw [M.eRk_closure_eq, M.eRk_empty]
  rfl

theorem strictMono_flatRank [Finite α] (M : Matroid α) : StrictMono (flatRank M) := by
  intro F G hFG
  obtain ⟨I, hI⟩ := M.exists_isBasis F.val F.property.subset_ground
  obtain ⟨J, hJ, hIJ⟩ := hI.indep.subset_isBasis_of_subset
    (hI.subset.trans (show F.val ⊆ G.val from hFG.le)) G.property.subset_ground
  have hne : I ≠ J := by
    intro h
    have heq := congrArg M.closure h
    rw [hI.closure_eq_closure, hJ.closure_eq_closure, F.property.closure, G.property.closure] at heq
    exact hFG.ne (Subtype.ext heq)
  change (M.eRk F.val).toNat < (M.eRk G.val).toNat
  rw [← hI.encard_eq_eRk, ← hJ.encard_eq_eRk]
  exact Set.ncard_lt_ncard (lt_of_le_of_ne hIJ hne)

/-- The coefficient family from palindromicity on the ranked flat poset. -/
def flatKLCoeff [Finite α] (M : Matroid α) : Flat M → ℕ → ℤ :=
  klCoeff (flatRank M) (strictMono_flatRank M)

theorem flatKLCoeff_isKLFamily [Finite α] (M : Matroid α) :
    IsKLFamily (flatRank M) (flatKLCoeff M) :=
  klCoeff_isKLFamily _ _

/-- The Z-sum on the entire ranked flat poset. -/
def matroidZCoeff [Finite α] (M : Matroid α) (i : ℕ) : ℤ :=
  zCoeff (flatRank M) (flatKLCoeff M) ⊥ i

theorem matroidZCoeff_palindrome [Finite α] (M : Matroid α) {i : ℕ} (hi : i ≤ M.eRank.toNat) :
    matroidZCoeff M i = matroidZCoeff M (M.eRank.toNat - i) := by
  have h := (flatKLCoeff_isKLFamily M).zCoeff_palindrome (flatRank M) (⊥ : Flat M) (i := i)
  simpa [matroidZCoeff, height] using h (by simpa [height] using hi)

theorem matroidZCoeff_eq_zero_of_rank_lt [Finite α] (M : Matroid α) {i : ℕ}
    (hi : M.eRank.toNat < i) : matroidZCoeff M i = 0 := by
  apply (flatKLCoeff_isKLFamily M).zCoeff_eq_zero_of_height_lt (flatRank M) (strictMono_flatRank M)
  simpa [height] using hi

private def polynomialFromCoeffs (bound : ℕ) (f : ℕ → ℤ) : ℤ[X] :=
  ∑ i ∈ Finset.range (bound + 1), Polynomial.monomial i (f i)

private theorem coeff_polynomialFromCoeffs (bound : ℕ) (f : ℕ → ℤ)
    (hSupp : ∀ i, bound < i → f i = 0) (i : ℕ) :
    (polynomialFromCoeffs bound f).coeff i = f i := by
  classical
  change (Polynomial.lcoeff ℤ i) (polynomialFromCoeffs bound f) = _
  rw [polynomialFromCoeffs, map_sum, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Polynomial.coeff_monomial, hj]
  · intro hi
    have h : bound < i := by
      simp only [Finset.mem_range, not_lt] at hi
      omega
    simp [hSupp i h]

/-- The integer polynomial family on the upper intervals of Mathlib matroid flats. -/
def flatKL [Finite α] (M : Matroid α) (F : Flat M) : ℤ[X] :=
  polynomialFromCoeffs (height (flatRank M) F) (flatKLCoeff M F)

@[simp] theorem coeff_flatKL [Finite α] (M : Matroid α) (F : Flat M) (i : ℕ) :
    (flatKL M F).coeff i = flatKLCoeff M F i := by
  apply coeff_polynomialFromCoeffs
  intro j hj
  exact (flatKLCoeff_isKLFamily M).coeff_eq_zero_of_height_lt (flatRank M) F hj

theorem flatKL_characteristicRecurrence [Finite α] (M : Matroid α) (F : Flat M) :
    (flatKL M F).reflect (height (flatRank M) F) =
      ∑ G ∈ Icc F ⊤, intervalCharacteristic (flatRank M) F G * flatKL M G := by
  have hDegree (G : Flat M) : (flatKL M G).natDegree ≤ height (flatRank M) G := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    rw [coeff_flatKL]
    exact (flatKLCoeff_isKLFamily M).coeff_eq_zero_of_height_lt (flatRank M) G hi
  apply (palindrome_iff_characteristicRecurrence (flatRank M) (strictMono_flatRank M).monotone
    (flatKL M) hDegree).mp _ F
  apply shiftedSum_reflect_of_isKLFamily
  simpa only [coeff_flatKL] using flatKLCoeff_isKLFamily M

/-- Package the finite Z-coefficient family into an integer polynomial. -/
def matroidZ [Finite α] (M : Matroid α) : ℤ[X] :=
  polynomialFromCoeffs M.eRank.toNat (matroidZCoeff M)

@[simp] theorem coeff_matroidZ [Finite α] (M : Matroid α) (i : ℕ) :
    (matroidZ M).coeff i = matroidZCoeff M i :=
  coeff_polynomialFromCoeffs _ _ (fun _ hi => matroidZCoeff_eq_zero_of_rank_lt M hi) i

/-- The finite Z-polynomial agrees with the sum of the rank-shifted upper interval polynomials. -/
theorem matroidZ_eq_sum [Finite α] (M : Matroid α) :
    matroidZ M = ∑ F : Flat M, X ^ flatRank M F * flatKL M F := by
  have h : matroidZ M = shiftedSum (flatRank M) (flatKL M) (⊥ : Flat M) := by
    ext i
    simp [coeff_shiftedSum, matroidZCoeff]
  have hall : Icc (⊥ : Flat M) ⊤ = Finset.univ := by
    ext F
    simp
  simpa [shiftedSum_apply, hall] using h

theorem matroidZ_of_rank_zero [Finite α] (M : Matroid α) (hM : M.eRank.toNat = 0) :
    matroidZ M = 1 := by
  ext i
  rw [coeff_matroidZ]
  have hi : height (flatRank M) (⊥ : Flat M) = 0 := by simp [height, hM]
  rw [matroidZCoeff, (flatKLCoeff_isKLFamily M).zCoeff_of_rank_zero _
    (strictMono_flatRank M) _ hi]
  simp [Polynomial.coeff_one]

#print axioms strictMono_flatRank
#print axioms flatKLCoeff_isKLFamily
#print axioms matroidZCoeff_palindrome
#print axioms coeff_flatKL
#print axioms flatKL_characteristicRecurrence
#print axioms coeff_matroidZ
#print axioms matroidZ_eq_sum
#print axioms matroidZ_of_rank_zero

end OpenMathResearch.MatroidKL
