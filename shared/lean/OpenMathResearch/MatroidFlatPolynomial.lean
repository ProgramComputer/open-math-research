import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.Fintype.Powerset
import OpenMathResearch.MatroidKL

/-!
# Rank and polynomial coefficients on Mathlib matroid flats

The flat rank is the natural-valued rank of Mathlib's finite matroid. The
bottom flat, which contains exactly the loops, has rank zero. The starting
flat in the recurrence can be any flat, so the same family also represents
the upper intervals needed for contraction.
-/

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

/-- Package the finite coefficient family into an integer polynomial. -/
def matroidZ [Finite α] (M : Matroid α) : ℤ[X] :=
  ∑ i ∈ Finset.range (M.eRank.toNat + 1), Polynomial.monomial i (matroidZCoeff M i)

@[simp] theorem coeff_matroidZ [Finite α] (M : Matroid α) (i : ℕ) :
    (matroidZ M).coeff i = matroidZCoeff M i := by
  classical
  change (Polynomial.lcoeff ℤ i) (matroidZ M) = _
  rw [matroidZ, map_sum, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Polynomial.coeff_monomial, hj]
  · intro hi
    have h : M.eRank.toNat < i := by
      simp only [Finset.mem_range, not_lt] at hi
      omega
    simp [matroidZCoeff_eq_zero_of_rank_lt M h]

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
#print axioms coeff_matroidZ
#print axioms matroidZ_of_rank_zero

end OpenMathResearch.MatroidKL
