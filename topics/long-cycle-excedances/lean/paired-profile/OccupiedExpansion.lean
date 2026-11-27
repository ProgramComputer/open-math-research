import OccupiedCoefficient

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Filter Finset
open scoped Topology PowerSeries

variable {ι : Type*} [DecidableEq ι]

theorem finite_occupiedCoeff_sum (A : Finset ι)
    (P : ι → ℂ⟦X⟧) (B : ι → ι → ℂ⟦X⟧) (N : ℕ) :
    (∑ a ∈ A, PowerSeries.coeff (R := ℂ) N (P a * ∏ q ∈ A.erase a, (1+B a q))) =
      ∑ i ∈ A.product A.powerset, occupiedCoeff P B N i := by
  refine Eq.trans ?_ (sum_product A A.powerset (occupiedCoeff P B N)).symm
  apply sum_congr rfl
  intro a _
  simp only [prod_one_add, mul_sum, map_sum]
  have hs : (A.erase a).powerset = A.powerset.filter (fun s => a ∉ s) := by
    ext s
    simp only [mem_powerset, mem_filter]
    constructor
    · intro h
      exact ⟨h.trans (erase_subset _ _), fun ha => (mem_erase.mp (h ha)).1 rfl⟩
    · rintro ⟨h,ha⟩ i hi
      exact mem_erase.mpr ⟨fun he => ha (he ▸ hi),h hi⟩
  rw [hs, sum_filter]
  apply sum_congr rfl
  intro s _
  by_cases ha : a ∈ s <;> simp [occupiedCoeff, ha]

theorem tendsto_occupiedCoeff_sum (P : ι → ℂ⟦X⟧) (B : ι → ι → ℂ⟦X⟧)
    (N : ℕ) (hs : Summable (fun i => ‖occupiedCoeff P B N i‖)) :
    Tendsto (fun A : Finset ι =>
      ∑ a ∈ A, PowerSeries.coeff (R := ℂ) N (P a * ∏ q ∈ A.erase a, (1+B a q))) atTop
      (𝓝 (∑' i, occupiedCoeff P B N i)) := by
  simp_rw [finite_occupiedCoeff_sum]
  apply hasSum_comp_finite_support (Summable.of_norm hs).hasSum
    (fun i => insert i.1 i.2) (fun A => A.product A.powerset)
  rintro A ⟨a,s⟩
  simp [insert_subset_iff]

#print axioms finite_occupiedCoeff_sum
#print axioms tendsto_occupiedCoeff_sum
end OpenMathResearch.LongCycleExcedances
