import FrontNormAlgebra
import Mathlib.Algebra.Order.Field.GeomSum

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset Polynomial

/-- A finite family with distinct ranks is bounded by the geometric tail,
independently of its last index and of any omitted ranks. -/
theorem front_finite_geometric_bound (s : Finset ℕ) (ρ C : ℝ) (m : ℕ)
    (hρ : 0 ≤ ρ) (hρ' : ρ < 1) (hC : 0 ≤ C) (rank : ℕ → ℕ)
    (hr : ∀ j ∈ s, m ≤ rank j) (hinj : Set.InjOn rank ↑s)
    (a : ℕ → ℝ) (ha : ∀ j ∈ s, a j ≤ C*ρ^(rank j)) :
    (∑ j ∈ s, a j) ≤ C*(ρ^m/(1-ρ)) := by
  let N := s.sup rank+1
  have hsub : s.image rank ⊆ Ico m N := by
    intro j hj
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hj
    exact mem_Ico.mpr ⟨hr i hi, Nat.lt_succ_of_le (le_sup hi)⟩
  calc
    _ ≤ ∑ j ∈ s, C*ρ^(rank j) := sum_le_sum ha
    _ = C*∑ j ∈ s.image rank, ρ^j := by
      rw [mul_sum, sum_image]
      exact fun _ hi _ hj he => hinj hi hj he
    _ ≤ C*∑ j ∈ Ico m N, ρ^j := mul_le_mul_of_nonneg_left
      (sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => pow_nonneg hρ _)) hC
    _ ≤ _ := mul_le_mul_of_nonneg_left (geom_sum_Ico_le_of_lt_one hρ hρ') hC

/-- Convert left and right weighted coefficient envelopes to the norm
after cancellation of the two central coefficients. -/
theorem front_norm_of_two_geometric_tails (P : ℝ[X]) {h : ℕ} {L U C₀ C₁ ρ : ℝ}
    (hρ : 0 ≤ ρ) (hρ' : ρ < 1) (h₀ : 0 ≤ C₀) (h₁ : 0 ≤ C₁)
    (hc : P.coeff h = 0) (hc' : P.coeff (h+1) = 0)
    (hleft : ∀ j < h, |P.coeff j| *frontCoefficientWeight h L U j ≤ C₀*ρ^(h-j))
    (hright : ∀ j, h+1 < j → |P.coeff j| *frontCoefficientWeight h L U j ≤ C₁*ρ^(j-(h+1))) :
    frontCoefficientNorm P h L U ≤ (C₀+C₁)*(ρ/(1-ρ)) := by
  let t (j : ℕ) := |P.coeff j| *frontCoefficientWeight h L U j
  let s₀ := P.support.filter (fun j => j < h)
  let s₁ := P.support.filter (fun j => ¬ j < h)
  have hsum : (∑ j ∈ s₀, t j) + (∑ j ∈ s₁, t j) = frontCoefficientNorm P h L U :=
    sum_filter_add_sum_filter_not _ _ _
  have hl := front_finite_geometric_bound s₀ ρ C₀ 1 hρ hρ' h₀ (h-·)
    (fun j hj => by change 1 ≤ h-j; have := (mem_filter.mp hj).2; omega)
    (fun j hj k hk he => by
      change h-j = h-k at he
      have := (mem_filter.mp hj).2
      have := (mem_filter.mp hk).2
      omega)
    t (fun j hj => hleft j (mem_filter.mp hj).2)
  have hr := front_finite_geometric_bound s₁ ρ C₁ 1 hρ hρ' h₁ (·-(h+1))
    (fun j hj => by
      change 1 ≤ j-(h+1)
      obtain ⟨hs, hle⟩ := mem_filter.mp hj
      have hn := mem_support_iff.mp hs
      have he : j ≠ h := fun e => hn (e ▸ hc)
      have he' : j ≠ h+1 := fun e => hn (e ▸ hc')
      omega)
    (fun j hj k hk he => by
      change j-(h+1) = k-(h+1) at he
      obtain ⟨hs, hle⟩ := mem_filter.mp hj
      obtain ⟨ht, hle'⟩ := mem_filter.mp hk
      have hj' : j ≠ h := fun e => (mem_support_iff.mp hs) (e ▸ hc)
      have hk' : k ≠ h := fun e => (mem_support_iff.mp ht) (e ▸ hc)
      omega)
    t (fun j hj => by
      obtain ⟨hs, hle⟩ := mem_filter.mp hj
      have hj' : j ≠ h := fun e => (mem_support_iff.mp hs) (e ▸ hc)
      have hj'' : j ≠ h+1 := fun e => (mem_support_iff.mp hs) (e ▸ hc')
      exact hright j (by omega))
  rw [←hsum, add_mul]
  simpa only [pow_one] using add_le_add hl hr

#print axioms front_finite_geometric_bound
#print axioms front_norm_of_two_geometric_tails
end OpenMathResearch.LongCycleExcedances
