import MarkedCoefficientComparison

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset Polynomial

/-- Joint support and positivity of the full product, including the empty factor. -/
theorem marked_product_geometry {ι : Type*} (A : Finset ι) {k : ℕ} (hk : 0 < k) (N : ℕ)
    (c : ι → ℕ→ℝ) (hc : ∀ q ∈ A, ∀ d, 0 ≤ c q d) :
    let P := ∏ q ∈ A, (1+markDegreeBin k N (c q))
    (∀ b d, 0 ≤ (P.coeff b).coeff d) ∧
      ∀ b d, (P.coeff b).coeff d ≠ 0 → 4*d ≤ k*b ∧ k*b ≤ 5*d :=
  ⟨marked_full_nonnegative A k N c hc,marked_full_degree_support A hk N c⟩

private theorem sum_initial_le_eval (p : ℝ[X]) (N : ℕ) (hp : ∀ t, 0 ≤ p.coeff t) :
    ∑ t ∈ range (N+1), p.coeff t ≤ p.eval 1 := by
  rw [eval_eq_sum_range' (n:=max N p.natDegree + 1) (by omega)]
  simp only [one_pow,mul_one]
  exact sum_le_sum_of_subset_of_nonneg (range_mono (by omega)) (fun t _ _ => hp t)

/-- Weighted degree masses can be summed once per total bin. The pointwise
comparison is needed only on the actual joint degree/bin support. -/
theorem weighted_marked_cost (P : ℝ[X][X]) (N : ℕ) (weight budget : ℕ→ℝ)
    (hp : ∀ b t, 0 ≤ (P.coeff b).coeff t)
    (hb : ∀ b, 0 ≤ budget b)
    (hw : ∀ b t, t ≤ N → (P.coeff b).coeff t ≠ 0 → weight t ≤ budget b) :
    (∑ t ∈ range (N+1), weight t*(P.eval 1).coeff t) ≤
      ∑ b ∈ range (P.natDegree+1), budget b*(forgetDegree P).coeff b := by
  rw [eval_eq_sum_range (p:=P)]
  simp only [one_pow,mul_one,finsetSum_coeff,mul_sum]
  rw [sum_comm]
  apply sum_le_sum
  intro b _
  calc
    _ ≤ ∑ t ∈ range (N+1), budget b*(P.coeff b).coeff t := by
      apply sum_le_sum
      intro t ht
      by_cases h : (P.coeff b).coeff t=0
      · simp [h]
      · exact mul_le_mul_of_nonneg_right (hw b t (by have := mem_range.mp ht; omega) h) (hp b t)
    _ = budget b*∑ t ∈ range (N+1), (P.coeff b).coeff t := (mul_sum ..).symm
    _ ≤ _ := by
      rw [forgetDegree,coeff_map]
      exact mul_le_mul_of_nonneg_left (sum_initial_le_eval _ _ (hp b)) (hb b)

#print axioms marked_product_geometry
#print axioms weighted_marked_cost
end OpenMathResearch.LongCycleExcedances
