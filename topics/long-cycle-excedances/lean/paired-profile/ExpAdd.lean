import CutoffFormalExp

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset Filter
open scoped PowerSeries PowerSeries.WithPiTopology Topology

theorem vanishesBelow_add {F G : ℂ⟦X⟧} {k : ℕ}
    (hF : VanishesBelow k F) (hG : VanishesBelow k G) : VanishesBelow k (F+G) := by
  intro n hn
  simp only [map_add, hF n hn, hG n hn, add_zero]

private theorem summable_weightedPow_product {F G : ℂ⟦X⟧} {k : ℕ} (hk : 0 < k)
    (hF : VanishesBelow k F) (hG : VanishesBelow k G) :
    Summable (fun a : ℕ × ℕ => weightedPow F a.1 * weightedPow G a.2) := by
  refine ⟨PowerSeries.mk (fun n => ∑ a ∈ (range (n/k+1)).product (range (n/k+1)),
    PowerSeries.coeff (R := ℂ) n (weightedPow F a.1 * weightedPow G a.2)), ?_⟩
  rw [HasSum, PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
  intro n
  have hfinite := hasSum_sum_of_ne_finset_zero
    (s := (range (n/k+1)).product (range (n/k+1)))
    (f := fun a : ℕ × ℕ => PowerSeries.coeff (R := ℂ) n (weightedPow F a.1 * weightedPow G a.2))
    (by
      intro a ha
      change PowerSeries.coeff (R := ℂ) n (weightedPow F a.1 * weightedPow G a.2) = 0
      rw [PowerSeries.coeff_mul]
      apply sum_eq_zero
      intro b hb
      have hab := mem_antidiagonal.mp hb
      by_cases h₁ : a.1 < n/k+1
      · have h₂ : n < a.2*k := (Nat.div_lt_iff_lt_mul hk).mp (by
          by_contra! hb
          exact ha (mem_product.mpr ⟨mem_range.mpr h₁, mem_range.mpr (by omega)⟩))
        rw [coeff_weightedPow_of_lt_cutoff hG (by omega : b.2 < a.2*k), mul_zero]
      · have h₁' : n < a.1*k := (Nat.div_lt_iff_lt_mul hk).mp (by omega)
        rw [coeff_weightedPow_of_lt_cutoff hF (by omega : b.1 < a.1*k), zero_mul])
  simpa only [HasSum, SummationFilter.unconditional, map_sum, PowerSeries.coeff_mk] using hfinite

private theorem weightedPow_add (F G : ℂ⟦X⟧) (n : ℕ) :
    weightedPow (F+G) n =
      ∑ a ∈ antidiagonal n, weightedPow F a.1 * weightedPow G a.2 := by
  rw [Nat.sum_antidiagonal_eq_sum_range_succ_mk, weightedPow, add_pow, mul_sum]
  apply sum_congr rfl
  intro a ha
  have han := Nat.lt_succ_iff.mp (mem_range.mp ha)
  have hfac : (n.choose a:ℂ)*(a.factorial:ℂ)*((n-a).factorial:ℂ) = (n.factorial:ℂ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial han
  have ha0 : (a.factorial:ℂ) ≠ 0 := by exact_mod_cast a.factorial_ne_zero
  have hb0 : ((n-a).factorial:ℂ) ≠ 0 := by exact_mod_cast (n-a).factorial_ne_zero
  have hc0 : (n.choose a:ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos han).ne'
  have hc : (n.factorial:ℂ)⁻¹*(n.choose a:ℂ) =
      (a.factorial:ℂ)⁻¹*((n-a).factorial:ℂ)⁻¹ := by
    rw [← hfac]
    field_simp [ha0,hb0,hc0] <;> ring
  simp only [weightedPow, ← map_natCast (PowerSeries.C ℂ)]
  calc
    _ = PowerSeries.C (R := ℂ) ((n.factorial:ℂ)⁻¹*(n.choose a:ℂ))*F^a*G^(n-a) := by
      rw [map_mul]
      ring
    _ = _ := by rw [hc, map_mul]; ring

theorem cutoffExp_add {F G : ℂ⟦X⟧} {k : ℕ} (hk : 0 < k)
    (hF : VanishesBelow k F) (hG : VanishesBelow k G) :
    cutoffExp (F+G) = cutoffExp F * cutoffExp G := by
  unfold cutoffExp
  rw [(hasSum_weightedPow hk hF).summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal
    (hasSum_weightedPow hk hG).summable (summable_weightedPow_product hk hF hG)]
  exact tsum_congr (weightedPow_add F G)

#print axioms cutoffExp_add
end OpenMathResearch.LongCycleExcedances
