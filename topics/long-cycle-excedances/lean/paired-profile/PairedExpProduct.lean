import ExpAdd

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset Filter
open scoped PowerSeries PowerSeries.WithPiTopology Topology

def cutoffLog (k : ℕ) : ℂ⟦X⟧ :=
  PowerSeries.mk fun p => if k ≤ p then 1/(p:ℂ) else 0

/-- The formal cycle-probability factor D. Its exponent is ∑_{p≥k} X^p/p. -/
def cutoffCycleSeries (k : ℕ) : ℂ⟦X⟧ := cutoffExp (cutoffLog k)

theorem cutoffExp_zero : cutoffExp (0 : ℂ⟦X⟧) = 1 := by
  ext n
  rw [coeff_cutoffExp (k:=1) (by decide) (by intro i hi; simp)]
  rw [sum_eq_single 0]
  · simp
  · intro j _ hj
    simp [zero_pow hj]
  · simp

theorem vanishesBelow_cutoffLog (k : ℕ) : VanishesBelow k (cutoffLog k) := by
  intro n hn
  simp [cutoffLog, not_le_of_gt hn]

theorem vanishesBelow_rescale {k : ℕ} {F : ℂ⟦X⟧} (a : ℂ)
    (hF : VanishesBelow k F) : VanishesBelow k (PowerSeries.rescale a F) := by
  intro n hn
  rw [PowerSeries.coeff_rescale, hF n hn]
  simp

theorem cutoffExp_rescale {k : ℕ} {F : ℂ⟦X⟧} (hk : 0 < k)
    (hF : VanishesBelow k F) (a : ℂ) :
    cutoffExp (PowerSeries.rescale a F) = PowerSeries.rescale a (cutoffExp F) := by
  ext n
  rw [coeff_cutoffExp hk (vanishesBelow_rescale a hF), PowerSeries.coeff_rescale,
    coeff_cutoffExp hk hF, mul_sum]
  apply sum_congr rfl
  intro j _
  rw [← map_pow, PowerSeries.coeff_rescale]
  ring

theorem pairedCycleLog_eq_rescale (k : ℕ) (C S : ℝ) (q : ℤ) :
    pairedCycleLog k C S q =
      PowerSeries.rescale (pairedPoleDenom C S q)⁻¹ (cutoffLog k) := by
  ext p
  rw [pairedCycleLog, PowerSeries.coeff_mk, PowerSeries.coeff_rescale,
    cutoffLog, PowerSeries.coeff_mk]
  split <;> ring

theorem cutoffExp_sum {ι : Type*} (A : Finset ι) {F : ι → ℂ⟦X⟧} {k : ℕ}
    (hk : 0 < k) (hF : ∀ q, VanishesBelow k (F q)) :
    cutoffExp (∑ q ∈ A, F q) = ∏ q ∈ A, cutoffExp (F q) := by
  classical
  induction A using Finset.induction_on with
  | empty => simp [cutoffExp_zero]
  | @insert q A hq ih =>
    rw [sum_insert hq, prod_insert hq, cutoffExp_add hk (hF q), ih]
    intro n hn
    simp [hF _ n hn]

theorem finite_paired_product_eq_truncated_exp {k : ℕ} (hk : 0 < k)
    (A : Finset ℤ) (C S : ℝ) (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n (∏ q ∈ A,
      PowerSeries.rescale (pairedPoleDenom C S q)⁻¹ (cutoffCycleSeries k)) =
      ∑ h ∈ range (n/k+1), PowerSeries.coeff (R := ℂ) n
        ((∑ q ∈ A, pairedCycleLog k C S q)^h)/(h.factorial:ℂ) := by
  have hV (q : ℤ) : VanishesBelow k (pairedCycleLog k C S q) := by
    rw [pairedCycleLog_eq_rescale]
    exact vanishesBelow_rescale _ (vanishesBelow_cutoffLog k)
  have he (q : ℤ) : PowerSeries.rescale (pairedPoleDenom C S q)⁻¹ (cutoffCycleSeries k)
      = cutoffExp (pairedCycleLog k C S q) := by
    rw [pairedCycleLog_eq_rescale, cutoffExp_rescale hk (vanishesBelow_cutoffLog k)]
    rfl
  simp_rw [he]
  rw [← cutoffExp_sum A hk hV, coeff_cutoffExp hk]
  intro j hj
  simp [hV _ j hj]

/-- In degrees strictly below k the product has only its constant term. -/
theorem finite_paired_product_coeff_below_cutoff {k n : ℕ} (hn : n < k)
    (A : Finset ℤ) (C S : ℝ) :
    PowerSeries.coeff (R := ℂ) n (∏ q ∈ A,
      PowerSeries.rescale (pairedPoleDenom C S q)⁻¹ (cutoffCycleSeries k)) =
      if n = 0 then 1 else 0 := by
  rw [finite_paired_product_eq_truncated_exp (by omega : 0 < k),
    Nat.div_eq_of_lt hn]
  simp [PowerSeries.coeff_one]

#print axioms finite_paired_product_coeff_below_cutoff
#print axioms cutoffExp_rescale
#print axioms finite_paired_product_eq_truncated_exp
end OpenMathResearch.LongCycleExcedances
