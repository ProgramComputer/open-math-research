import OccupiedExpansion
import PairedExpProduct

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset Filter
open scoped PowerSeries Topology

def occupiedDistinct (k : ℕ) (C S : ℝ) (a : ℤ) : ℂ⟦X⟧ :=
  PowerSeries.rescale (pairedPoleDenom C S a)⁻¹ (cutoffCycleSeries k - 1)

def occupiedPrimitive (k : ℕ) (C S : ℝ) (a q : ℤ) : ℂ⟦X⟧ :=
  PowerSeries.C (R := ℂ) (pairedPoleDenom C S q/(pairedPoleDenom C S q-pairedPoleDenom C S a)) *
    PowerSeries.rescale (pairedPoleDenom C S q)⁻¹ ((cutoffCycleSeries k-1)*(1-PowerSeries.X))

private theorem vanishesBelow_cycle_minus_one (k : ℕ) : VanishesBelow k (cutoffCycleSeries k-1) := by
  intro n hn
  rw [map_sub, cutoffCycleSeries, coeff_cutoffExp (by omega : 0<k) (vanishesBelow_cutoffLog k),
    Nat.div_eq_of_lt hn]
  simp

private theorem vanishesBelow_cleared_cycle (k : ℕ) :
    VanishesBelow k ((cutoffCycleSeries k-1)*(1-PowerSeries.X)) := by
  intro n hn
  rw [PowerSeries.coeff_mul]
  apply sum_eq_zero
  intro a ha
  have hsum := mem_antidiagonal.mp ha
  rw [vanishesBelow_cycle_minus_one k a.1 (by omega), zero_mul]

private theorem off_inv_norm (C : ℝ) {S : ℝ} (hS : S ≠ 0) {a q : ℤ} (hqa : q ≠ a) :
    ‖(pairedPoleDenom C S q-pairedPoleDenom C S a)⁻¹‖ ≤ (2*|S|)⁻¹ := by
  have hone : (1:ℝ) ≤ |((q-a:ℤ):ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast (show (1:ℤ) ≤ |q-a| from Int.add_one_le_iff.mpr (abs_pos.mpr (sub_ne_zero.mpr hqa)))
  rw [norm_inv, pairedPoleDenom_sub, norm_mul, norm_mul, norm_mul, Complex.norm_I,
    one_mul, show ‖(2:ℂ)‖ = 2 by norm_num, ← Int.cast_sub, Complex.norm_intCast, Complex.norm_real,
    Real.norm_eq_abs]
  apply (inv_le_inv₀ (by positivity) (by positivity)).2
  nlinarith [mul_nonneg (sub_nonneg.mpr hone) (abs_nonneg S), abs_pos.mpr hS]

def polePowerBudget (N : ℕ) (C S : ℝ) (q : ℤ) : ℝ :=
  ∑ p ∈ Icc 2 N, ‖(pairedPoleDenom C S q)⁻¹‖^p

private theorem polePowerBudget_nonneg (N : ℕ) (C S : ℝ) (q : ℤ) :
    0 ≤ polePowerBudget N C S q := sum_nonneg (fun _ _ => by positivity)

private theorem summable_polePowerBudget (N : ℕ) (C : ℝ) {S : ℝ} (hS : S ≠ 0) :
    Summable (polePowerBudget N C S) := by
  exact summable_sum (fun p hp => summable_paired_pole_power_norm C hS (mem_Icc.mp hp).1)

private theorem pole_power_le_budget (N : ℕ) (C S : ℝ) (q : ℤ) {p : ℕ}
    (hp : 2 ≤ p) (hN : p ≤ N) :
    ‖(pairedPoleDenom C S q)⁻¹‖^p ≤ polePowerBudget N C S q :=
  single_le_sum (fun _ _ => by positivity) (mem_Icc.mpr ⟨hp,hN⟩)

private def coeffBudget (N : ℕ) (F : ℂ⟦X⟧) : ℝ :=
  ∑ j ∈ range (N+1), ‖PowerSeries.coeff (R := ℂ) j F‖

private theorem coeff_le_budget (N : ℕ) (F : ℂ⟦X⟧) {j : ℕ} (hj : j ≤ N) :
    ‖PowerSeries.coeff (R := ℂ) j F‖ ≤ coeffBudget N F :=
  single_le_sum (f := fun n => ‖PowerSeries.coeff (R := ℂ) n F‖)
    (fun _ _ => norm_nonneg _) (mem_range.mpr (Nat.lt_succ_of_le hj))

theorem summable_actual_occupiedCoeff {k : ℕ} (hk : 3 ≤ k) (N : ℕ) (C : ℝ) {S : ℝ}
    (hS : S ≠ 0) :
    Summable (fun i => ‖occupiedCoeff (occupiedDistinct k C S) (occupiedPrimitive k C S) N i‖) := by
  let D := cutoffCycleSeries k - 1
  let B := D*(1-PowerSeries.X)
  let u := fun a => coeffBudget N D*polePowerBudget N C S a
  let w := fun q => (coeffBudget N B*(2*|S|)⁻¹)*polePowerBudget N C S q
  have hD : 0 ≤ coeffBudget N D := sum_nonneg (fun _ _ => norm_nonneg _)
  have hB : 0 ≤ coeffBudget N B := sum_nonneg (fun _ _ => norm_nonneg _)
  have hu0 (a : ℤ) : 0 ≤ u a := mul_nonneg hD (polePowerBudget_nonneg N C S a)
  have hw0 (q : ℤ) : 0 ≤ w q :=
    mul_nonneg (mul_nonneg hB (by positivity)) (polePowerBudget_nonneg N C S q)
  have hs := summable_polePowerBudget N C hS
  apply summable_occupiedCoeff _ _ _ (hs.mul_left (coeffBudget N D))
    (hs.mul_left (coeffBudget N B*(2*|S|)⁻¹)) hu0 hw0
  · intro a n hn
    rw [occupiedDistinct, PowerSeries.coeff_rescale]
    change ‖((pairedPoleDenom C S a)⁻¹)^n*PowerSeries.coeff (R := ℂ) n D‖ ≤ u a
    by_cases hnk : n<k
    · rw [vanishesBelow_cycle_minus_one k n hnk, mul_zero, norm_zero]
      exact hu0 a
    · rw [norm_mul,norm_pow,mul_comm]
      exact mul_le_mul (coeff_le_budget N D hn) (pole_power_le_budget N C S a (by omega) hn)
        (by positivity) hD
  · intro a q hqa n hn
    by_cases hnk : n<k
    · rw [occupiedPrimitive, PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale,
        vanishesBelow_cleared_cycle k n hnk, mul_zero, mul_zero, norm_zero]
      exact hw0 q
    · obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
      rw [occupiedPrimitive, finite_cycle_primitive_coeff _ _
        (pairedPoleDenom_ne_zero C hS q), norm_mul,norm_div,norm_pow]
      change ‖(pairedPoleDenom C S q)⁻¹‖^j /
          ‖pairedPoleDenom C S q-pairedPoleDenom C S a‖ * ‖PowerSeries.coeff (R := ℂ) (j+1) B‖ ≤ w q
      rw [div_eq_mul_inv, ← norm_inv]
      have hp := pole_power_le_budget N C S q (by omega : 2 ≤ j) (by omega : j ≤ N)
      have hq := off_inv_norm C hS hqa
      have hb := coeff_le_budget N B hn
      have hm := mul_le_mul (mul_le_mul hp hq (norm_nonneg _) (polePowerBudget_nonneg N C S q))
        hb (norm_nonneg _) (mul_nonneg (polePowerBudget_nonneg N C S q) (by positivity))
      exact hm.trans_eq (by dsimp [w]; ring)

#print axioms summable_actual_occupiedCoeff
end OpenMathResearch.LongCycleExcedances
