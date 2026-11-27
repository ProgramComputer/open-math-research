import PairedCoefficientLimit
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Topology.Algebra.InfiniteSum.Ring

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset Filter
open scoped PowerSeries PowerSeries.WithPiTopology Topology

def VanishesBelow (k : ℕ) (F : ℂ⟦X⟧) : Prop :=
  ∀ n < k, PowerSeries.coeff (R := ℂ) n F = 0

theorem coeff_pow_of_lt_cutoff {F : ℂ⟦X⟧} {k : ℕ}
    (hF : VanishesBelow k F) {n j : ℕ} (h : n < j*k) :
    PowerSeries.coeff (R := ℂ) n (F^j) = 0 := by
  induction j generalizing n with
  | zero => simp at h
  | succ j ih =>
    rw [Nat.succ_mul] at h
    rw [pow_succ, PowerSeries.coeff_mul]
    apply sum_eq_zero
    intro a ha
    have hsum := mem_antidiagonal.mp ha
    by_cases hb : a.2 < k
    · rw [hF _ hb, mul_zero]
    · rw [ih (by omega), zero_mul]

def weightedPow (F : ℂ⟦X⟧) (j : ℕ) : ℂ⟦X⟧ :=
  PowerSeries.C (R := ℂ) ((j.factorial:ℂ)⁻¹)*F^j

theorem coeff_weightedPow_of_lt_cutoff {F : ℂ⟦X⟧} {k : ℕ}
    (hF : VanishesBelow k F) {n j : ℕ} (h : n < j*k) :
    PowerSeries.coeff (R := ℂ) n (weightedPow F j) = 0 := by
  rw [weightedPow, PowerSeries.coeff_C_mul, coeff_pow_of_lt_cutoff hF h, mul_zero]

theorem hasSum_weightedPow_coeff {F : ℂ⟦X⟧} {k : ℕ} (hk : 0 < k)
    (hF : VanishesBelow k F) (n : ℕ) :
    HasSum (fun j => PowerSeries.coeff (R := ℂ) n (weightedPow F j))
      (∑ j ∈ range (n/k+1), PowerSeries.coeff (R := ℂ) n (F^j)/(j.factorial:ℂ)) := by
  let s := range (n/k+1)
  let f := fun j => PowerSeries.coeff (R := ℂ) n (weightedPow F j)
  have hfinite : HasSum f (∑ j ∈ s, f j) := hasSum_sum_of_ne_finset_zero (by
    intro j hj
    apply coeff_weightedPow_of_lt_cutoff hF
    exact (Nat.div_lt_iff_lt_mul hk).mp (by simpa [s] using hj))
  have he : (∑ j ∈ s, f j) =
      ∑ j ∈ range (n/k+1), PowerSeries.coeff (R := ℂ) n (F^j)/(j.factorial:ℂ) := by
    apply sum_congr rfl
    intro j _
    rw [show f j = PowerSeries.coeff (R := ℂ) n (weightedPow F j) from rfl,
      weightedPow, PowerSeries.coeff_C_mul, div_eq_mul_inv, mul_comm]
  exact he ▸ hfinite

def cutoffExp (F : ℂ⟦X⟧) : ℂ⟦X⟧ := ∑' j, weightedPow F j

theorem hasSum_weightedPow {F : ℂ⟦X⟧} {k : ℕ} (hk : 0 < k)
    (hF : VanishesBelow k F) :
    HasSum (weightedPow F) (PowerSeries.mk fun n =>
      ∑ j ∈ range (n/k+1), PowerSeries.coeff (R := ℂ) n (F^j)/(j.factorial:ℂ)) := by
  rw [HasSum, PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
  intro n
  simpa only [HasSum, SummationFilter.unconditional, map_sum, PowerSeries.coeff_mk] using hasSum_weightedPow_coeff hk hF n

theorem coeff_cutoffExp {F : ℂ⟦X⟧} {k : ℕ} (hk : 0 < k)
    (hF : VanishesBelow k F) (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n (cutoffExp F) =
      ∑ j ∈ range (n/k+1), PowerSeries.coeff (R := ℂ) n (F^j)/(j.factorial:ℂ) := by
  rw [cutoffExp, (hasSum_weightedPow hk hF).tsum_eq, PowerSeries.coeff_mk]

#print axioms coeff_cutoffExp
end OpenMathResearch.LongCycleExcedances
