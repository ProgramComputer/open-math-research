import PairedExpProduct
import CycleNumeratorVariation

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset
open scoped PowerSeries PowerSeries.WithPiTopology

/-- The coefficientwise Euler derivative. -/
private def degreeWeight (F : ℂ⟦X⟧) : ℂ⟦X⟧ :=
  PowerSeries.mk fun n => (n:ℂ)*PowerSeries.coeff (R := ℂ) n F

private theorem coeff_degreeWeight (F : ℂ⟦X⟧) (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n (degreeWeight F) = (n:ℂ)*PowerSeries.coeff (R := ℂ) n F := by
  rw [degreeWeight,PowerSeries.coeff_mk]

private theorem degreeWeight_C (a : ℂ) :
    degreeWeight (PowerSeries.C (R := ℂ) a) = 0 := by
  ext n
  rw [coeff_degreeWeight,PowerSeries.coeff_C,map_zero]
  split_ifs with h
  · simp [h]
  · simp

private theorem degreeWeight_mul (F G : ℂ⟦X⟧) :
    degreeWeight (F*G) = degreeWeight F*G+F*degreeWeight G := by
  ext n
  rw [coeff_degreeWeight,PowerSeries.coeff_mul,map_add,PowerSeries.coeff_mul,
    PowerSeries.coeff_mul,mul_sum,←sum_add_distrib]
  apply sum_congr rfl
  intro a ha
  have he : (n:ℂ) = (a.1:ℂ)+(a.2:ℂ) := by exact_mod_cast (mem_antidiagonal.mp ha).symm
  rw [coeff_degreeWeight,coeff_degreeWeight,he]
  ring

private theorem degreeWeight_pow_succ (F : ℂ⟦X⟧) (j : ℕ) :
    degreeWeight (F^(j+1)) = PowerSeries.C (R := ℂ) ((j+1:ℕ):ℂ) * F^j * degreeWeight F := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ F j.succ,degreeWeight_mul,ih]
    have he : PowerSeries.C (R := ℂ) ((j+1:ℕ):ℂ)+1 = PowerSeries.C (R := ℂ) ((j.succ+1:ℕ):ℂ) := by
      rw [←(PowerSeries.C (R := ℂ)).map_one,←map_add]
      push_cast
      rfl
    rw [←he,pow_succ F j]
    ring

private theorem degreeWeight_weightedPow_succ (F : ℂ⟦X⟧) (j : ℕ) :
    degreeWeight (weightedPow F (j+1)) = weightedPow F j * degreeWeight F := by
  have hj : (((j+1:ℕ):ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have he : (((j+1).factorial:ℂ))⁻¹ * ((j+1:ℕ):ℂ) = (j.factorial:ℂ)⁻¹ := by
    rw [Nat.factorial_succ,Nat.cast_mul,mul_inv]
    calc
      _ = ((((j+1:ℕ):ℂ))⁻¹*((j+1:ℕ):ℂ))*(j.factorial:ℂ)⁻¹ := by ring
      _ = _ := by rw [inv_mul_cancel₀ hj,one_mul]
  rw [weightedPow,degreeWeight_mul,degreeWeight_C,zero_mul,zero_add,
    degreeWeight_pow_succ,weightedPow,←mul_assoc,←mul_assoc,←map_mul,he,mul_assoc]

private theorem degreeWeight_cutoffExp {F : ℂ⟦X⟧} {k : ℕ}
    (hk : 0 < k) (hF : VanishesBelow k F) :
    degreeWeight (cutoffExp F) = cutoffExp F * degreeWeight F := by
  ext n
  let c := PowerSeries.coeff (R := ℂ) n
  have hs : HasSum (weightedPow F) (cutoffExp F) := by
    have hw := hasSum_weightedPow hk hF
    rw [cutoffExp,hw.tsum_eq]
    exact hw
  have hL : HasSum (fun j => c (degreeWeight (weightedPow F j))) (c (degreeWeight (cutoffExp F))) := by
    have he := (hs.map c (PowerSeries.WithPiTopology.continuous_coeff (R := ℂ) n)).mul_left (n:ℂ)
    simpa only [c,Function.comp_apply,coeff_degreeWeight] using he
  have hR : HasSum (fun j => c (weightedPow F j * degreeWeight F))
      (c (cutoffExp F * degreeWeight F)) :=
    (hs.mul_right (degreeWeight F)).map c (PowerSeries.WithPiTopology.continuous_coeff (R := ℂ) n)
  change c (degreeWeight (cutoffExp F)) = c (cutoffExp F*degreeWeight F)
  rw [←hL.tsum_eq,hL.summable.tsum_eq_zero_add]
  have hzero : weightedPow F 0 = PowerSeries.C (R := ℂ) 1 := by simp [weightedPow]
  rw [hzero,degreeWeight_C,map_zero,zero_add]
  simpa only [degreeWeight_weightedPow_succ] using hR.tsum_eq

private theorem coeff_degreeWeight_cutoffLog {k : ℕ} (hk : 0 < k) (p : ℕ) :
    PowerSeries.coeff (R := ℂ) p (degreeWeight (cutoffLog k)) = if k ≤ p then 1 else 0 := by
  rw [coeff_degreeWeight,cutoffLog,PowerSeries.coeff_mk]
  split_ifs with hp
  · have hn : (p:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [mul_one_div,div_self hn]
  · rw [mul_zero]

/-- Coefficient recurrence for the actual formal exponential used by the
paired profile. -/
theorem cutoffCycleSeries_coeff_recurrence {k n : ℕ} (hk : 0 < k) (hn : k ≤ n) :
    (n:ℂ)*PowerSeries.coeff (R := ℂ) n (cutoffCycleSeries k) =
      ∑ j ∈ range (n-k+1), PowerSeries.coeff (R := ℂ) j (cutoffCycleSeries k) := by
  rw [←coeff_degreeWeight,cutoffCycleSeries,degreeWeight_cutoffExp hk (vanishesBelow_cutoffLog k),
    PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => PowerSeries.coeff (R := ℂ) i (cutoffExp (cutoffLog k)) *
        PowerSeries.coeff (R := ℂ) j (degreeWeight (cutoffLog k)))]
  simp_rw [coeff_degreeWeight_cutoffLog hk]
  symm
  calc
    _ = ∑ j ∈ range (n-k+1), PowerSeries.coeff (R := ℂ) j (cutoffExp (cutoffLog k)) *
        (if k ≤ n-j then 1 else 0) := by
      apply sum_congr rfl
      intro j hj
      rw [if_pos (by have := mem_range.mp hj; omega : k ≤ n-j),mul_one]
    _ = _ := by
      apply sum_subset (range_mono (by omega))
      intro j hj hj'
      rw [if_neg (by have := not_lt.mp (fun hh => hj' (mem_range.mpr hh)); omega : ¬k ≤ n-j),mul_zero]

/-- The anchored probability specification uniquely determines each
coefficient of the cutoff formal exponential. -/
theorem coeff_cutoffCycleSeries_eq_of_spec {k : ℕ} {d : ℕ → ℝ}
    (hd : CycleProbability.Spec k d) (hk : 0 < k) (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n (cutoffCycleSeries k) = (d n:ℂ) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hz : n = 0
    · subst n
      rw [hd.zero,cutoffCycleSeries,coeff_cutoffExp hk (vanishesBelow_cutoffLog k)]
      simp
    by_cases hn : n < k
    · rw [hd.small n (Nat.pos_of_ne_zero hz) hn,cutoffCycleSeries,
        coeff_cutoffExp hk (vanishesBelow_cutoffLog k),Nat.div_eq_of_lt hn]
      simp [PowerSeries.coeff_one,hz]
    have hkn := not_lt.mp hn
    have hr := cutoffCycleSeries_coeff_recurrence hk hkn
    have hsum : (∑ j ∈ range (n-k+1), PowerSeries.coeff (R := ℂ) j (cutoffCycleSeries k)) =
        ∑ j ∈ range (n-k+1), (d j:ℂ) := by
      apply sum_congr rfl
      intro j hj
      exact ih j (by have := mem_range.mp hj; omega)
    rw [hsum] at hr
    have hb := congrArg Complex.ofReal (hd.recurrence n hkn)
    rw [Complex.ofReal_mul,Complex.ofReal_natCast,Complex.ofReal_sum] at hb
    exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr hz) (hr.trans hb.symm)

/-- The numerator series in the actual occupied-pole resummation. -/
def cutoffCycleNumerator (k : ℕ) : ℂ⟦X⟧ :=
  (cutoffCycleSeries k-1)*(1-PowerSeries.X)

/-- The numerator coefficients are the differences after removing the
constant probability mass. -/
theorem coeff_cutoffCycleNumerator_eq_of_spec {k s : ℕ} {d : ℕ → ℝ}
    (hd : CycleProbability.Spec k d) (hk : 0 < k) :
    PowerSeries.coeff (R := ℂ) s (cutoffCycleNumerator k) =
      (CycleProbability.numeratorDiff k d s:ℂ) := by
  have he (p : ℕ) : PowerSeries.coeff (R := ℂ) p (cutoffCycleSeries k-1) =
      (CycleProbability.cutoffWeight k d p:ℂ) := by
    rw [map_sub,coeff_cutoffCycleSeries_eq_of_spec hd hk,PowerSeries.coeff_one,
      CycleProbability.cutoffWeight]
    by_cases hp : k ≤ p
    · simp [hp,show p ≠ 0 by omega]
    · by_cases hz : p = 0
      · simp [hz,hd.zero,show ¬k ≤ 0 by omega]
      · simp [hp,hz,hd.small p (Nat.pos_of_ne_zero hz) (by omega)]
  have hX := PowerSeries.coeff_mul_X_pow' (cutoffCycleSeries k-1) 1 s
  simp only [pow_one] at hX
  rw [cutoffCycleNumerator,mul_sub,mul_one,map_sub,hX,he,
    CycleProbability.numeratorDiff,Complex.ofReal_sub]
  split_ifs with hs
  · rw [he]
  · have hz : s-1 < k := by omega
    simp [CycleProbability.cutoffWeight,show ¬k ≤ s-1 by omega]

#print axioms cutoffCycleSeries_coeff_recurrence
#print axioms coeff_cutoffCycleSeries_eq_of_spec
#print axioms coeff_cutoffCycleNumerator_eq_of_spec
end OpenMathResearch.LongCycleExcedances
