import ResidualLagGrid
import RepositoryColorAlpha
import RepositoryLoadLag

set_option autoImplicit false
noncomputable section
namespace RepositoryQuotientAudit
open LongCycles PowerSeries Finset OpenMathResearch.LongCycleExcedances
open OpenMathResearch.LongCycleExcedances.ColorAnchor

/-- Delete one exponent from the number of residual colors using
the acceptance bound; the estimate also includes zero residual colors. -/
theorem original_residual_count_bound {m i k : ℕ} (hk : 2 ≤ k)
    (hkm : k ≤ m) (hs : 100*i ≤ m) :
    realCount m i k ≤ (151/(100*(k:ℝ)))*(m:ℝ)*(i:ℝ)^(m-1) := by
  have hm0 : 0 < m := by omega
  rcases Nat.eq_zero_or_pos i with rfl|hi
  · have h := (realCount_bounds m 0 k).2
    simp only [Nat.cast_zero,zero_pow hm0.ne'] at h
    exact h.trans (by positivity)
  · have hk0 : 0 < k := by omega
    have hmR : (0:ℝ) < m := Nat.cast_pos.mpr hm0
    have hiR : (0:ℝ) < i := Nat.cast_pos.mpr hi
    have hkR : (0:ℝ) < k := Nat.cast_pos.mpr hk0
    have h := (original_front_acceptance_upper hi hk0 hkm hs).2
    have hbound := (div_le_iff₀ (pow_pos hiR m)).mp h
    have hpow : (i:ℝ)^m=(i:ℝ)^(m-1)*i := by
      rw [←pow_succ, Nat.sub_add_cancel hm0]
    apply hbound.trans_eq
    rw [hpow]
    field_simp
    <;> ring

/-- An independent second grid bound for the same literal coefficient.
Here n−1 is the sample size of the binomial grid. -/
theorem original_lag_residual_grid {n k p : ℕ} (hk : 2 ≤ k) (hp : 0 < p)
    (hhalf : 2*k ≤ n+1) (hs : 200*p ≤ n) :
    (((k:ℝ)*p)/n)*((originalFrontLag n k).coeff p/(p:ℝ)^n) ≤
      (151/100)* ∑ j ∈ range (p+1), colorLoad (n-1) (k-1) ((j:ℝ)/p) := by
  obtain ⟨N,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
  let d := k-1
  let m := N+1+1-k
  have hd : d ≤ N := by dsimp [d]; omega
  have hkm : k ≤ m := by dsimp [m]; omega
  have hm0 : 0 < m := by omega
  have hm : N-d+1=m := by dsimp [m,d]; omega
  have hraw := (original_color_successor_lag (n:=N+1) hk p).2
  rw [original_color_successor_exact hk (by omega : k ≤ N+1+1) p] at hraw
  have hres := color_lag_residual_grid hd hp
    (fun i => coeff (R:=ℝ) i (colorTransform m (enumerator m k)))
    (C:=151/(100*(k:ℝ))) (by positivity) hraw (by
      intro i hi
      rw [←original_color_count_eq_transform hm0 hk, hm]
      have hh := original_residual_count_bound (i:=i) hk hkm (by dsimp [m]; omega : 100*i ≤ m)
      simpa only [←hm,Nat.add_sub_cancel] using hh)
  have ha : (0:ℝ) ≤ ((k:ℝ)*p)/(N+1:ℕ) := by positivity
  apply (mul_le_mul_of_nonneg_left hres ha).trans_eq
  rw [←mul_assoc]
  congr 1
  have hkR : (0:ℝ) < k := by positivity
  have hpR : (0:ℝ) < p := by positivity
  have hNR : (0:ℝ) < (N+1:ℕ) := by positivity
  field_simp
  <;> ring

#print axioms original_residual_count_bound
#print axioms original_lag_residual_grid
end RepositoryQuotientAudit
