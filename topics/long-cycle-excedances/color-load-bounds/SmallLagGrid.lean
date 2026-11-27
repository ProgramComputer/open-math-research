import BinomialColorLoad
import LoadEnvelope

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset Real

private theorem small_grid_geom {r : ℝ} (hr : r ≤ exp (-(25/4):ℝ)) :
    r/(1-r) ≤ 1/500 := by
  have h := hr.trans_lt color_load_geom_small
  apply (div_le_iff₀ (show 0 < 1-r by linarith)).mpr
  linarith

/-- The small-cutoff grid bound uses only the lower-tail estimate and the
finite geometric sum. The zero endpoint vanishes since k-1 is positive. -/
theorem small_lag_grid_mass {n k p : ℕ} (hp : 0 < p) (hk : 2 ≤ k)
    (hkn : k ≤ n) (hs : 200*p ≤ n)
    (ha : ((k:ℝ)*p)/(n:ℝ) ≤ 3/4) :
    (∑ j ∈ range (p+1), colorLoad n (k-1) ((j:ℝ)/p)) ≤ 1/500 := by
  have hn : 0 < n := by omega
  have hpR : (0:ℝ) < p := Nat.cast_pos.mpr hp
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr hn
  let r := exp (-(n:ℝ)/(32*(p:ℝ)))
  have hr : 0 < r := exp_pos _
  have hr1 : r < 1 := exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (neg_lt_zero.mpr hnR) (by positivity))
  have hr25 : r ≤ exp (-(25/4):ℝ) := by
    apply exp_le_exp.mpr
    apply (div_le_iff₀ (by positivity : (0:ℝ) < 32*(p:ℝ))).mpr
    have hs' : 200*(p:ℝ) ≤ n := by exact_mod_cast hs
    linarith only [hs']
  have hzero : colorLoad n (k-1) (((0:ℕ):ℝ)/(p:ℝ)) = 0 := by
    simp [colorLoad, zero_pow (by omega : k-1 ≠ 0)]
  have hpoint (j : ℕ) (hj : 0 < j) (hjp : j ≤ p) :
      colorLoad n (k-1) ((j:ℝ)/p) ≤ r^j := by
    let x := (j:ℝ)/p
    have hx : 0 ≤ x := by dsimp [x]; positivity
    have hu : x ≤ 1 := (div_le_one hpR).mpr (Nat.cast_le.mpr hjp)
    have hm : (k:ℝ) ≤ 3*(n:ℝ)*x/4 := by
      have hh := (div_le_iff₀ hnR).mp ha
      have hjR : (1:ℝ) ≤ j := by exact_mod_cast hj
      have hprod := mul_le_mul_of_nonneg_left hjR hnR.le
      have ht : (k:ℝ)*(p:ℝ) ≤ (3/4:ℝ)*((n:ℝ)*(j:ℝ)) := by nlinarith only [hh,hprod]
      calc
        _ ≤ (3/4:ℝ)*((n:ℝ)*(j:ℝ))/(p:ℝ) := (le_div_iff₀ hpR).mpr ht
        _ = _ := by dsimp [x]; ring
    have hi : k-1 ∈ (range (n+1)).filter (· < k) :=
      mem_filter.mpr ⟨mem_range.mpr (by omega), by omega⟩
    have ht := (single_le_sum (fun i _ => color_load_nonneg n i hx hu) hi).trans
      (color_load_lower_tail n k hx hu hm)
    have he : exp (-(n:ℝ)*x/32) = r^j := by
      dsimp [x,r]
      rw [←exp_nat_mul]
      congr 1
      ring
    exact ht.trans_eq he
  rw [sum_range_succ']
  simp only [hzero,add_zero]
  calc
    _ ≤ ∑ i ∈ range p, r^(i+1) := sum_le_sum fun i hi =>
      hpoint (i+1) (by omega) (mem_range.mp hi)
    _ = r * ∑ i ∈ range p, r^i := by
      rw [mul_sum]
      apply sum_congr rfl
      intro i _
      rw [pow_succ, mul_comm]
    _ ≤ r/(1-r) := by
      have hgeom := geom_sum_mul r p
      have hnum : (∑ i ∈ range p, r^i)*(1-r) ≤ 1 := by
        nlinarith only [hgeom, pow_nonneg hr.le p]
      have hf : (∑ i ∈ range p, r^i) ≤ 1/(1-r) :=
        (le_div_iff₀ (sub_pos.mpr hr1)).mpr hnum
      simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hf hr.le
    _ ≤ _ := small_grid_geom hr25

#print axioms small_lag_grid_mass
end OpenMathResearch.LongCycleExcedances
