import LinearSlabs

set_option autoImplicit false
namespace OpenMathResearch.LongCycleExcedances
open Finset

private theorem rational_odd_square (q : ℤ) : 0 ≤ rationalOdd q^2-1 := by
  have hp : |(2*(q:ℚ)+1)| ≥ 1 := by
    by_cases h : 0≤q
    · have hr : 0≤(q:ℚ) := by exact_mod_cast h
      rw [abs_of_nonneg (by linarith)]
      linarith
    · have hr : (q:ℚ) ≤ -1 := by exact_mod_cast (show q ≤ -1 by omega)
      rw [abs_of_nonpos (by linarith)]
      linarith
  have hh := pow_le_pow_left₀ (by norm_num : (0:ℚ)≤1) hp 2
  simpa [rationalOdd,sq_abs,sub_nonneg] using hh

private theorem linear_weight_antitone {c d : ℚ} (hc : 0≤c) (hcd : c≤d) (q : ℤ) :
    linearWeight d q ≤ linearWeight c q := by
  have hv := rational_odd_square q
  have hlo : 0<1+c*(rationalOdd q^2-1) := by linarith only [mul_nonneg hc hv]
  apply Nat.ceil_mono
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply inv_anti₀ (pow_pos hlo 96)
  exact pow_le_pow_left₀ hlo.le (by linarith only [mul_le_mul_of_nonneg_right hcd hv]) 96

theorem linear_head_antitone {c d : ℚ} (hc : 0≤c) (hcd : c≤d) :
    linearHead d ≤ linearHead c := by
  rw [linearHead_eq,linearHead_eq]
  apply Finset.sup_le
  intro a ha
  apply le_trans _ (le_sup (s:=signedCenters 31) (f:=fun z =>
    ∑ q ∈ (signedHead 31).erase z, linearGapWeight c z q) ha)
  apply sum_le_sum
  intro q _
  exact Nat.ceil_mono (div_le_div_of_nonneg_right
    (show (linearWeight d q:ℚ) ≤ linearWeight c q by exact_mod_cast linear_weight_antitone hc hcd q)
    (by positivity))

theorem linear_half_tail_antitone {c d : ℚ} (hc : 0<c) (hcd : c≤d) :
    linearHalfTail d ≤ linearHalfTail c := by
  have hb : 0<(1+c*(63^2-1):ℚ) := by linarith
  have hv : (1+c*(63^2-1):ℚ) ≤ 1+d*(63^2-1) := by linarith
  have hpow := inv_anti₀ (pow_pos hb 95) (pow_le_pow_left₀ hb.le hv 95)
  have hfirst : linearFirstTail d ≤ linearFirstTail c := by
    apply Nat.ceil_mono
    exact div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hpow (by positivity))
      (by positivity) (by linarith)
  have hmass : linearMassTail d ≤ linearMassTail c := Nat.ceil_mono (div_le_div_of_nonneg_right
    (show (linearFirstTail d:ℚ) ≤ linearFirstTail c by exact_mod_cast hfirst) (by norm_num : (0:ℚ)≤63))
  exact Nat.ceil_mono (div_le_div_of_nonneg_right
    (show (linearMassTail d:ℚ) ≤ linearMassTail c by exact_mod_cast hmass) (by norm_num : (0:ℚ)≤2))

theorem linear_head_lower_two_poles (c : ℚ) : 3*linearScale/4 ≤ linearHead c := by
  let a : ℤ := 1
  let U : Finset ℤ := {0,-1}
  have hu : U ⊆ (signedHead 31).erase a := by
    intro x hx
    simp only [U,mem_insert,mem_singleton] at hx
    rcases hx with rfl|rfl <;> decide
  have hc : a ∈ signedCenters 31 := by decide
  have h := (sum_le_sum_of_subset_of_nonneg (f:=linearGapWeight c a) hu (fun _ _ _ => Nat.zero_le _)).trans
    (le_sup (s:=signedCenters 31) (f:=fun z => ∑ q ∈ (signedHead 31).erase z,linearGapWeight c z q) hc)
  rw [linearHead_eq]
  apply le_trans _ h
  norm_num [U,a,linearGapWeight,linearWeight,linearScale,rationalOdd,oddGap]

#print axioms linear_head_antitone
#print axioms linear_half_tail_antitone
#print axioms linear_head_lower_two_poles
end OpenMathResearch.LongCycleExcedances
