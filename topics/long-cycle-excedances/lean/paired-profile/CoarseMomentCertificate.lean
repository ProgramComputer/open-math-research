import RepositoryRegularCost
import LiteralLinearTable

set_option autoImplicit false
namespace OpenMathResearch.LongCycleExcedances
open Finset

noncomputable def coarseZerothUnits (c : ℚ) : ℕ :=
  (∑ q ∈ signedHead 31, linearWeight c q) + 2 * linearHalfTail c

def coarseFirstUnits (c : ℚ) : ℕ :=
  2 * (∑ i ∈ range 31, (2*i+3)*linearWeight c ((i:ℤ)+1)) + linearFirstTail c

private theorem inv_base_antitone {c d p : ℝ} (hc : 0 ≤ c) (hd : c ≤ d)
    (hp : 1 ≤ p^2) (m : ℕ) :
    ((oBase d p)^m)⁻¹ ≤ ((oBase c p)^m)⁻¹ := by
  have h : 0 ≤ p^2-1 := by linarith
  have h₀ : 0 < oBase c p := by unfold oBase; linarith only [mul_nonneg hc h]
  apply inv_anti₀ (pow_pos h₀ m)
  exact pow_le_pow_left₀ h₀.le (by unfold oBase; linarith only [mul_le_mul_of_nonneg_right hd h]) m

private theorem coarse_weight_cap {c : ℚ} {d : ℝ} (hc : 0 ≤ (c:ℝ)) (hd : (c:ℝ) ≤ d) (q : ℤ) :
    oddBinKernel d q ≤ (linearWeight c q:ℝ)/linearScale := by
  have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) (primitive_odd_abs_ge_one q) 2
  have hp : 1 ≤ primitiveOddNumber q^2 := by simpa [sq_abs] using hh
  apply (inv_base_antitone hc hd hp 96).trans
  apply (le_div_iff₀ (by norm_num [linearScale] : (0:ℝ)<linearScale)).mpr
  have h : (linearScale:ℚ)*((1+c*(rationalOdd q^2-1))^96)⁻¹ ≤ (linearWeight c q:ℚ) := Nat.le_ceil _
  have h' : (linearScale:ℝ)*((1+(c:ℝ)*(primitiveOddNumber q^2-1))^96)⁻¹ ≤ (linearWeight c q:ℝ) := by
    unfold primitiveOddNumber
    unfold rationalOdd at h
    exact_mod_cast h
  simpa only [oBase,mul_comm] using h'

private theorem coarse_first_tail_cap {c : ℚ} {d : ℝ} (hc : 0 < (c:ℝ)) (hd : (c:ℝ) ≤ d) :
    oTail d 63/(190*d) ≤ (linearFirstTail c:ℝ)/linearScale := by
  have hh := inv_base_antitone hc.le hd (by norm_num : (1:ℝ) ≤ 63^2) 95
  have hp : 0 < (oBase (c:ℝ) 63)^95 := by unfold oBase; positivity
  apply (div_le_div₀ (inv_nonneg.mpr hp.le) hh (by positivity : 0 < 190*(c:ℝ)) (by linarith)).trans
  apply (le_div_iff₀ (by norm_num [linearScale] : (0:ℝ)<linearScale)).mpr
  have h : (linearScale:ℚ)*((1+c*(63^2-1))^95)⁻¹/(190*c) ≤ (linearFirstTail c:ℚ) := Nat.le_ceil _
  have h' : (linearScale:ℝ)*((1+(c:ℝ)*(63^2-1))^95)⁻¹/(190*(c:ℝ)) ≤ (linearFirstTail c:ℝ) := by
    exact_mod_cast h
  calc
    _ = (linearScale:ℝ)*((1+(c:ℝ)*(63^2-1))^95)⁻¹/(190*(c:ℝ)) := by unfold oBase; ring
    _ ≤ _ := h'

private theorem coarse_zeroth_tail_cap {c : ℚ} {d : ℝ} (hc : 0 < (c:ℝ)) (hd : (c:ℝ) ≤ d) :
    oTail d 63/(190*d*63) ≤ (2*(linearHalfTail c:ℝ))/linearScale := by
  have h1 := coarse_first_tail_cap hc hd
  have h2 : (linearFirstTail c:ℚ)/63 ≤ linearMassTail c := Nat.le_ceil _
  have h3 : (linearMassTail c:ℚ)/2 ≤ linearHalfTail c := Nat.le_ceil _
  have h23 : (linearFirstTail c:ℝ)/63 ≤ 2*(linearHalfTail c:ℝ) := by
    have h : linearFirstTail c ≤ 126 * linearHalfTail c := by
      exact_mod_cast (show (linearFirstTail c:ℚ) ≤ 126*(linearHalfTail c:ℚ) by linarith only [h2,h3])
    have h' : (linearFirstTail c:ℝ) ≤ 126 * (linearHalfTail c:ℝ) := by exact_mod_cast h
    linarith only [h']
  rw [←div_div]
  apply (div_le_div_of_nonneg_right h1 (by norm_num : (0:ℝ)≤63)).trans
  rw [div_right_comm]
  exact div_le_div_of_nonneg_right h23 (by positivity)

theorem coarse_zeroth_moment_cap {c : ℚ} {d : ℝ} (hc : 0 < (c:ℝ)) (hd : (c:ℝ) ≤ d) :
    zerothMomentBound d 31 ≤ (coarseZerothUnits c:ℝ)/linearScale := by
  unfold zerothMomentBound coarseZerothUnits
  push_cast
  rw [add_div, sum_div]
  apply add_le_add (sum_le_sum (fun q _ => coarse_weight_cap hc.le hd q)) _
  rw [show (2*(31:ℝ)+1)=63 by norm_num]
  exact coarse_zeroth_tail_cap hc hd

theorem coarse_first_moment_cap {c : ℚ} {d : ℝ} (hc : 0 < (c:ℝ)) (hd : (c:ℝ) ≤ d) :
    firstMomentBound d 31 ≤ (coarseFirstUnits c:ℝ)/linearScale := by
  unfold firstMomentBound coarseFirstUnits
  push_cast
  rw [add_div, mul_div_assoc, sum_div]
  rw [show (2*(31:ℝ)+1)=63 by norm_num]
  apply add_le_add _ (coarse_first_tail_cap hc hd)
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply sum_le_sum
  intro i _
  rw [mul_div_assoc]
  have hp : primitiveOddNumber ((i:ℤ)+1)=2*(i:ℝ)+3 := by unfold primitiveOddNumber; push_cast; ring
  unfold positiveOddMoment
  have hw := coarse_weight_cap hc.le hd ((i:ℤ)+1)
  change oWeight d (primitiveOddNumber ((i:ℤ)+1)) ≤ _ at hw
  rw [hp] at hw
  exact mul_le_mul_of_nonneg_left hw (by positivity)

#print axioms coarse_zeroth_moment_cap
#print axioms coarse_first_moment_cap
end OpenMathResearch.LongCycleExcedances
