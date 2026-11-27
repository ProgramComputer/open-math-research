import PositiveFrequency

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset Real

def radialFrequency (k : ℕ) (s R : ℝ) (a : ℕ) : ℝ :=
  let A := ((a+1:ℕ):ℝ)
  exp (-A*s) * ∑ j ∈ range (k-1), (A*R)^j/(j.factorial:ℝ)

theorem radial_frequency_sum (k : ℕ) (s R D : ℝ) (hs : 0 < s) (hsR : s ≤ R)
    (hk : 0 < k) (hD : 0 ≤ D) (hR : R-s ≤ D*(s/k))
    (hc : 0 < 1/50-D/k) (F : Finset ℕ) :
    (∑ a ∈ F, radialFrequency k s R a) ≤
      ((5/4:ℝ)*k/s)*exp (D*(5/4)) + 1/((1/50-D/k)*s) := by
  have hkR : (0:ℝ) < k := by exact_mod_cast hk
  have hR0 : 0 ≤ R := hs.le.trans hsR
  have hcut : (0:ℝ) ≤ (5/4)*k/s := by positivity
  apply positive_mesh_split hcut (exp_pos _).le (by norm_num : (0:ℝ)≤1) (mul_pos hc hs) F
  · intro a _ ha
    let A := ((a+1:ℕ):ℝ)
    have hA : 0 ≤ A := by positivity
    have hAs : A*s ≤ (5/4:ℝ)*k := (le_div_iff₀ hs).mp ha
    unfold radialFrequency
    calc
      _ ≤ exp (-A*s)*exp (A*R) :=
        mul_le_mul_of_nonneg_left (sum_le_exp_of_nonneg (mul_nonneg hA hR0) _) (exp_pos _).le
      _ = exp (A*(R-s)) := by rw [← exp_add]; congr 1; ring
      _ ≤ _ := by
        apply exp_le_exp.mpr
        apply (mul_le_mul_of_nonneg_left hR hA).trans
        have h := mul_le_mul_of_nonneg_left ((div_le_iff₀ hkR).mpr hAs) hD
        convert h using 1
        ring
  · intro a _ ha
    let A := ((a+1:ℕ):ℝ)
    have hA : 0 ≤ A := by positivity
    have hAs : (5/4:ℝ)*k < A*s := (div_lt_iff₀ hs).mp ha
    have hAr : (5/4:ℝ)*k ≤ A*R :=
      hAs.le.trans (mul_le_mul_of_nonneg_left hsR hA)
    unfold radialFrequency
    rw [one_mul]
    calc
      _ ≤ exp (-A*s)*exp (49/50*(A*R)) :=
        mul_le_mul_of_nonneg_left (poisson_lower_tilt (mul_nonneg hA hR0) k hAr) (exp_pos _).le
      _ ≤ _ := by
        rw [← exp_add]
        apply exp_le_exp.mpr
        have h := mul_le_mul_of_nonneg_left hR hA
        have h' := mul_le_mul_of_nonneg_left hsR (show 0 ≤ (1/50:ℝ)*A by positivity)
        change -A*s+49/50*(A*R) ≤ -A*((1/50-D/k)*s)
        simp only [div_eq_mul_inv] at h ⊢
        nlinarith only [h,h']

def tailFrequency (s t : ℝ) (J : ℕ → Finset ℕ) (a : ℕ) : ℝ :=
  let A := ((a+1:ℕ):ℝ)
  exp (-A*s)/A * ∑ j ∈ J a, (A*t)^j/(j.factorial:ℝ)

theorem tail_frequency_sum (k : ℕ) (s t : ℝ) (hk : 100 ≤ k) (ht : 1 ≤ t)
    (hgap : (69/100)*s/k ≤ s-t) (hts : t < s)
    (F : Finset ℕ) (J : ℕ → Finset ℕ) (hJ : ∀ a j, j ∈ J a → k ≤ j) :
    (∑ a ∈ F, tailFrequency s t J a) ≤ 1/1000+2/(69/100) := by
  have hK : (100:ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0:ℝ) < k := by linarith
  have ht0 : 0 < t := by linarith
  have hs0 : 0 < s := ht0.trans hts
  have hc : 0 < s-t := by linarith
  have hsplit :
      (∑ a ∈ F, tailFrequency s t J a) ≤
        ((k:ℝ)/(2*t))*exp (-(k:ℝ)/6) + (2*t/k)/(s-t) := by
    refine positive_mesh_split (by positivity) (exp_pos _).le (by positivity) hc F _ ?_ ?_
    · intro a _ ha
      let A := ((a+1:ℕ):ℝ)
      have hA : 0 < A := by positivity
      have hA1 : 1 ≤ A := by
        change (1:ℝ) ≤ ((a+1:ℕ):ℝ)
        exact_mod_cast (by omega : 1 ≤ a+1)
      have ha' : A*(2*t) ≤ k := (le_div_iff₀ (by positivity : 0<2*t)).mp ha
      unfold tailFrequency
      calc
        _ ≤ exp (-A*s)/A * exp (2*(A*t)-(2/3:ℝ)*k) :=
          mul_le_mul_of_nonneg_left (poisson_upper_tilt (by positivity) _ _ (hJ a)) (by positivity)
        _ = exp (-A*s+(2*(A*t)-(2/3:ℝ)*k))/A := by
          rw [exp_add]
          ring
        _ ≤ exp (-A*s+(2*(A*t)-(2/3:ℝ)*k)) := by
          apply div_le_self (exp_pos _).le hA1
        _ ≤ _ := by
          apply exp_le_exp.mpr
          nlinarith only [ha', mul_le_mul_of_nonneg_left hts.le hA.le]
    · intro a _ ha
      let A := ((a+1:ℕ):ℝ)
      have hA : 0 < A := by positivity
      have ha' : (k:ℝ) < A*(2*t) := (div_lt_iff₀ (by positivity : 0<2*t)).mp ha
      have hi : (1:ℝ)/A ≤ 2*t/k := by
        apply (div_le_div_iff₀ hA hk0).mpr
        nlinarith only [ha']
      unfold tailFrequency
      calc
        _ ≤ exp (-A*s)/A * exp (A*t) :=
          mul_le_mul_of_nonneg_left (expTerms_le (by positivity) _) (by positivity)
        _ = (1/A)*exp (-A*(s-t)) := by
          rw [show -A*(s-t)=-A*s+A*t by ring, exp_add]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hi (exp_pos _).le
  apply hsplit.trans
  apply add_le_add
  · have hcut : (k:ℝ)/(2*t) ≤ k := by
      exact div_le_self hk0.le (by linarith)
    exact (mul_le_mul_of_nonneg_right hcut (exp_pos _).le).trans (high_height_exp_reserve hK)
  · have h : (69/100)*s ≤ (s-t)*(k:ℝ) := (div_le_iff₀ hk0).mp hgap
    apply (div_le_iff₀ hc).mpr
    apply (div_le_iff₀ hk0).mpr
    nlinarith only [h,hts]

#print axioms radial_frequency_sum
#print axioms tail_frequency_sum
end OpenMathResearch.LongCycleExcedances
