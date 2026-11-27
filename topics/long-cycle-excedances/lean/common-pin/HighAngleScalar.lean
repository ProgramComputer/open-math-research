import OpenMathResearch.FirstLevelHits
import OpenMathResearch.DiskUniqueness
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Basic


noncomputable section
namespace OpenMathResearch.LongCycleExcedances

theorem cutoff_radius_power_le_exp_one {k j : ℕ} (hk : 0 < k) (hj : j ≤ k) :
    (1 + 1/(k:ℝ))^j ≤ Real.exp 1 := by
  have hk' : 0 < (k:ℝ) := by exact_mod_cast hk
  have hx : 0 < 1 + 1/(k:ℝ) := by positivity
  have hl := Real.log_le_sub_one_of_pos hx
  have hj' : (j:ℝ) ≤ k := by exact_mod_cast hj
  rw [← Real.exp_log hx, ← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  calc
    (j:ℝ) * Real.log (1+1/(k:ℝ)) ≤ (j:ℝ) * (1/(k:ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    _ ≤ (k:ℝ)*(1/(k:ℝ)) := mul_le_mul_of_nonneg_right hj' (by positivity)
    _ = 1 := by field_simp

theorem coherentLinearTilt_bound {t R : ℝ} (ht : -1 ≤ t) (ht0 : t ≤ 0)
    (hR : 0 ≤ R) (hR' : R ≤ 10) :
    |-t/(1-t)*R| ≤ 5 := by
  have hd : 0 < 1-t := by linarith
  have hnon : 0 ≤ -t/(1-t) := div_nonneg (by linarith) hd.le
  rw [abs_of_nonneg (mul_nonneg hnon hR)]
  calc
    _ ≤ (1/2:ℝ)*R := by
      apply mul_le_mul_of_nonneg_right _ hR
      exact (div_le_iff₀ hd).2 (by linarith)
    _ ≤ 5 := by linarith

end OpenMathResearch.LongCycleExcedances

noncomputable section
open Finset
namespace OpenMathResearch.LongCycleExcedances

private theorem shifted_harmonic_sum (m : ℕ) :
    (∑ i ∈ range m, 1 / ((i:ℝ)+2)) ≤ Real.log ((m:ℝ)+1) := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [sum_range_succ, Nat.cast_succ, show (m:ℝ)+1+1=(m:ℝ)+2 by ring]
    have h₁ : 0 < (m:ℝ)+1 := by positivity
    have h₂ : 0 < (m:ℝ)+2 := by positivity
    have h := Real.one_sub_inv_le_log_of_pos (div_pos h₂ h₁)
    rw [Real.log_div h₂.ne' h₁.ne', inv_div] at h
    have he : 1 - ((m:ℝ)+1)/((m:ℝ)+2) = 1/((m:ℝ)+2) := by
      field_simp [h₂.ne'] <;> ring
    rw [he] at h
    linarith

theorem high_angle_finite_log_bound {k : ℕ} (hk : 2 ≤ k)
    (g : ℕ → ℝ) (R : ℝ)
    (hfirst : |g 1 * R| ≤ 5)
    (hrest : ∀ j : ℕ, 2 ≤ j → j < k → |g j * R^j| ≤ 18/(j:ℝ)) :
    (∑ i ∈ range (k-1), |g (i+1) * R^(i+1)|) ≤ 5 + 18*Real.log k := by
  have he : k-1 = (k-2)+1 := by omega
  rw [he, sum_range_succ']
  simp only [zero_add, pow_one]
  have hp : (∑ i ∈ range (k-2), |g (i+1+1) * R^(i+1+1)|) ≤
      18 * (∑ i ∈ range (k-2), 1 / ((i:ℝ)+2)) := by
    rw [mul_sum]
    refine sum_le_sum fun i hi => ?_
    have hi' := mem_range.mp hi
    have h := hrest (i+1+1) (by omega) (by omega)
    rw [mul_one_div]
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using h
  have hh := shifted_harmonic_sum (k-2)
  have hk' : (k-2)+1 ≤ k := by omega
  have hp' : (0:ℝ) < (((k-2)+1:ℕ):ℝ) := by positivity
  have hc : ((((k-2)+1:ℕ):ℝ)) ≤ (k:ℝ) := by exact_mod_cast hk'
  have hl := Real.log_le_log hp' hc
  push_cast at hl
  linarith

end OpenMathResearch.LongCycleExcedances

noncomputable section
open Finset
namespace OpenMathResearch.LongCycleExcedances

theorem taylor_tail_majorant (u : ℕ → ℂ) {A ρ : ℝ}
    (hA : 0 ≤ A) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hu : ∀ j, ‖u j‖ ≤ A*ρ^j) (n : ℕ) :
    Summable (fun j => ‖u j‖) ∧
      ‖(∑' j, u j) - ∑ j ∈ range n, u j‖ ≤ A*ρ^n/(1-ρ) := by
  have hsρ : Summable fun j : ℕ => ρ^j :=
    summable_geometric_of_lt_one hρ0 hρ1
  have hs : Summable (fun j => ‖u j‖) :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _) hu (hsρ.mul_left A)
  have hdom (j : ℕ) : ‖u (j+n)‖ ≤ (A*ρ^n)*ρ^j := by
    convert hu (j+n) using 1
    rw [pow_add]
    ring
  have hshift : Summable (fun j => ‖u (j+n)‖) :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _) hdom (hsρ.mul_left _)
  refine ⟨hs, ?_⟩
  rw [← hs.of_norm.sum_add_tsum_nat_add n, add_sub_cancel_left]
  have h := (norm_tsum_le_tsum_norm hshift).trans (hshift.tsum_le_tsum hdom (hsρ.mul_left _))
  rw [tsum_mul_left, tsum_geometric_of_lt_one hρ0 hρ1] at h
  simpa only [div_eq_mul_inv] using h

end OpenMathResearch.LongCycleExcedances

namespace OpenMathResearch.LongCycleExcedances

/-- The explicit row threshold makes the common-bound geometric envelope
smaller than one sixth. -/
theorem high_angle_geometric_envelope (K : ℝ) (n : ℕ) (hk : 7 ≤ K) (hn : 0 < n)
    (hEuler : Real.exp 1 < 3) (hsize : 100*K*Real.log K ≤ n) :
    4 * Real.exp 10 * K^37 * (1 + 1/K)⁻¹^(n-1) < 1/6 := by
  have hk0 : 0 < K := by linarith
  have hx : 0 < 1 + 1/K := by positivity
  let q : ℝ := (1+1/K)⁻¹
  have hq : 0 < q := inv_pos.mpr hx
  have hqeq : q = K/(K+1) := by
    unfold q
    field_simp [(by linarith : K+1 ≠ 0), hk0.ne']
  have hqlog : Real.log q ≤ -(1/(2*K)) := by
    have h1 := Real.log_le_sub_one_of_pos hq
    have h2 : q - 1 ≤ -(1/(2*K)) := by
      calc
        _ = -(1/(K+1)) := by
          rw [hqeq]
          field_simp [(by linarith : K+1 ≠ 0)] <;> ring
        _ ≤ _ := neg_le_neg (one_div_le_one_div_of_le (by linarith) (by linarith))
    exact h1.trans h2
  have hncast : ((n-1:ℕ):ℝ) = (n:ℝ)-1 := by
    rw [Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_one]
  have hb : 50*Real.log K - 1 ≤ ((n:ℝ)-1)/(2*K) := by
    apply (le_div_iff₀ (by positivity : 0 < 2*K)).mpr
    nlinarith only [hsize,hk]
  have htail : q^(n-1) ≤ Real.exp (1-50*Real.log K) := by
    conv_lhs => rw [← Real.exp_log hq, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    rw [hncast]
    have h0 : 0 ≤ (n:ℝ)-1 := sub_nonneg.mpr (by exact_mod_cast (show 1 ≤ n by omega))
    have hm := mul_le_mul_of_nonneg_left hqlog h0
    calc
      _ ≤ (↑n-1) * -(1/(2*K)) := hm
      _ = -((↑n-1)/(2*K)) := by ring
      _ ≤ _ := by linarith only [hb]
  have hEuler11 : Real.exp 11 ≤ (3:ℝ)^11 := by
    rw [show (11:ℝ) = (11:ℕ)*1 by norm_num, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_pos _).le hEuler.le _
  have hfinal : 4 * (3:ℝ)^11 / K^13 < 1/6 := by
    have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 7) hk 13
    apply (div_lt_iff₀ (by positivity : 0 < K^13)).2
    norm_num at hp ⊢
    linarith
  change 4 * Real.exp 10 * K^37 * q^(n-1) < 1/6
  calc
    _ ≤ 4 * Real.exp 10 * K^37 * Real.exp (1-50*Real.log K) :=
      mul_le_mul_of_nonneg_left htail (by positivity)
    _ = 4 * Real.exp 11 / K^13 := by
      rw [Real.exp_sub, show (50:ℝ) * Real.log K = (50:ℕ) * Real.log K by norm_num,
        Real.exp_nat_mul, Real.exp_log hk0]
      have he : Real.exp 10 * Real.exp 1 = Real.exp 11 := by rw [← Real.exp_add]; norm_num
      rw [show K^50 = K^37*K^13 by rw [← pow_add]]
      calc
        _ = 4 * (Real.exp 10 * Real.exp 1) / K^13 := by field_simp [hk0.ne'] <;> ring
        _ = _ := by rw [he]
    _ ≤ 4 * (3:ℝ)^11 / K^13 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hEuler11 (by norm_num)) (by positivity)
    _ < _ := hfinal

#print axioms high_angle_geometric_envelope
end OpenMathResearch.LongCycleExcedances

namespace OpenMathResearch.LongCycleExcedances

/-- An actual old zero and two strict principal-mode margins imply the
prescribed sign of the actual next value. -/
theorem next_sign_of_unit_principal_mode {a : ℂ} {c S y : ℝ}
    (ha : ‖a‖ = 1) (hc : |c| ≤ 1) (hs : (1:ℝ)/2 ≤ S)
    (hold : |a.re| ≤ 1/6) (hnext : |y-(c*a.re+S*a.im)| ≤ 1/6) :
    0 < y*a.im := by
  have hnorm := Complex.sq_norm a
  rw [ha, Complex.normSq_apply] at hnorm
  have hr2 := pow_le_pow_left₀ (abs_nonneg a.re) hold 2
  rw [sq_abs] at hr2
  have hi : (2:ℝ)/3 < |a.im| := by
    by_contra h
    have hi2 := pow_le_pow_left₀ (abs_nonneg a.im) (le_of_not_gt h) 2
    rw [sq_abs] at hi2
    nlinarith only [hnorm, hr2, hi2]
  have hprod : |c*a.re| ≤ 1/6 := by
    rw [abs_mul]
    simpa using mul_le_mul hc hold (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
  have herror : |y-S*a.im| ≤ 1/3 := by
    have he : y-S*a.im = (y-(c*a.re+S*a.im)) + c*a.re := by ring
    rw [he]
    linarith only [abs_add_le (y-(c*a.re+S*a.im)) (c*a.re), hprod, hnext]
  rcases lt_or_ge 0 a.im with him | him
  · rw [abs_of_pos him] at hi
    have h := mul_le_mul_of_nonneg_right hs him.le
    exact mul_pos (by linarith only [h, hi, (abs_le.mp herror).1]) him
  · rw [abs_of_nonpos him] at hi
    have h := mul_le_mul_of_nonneg_right hs (neg_nonneg.mpr him)
    exact mul_pos_of_neg_of_neg (by linarith only [h, hi, (abs_le.mp herror).2])
      (by linarith only [hi])

#print axioms next_sign_of_unit_principal_mode
end OpenMathResearch.LongCycleExcedances
