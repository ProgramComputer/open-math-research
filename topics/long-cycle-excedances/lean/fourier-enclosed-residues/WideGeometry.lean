import WideDensity

noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real

private theorem wide_exp_bound : exp (113/200 : ℝ) ≤ 44/25 := by
  have h := exp_bound' (x := 113/200) (by norm_num) (by norm_num) (n := 7) (by decide)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith only [h]

/-- The existence of any enclosed nonprincipal odd pole forces sufficient height
and bounds the entire enclosing radius against the height. -/
theorem wide_residue_height_power {k : ℕ} (hk : 100 ≤ k)
    {s r R : ℝ} (hs : 0 < s) (hr : r^2 = s^2 + π^2)
    (hR : 0 ≤ R) (hbelow : s^2 + 9*π^2 ≤ R^2)
    (hcap : R^2 ≤ r^2*(1+2/(k:ℝ))) :
    125/2 ≤ s ∧ R^(k-1) ≤ s^(k-1)*(31/10) := by
  have hk' : (100:ℝ) ≤ k := by exact_mod_cast hk
  have hk₀ : (0:ℝ) < k := by linarith
  have hsub : 8*π^2 ≤ r^2*(2/(k:ℝ)) := by
    have h := hbelow.trans hcap
    linarith only [h,hr]
  have hlarge : 4*(k:ℝ)*π^2 ≤ r^2 := by
    have h := (le_div_iff₀ hk₀).mp
      (show 8*π^2 ≤ r^2*2/(k:ℝ) by simpa [mul_div_assoc] using hsub)
    linarith only [h]
  have hss : (4*(k:ℝ)-1)*π^2 ≤ s^2 := by linarith only [hlarge,hr]
  have hheight : (125/2:ℝ) ≤ s := by
    apply le_of_sq_le_sq _ hs.le
    have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 3.1415) pi_gt_d4.le 2
    exact le_trans (by norm_num : (125/2:ℝ)^2 ≤ 3.1415^2*399)
      ((mul_le_mul hp (by linarith : (399:ℝ) ≤ 4*(k:ℝ)-1)
        (by norm_num) (sq_nonneg π)).trans (by simpa [mul_comm] using hss))
  refine ⟨hheight, ?_⟩
  have hRpos : 0 < R := by nlinarith only [hR, hbelow, sq_pos_of_pos hs, sq_nonneg π]
  have hd : R^2 ≤ s^2*(1+(113/50)/(k:ℝ)) := by
    have hc : ((k:ℝ)+2)*π^2 ≤ (13/50)*s^2 := by
      exact (mul_le_mul_of_nonneg_right
        (show (k:ℝ)+2 ≤ (13/50)*(4*(k:ℝ)-1) by linarith) (sq_nonneg π)).trans
        (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hss (by norm_num))
    apply (le_of_mul_le_mul_right _ hk₀)
    have h := mul_le_mul_of_nonneg_right hcap hk₀.le
    rw [mul_assoc, add_mul, one_mul, div_mul_cancel₀ _ hk₀.ne', hr] at h
    rw [mul_assoc, add_mul, one_mul, div_mul_cancel₀ _ hk₀.ne']
    nlinarith only [h,hc]
  have hlog : log (R/s) ≤ (113/100)/(k:ℝ) := by
    have hh : R^2/s^2 ≤ 1+(113/50)/(k:ℝ) :=
      (div_le_iff₀ (sq_pos_of_pos hs)).mpr (by simpa [mul_comm] using hd)
    rw [←div_pow] at hh
    have hl := log_le_sub_one_of_pos (pow_pos (div_pos hRpos hs) 2)
    rw [log_pow] at hl
    norm_num at hl
    have he : (113/50:ℝ)/(k:ℝ) = 2*((113/100)/(k:ℝ)) := by ring
    linarith only [hl,hh,he]
  have hn : (0:ℝ) ≤ (k-1:ℕ) := Nat.cast_nonneg _
  have hnk : ((k-1:ℕ):ℝ) ≤ k := by exact_mod_cast (Nat.sub_le k 1)
  have hlogn : log ((R/s)^(k-1)) ≤ 113/100 := by
    rw [log_pow]
    calc
      _ ≤ ((k-1:ℕ):ℝ) * (113/100/(k:ℝ)) := mul_le_mul_of_nonneg_left hlog hn
      _ ≤ (k:ℝ) * (113/100/(k:ℝ)) := mul_le_mul_of_nonneg_right hnk (by positivity)
      _ = _ := by
        field_simp
        ring
  have hE : exp (113/100:ℝ) ≤ 31/10 := by
    rw [show (113/100:ℝ) = 113/200+113/200 by norm_num, exp_add, ←pow_two]
    exact (pow_le_pow_left₀ (exp_pos _).le wide_exp_bound 2).trans (by norm_num)
  rw [mul_comm (s^(k-1)) _, ←div_le_iff₀ (pow_pos hs _), ←div_pow]
  exact ((log_le_log_iff (pow_pos (div_pos hRpos hs) _) (exp_pos _)).mp
    (by rwa [log_exp])).trans hE

#print axioms wide_residue_height_power
end OpenMathResearch.LongCycleExcedances
