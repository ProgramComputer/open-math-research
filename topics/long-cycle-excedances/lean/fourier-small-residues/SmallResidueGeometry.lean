import WideGeometry

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real

/-- Enclosure of a minor pole bounds the radius to height ratio uniformly
on the finite cutoffs, even at the smallest cutoff eight. -/
theorem small_residue_height_power {k : ℕ} (hk : 8 ≤ k) {s r R : ℝ} (hs : 0 ≤ s)
    (hr : r^2=s^2+π^2) (hR : 0 ≤ R) (hminor : s^2+9*π^2 ≤ R^2)
    (hcap : R^2 ≤ r^2*(1+2/(k:ℝ))) :
    17≤s ∧ R^(k-1) ≤ s^(k-1)*(31/10) := by
  have hK : (8:ℝ)≤k := by exact_mod_cast hk
  have hK0 : (0:ℝ)<k := by linarith
  have hgap : (4*(k:ℝ)-1)*π^2 ≤ s^2 := by
    have hdiff : 8*π^2 ≤ r^2*(2/(k:ℝ)) := by
      rw [mul_add, mul_one] at hcap
      linarith only [hminor,hcap,hr]
    have hz := (le_div_iff₀ hK0).mp (show 8*π^2 ≤ 2*r^2/(k:ℝ) by convert hdiff using 1; ring)
    nlinarith only [hz,hr]
  have height : 17 ≤ s := by
    apply le_of_sq_le_sq _ hs
    have hb : (31:ℝ) ≤ 4*k-1 := by linarith
    nlinarith only [hgap,mul_le_mul_of_nonneg_right hb (sq_nonneg π),
      pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 3.14) (by linarith only [Real.pi_gt_d4] : (3.14:ℝ) ≤ π) 2]
  have hs' : 0<s := by linarith
  have hR' : 0<R := by nlinarith [sq_pos_of_pos hs',sq_nonneg π]
  have hf : R^2/s^2 ≤ (1+π^2/s^2)*(1+2/(k:ℝ)) := by
    apply (div_le_iff₀ (sq_pos_of_pos hs')).mpr
    rw [hr] at hcap
    have he : (1+π^2/s^2)*(1+2/(k:ℝ))*s^2=(s^2+π^2)*(1+2/(k:ℝ)) := by
      field_simp [hs'.ne']; ring
    rwa [he]
  rw [←div_pow] at hf
  have hl := Real.log_le_log (pow_pos (div_pos hR' hs') 2) hf
  rw [Real.log_pow,Real.log_mul (by positivity) (by positivity)] at hl
  have hlog : 2*log (R/s) ≤ π^2/s^2+2/(k:ℝ) := by
    linarith only [hl,log_le_sub_one_of_pos (show 0<1+π^2/s^2 by positivity),
      log_le_sub_one_of_pos (show (0:ℝ)<1+2/(k:ℝ) by positivity)]
  have hm : ((k-1:ℕ):ℝ)=(k:ℝ)-1 := by rw [Nat.cast_sub (by omega)]; norm_num
  have hrad : ((k:ℝ)-1)*(π^2/s^2) ≤ 1/4 := by
    rw [←mul_div_assoc]
    apply (div_le_div_iff₀ (sq_pos_of_pos hs') (by norm_num)).mpr
    nlinarith only [hgap,sq_nonneg π]
  have hder : ((k:ℝ)-1)*(2/(k:ℝ))≤2 := by
    rw [←mul_div_assoc]; exact (div_le_iff₀ hK0).mpr (by linarith)
  have hlogpow : log ((R/s)^(k-1)) ≤ 9/8 := by
    rw [log_pow,hm]
    nlinarith only [mul_le_mul_of_nonneg_left hlog (show 0≤(k:ℝ)-1 by linarith),hrad,hder]
  have hex : exp (9/8:ℝ) ≤ 31/10 := by
    have hl := Real.exp_bound' (x:=9/16) (by norm_num) (by norm_num) (n:=7) (by decide)
    norm_num [Finset.sum_range_succ,Nat.factorial] at hl
    rw [show (9/8:ℝ)=9/16+9/16 by norm_num,exp_add,←pow_two]
    exact (pow_le_pow_left₀ (exp_pos _).le (by linarith only [hl] : exp (9/16:ℝ) ≤ 44/25) 2).trans (by norm_num)
  refine ⟨height,?_⟩
  rw [mul_comm (s^(k-1)) _,←div_le_iff₀ (pow_pos hs' _),←div_pow]
  exact ((log_le_log_iff (pow_pos (div_pos hR' hs') _) (exp_pos _)).mp (by rwa [log_exp])).trans hex

#print axioms small_residue_height_power
end OpenMathResearch.LongCycleExcedances
