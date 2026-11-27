import RepositoryPrincipalFactor
import PairedPoleConvergence

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset Filter
open scoped PowerSeries Topology

/-- The pole q=0 represents the signed odd integer +1. Its denominator has
minimal norm, including the conjugate denominator at q=-1. -/
theorem principal_pole_ratio_norm_le (C : ℝ) {S : ℝ} (hS : S ≠ 0) (q : ℤ) :
    ‖pairedPoleDenom C S 0 / pairedPoleDenom C S q‖ ≤ 1 := by
  have hpos := norm_pos_iff.mpr (pairedPoleDenom_ne_zero C hS q)
  rw [norm_div,div_le_one hpos]
  have hreal (q : ℤ) : ‖pairedPoleDenom C S q‖^2 = C^2+((2*(q:ℝ)+1)*S)^2 := by
    rw [Complex.sq_norm,Complex.normSq_apply]
    simp [pairedPoleDenom,Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im]
    ring
  have ho : (1:ℤ) ≤ |2*q+1| := Int.add_one_le_iff.mpr (abs_pos.mpr (by omega))
  have hr : (1:ℝ) ≤ |2*(q:ℝ)+1| := by exact_mod_cast ho
  have hs := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hr 2
  rw [sq_abs] at hs
  have hq : ‖pairedPoleDenom C S 0‖^2 ≤ ‖pairedPoleDenom C S q‖^2 := by
    rw [hreal,hreal]
    simp only [Int.cast_zero,mul_zero,zero_add,one_mul,mul_pow]
    nlinarith only [mul_nonneg (sub_nonneg.mpr hs) (sq_nonneg S)]
  nlinarith only [hq,norm_nonneg (pairedPoleDenom C S 0),norm_nonneg (pairedPoleDenom C S q),
    sq_nonneg (‖pairedPoleDenom C S 0‖-‖pairedPoleDenom C S q‖)]

private theorem pole_gap_norm_lower (C : ℝ) {S : ℝ} {a q : ℤ} (hqa : q ≠ a) :
    2*|S| ≤ ‖pairedPoleDenom C S q-pairedPoleDenom C S a‖ := by
  have hp : (1:ℝ) ≤ |((q-a:ℤ):ℝ)| := by
    rw [←Int.cast_abs]
    exact_mod_cast (Int.add_one_le_iff.mpr (abs_pos.mpr (sub_ne_zero.mpr hqa)) : (1:ℤ) ≤ |q-a|)
  rw [pairedPoleDenom_sub,norm_mul,norm_mul,norm_mul,Complex.norm_I,one_mul,
    show ‖(2:ℂ)‖=2 by norm_num,←Int.cast_sub,Complex.norm_intCast,Complex.norm_real,Real.norm_eq_abs]
  nlinarith only [mul_nonneg (sub_nonneg.mpr hp) (abs_nonneg S)]

/-- All nonprincipal logarithms in the +1 residue form an absolutely summable family. -/
theorem principal_log_lattice_summable (j : ℕ) (C : ℝ) {S : ℝ} (hS : S ≠ 0) :
    Summable (fun q : {q : ℤ // q ≠ 0} =>
      ‖principalLogIntegral j (pairedPoleDenom C S 0 / pairedPoleDenom C S q)‖) := by
  let A := pairedPoleDenom C S 0
  let K := 1+‖A‖/(2*|S|)
  have hsep : 0 < 2*|S| := mul_pos (by norm_num) (abs_pos.mpr hS)
  have hpow := (summable_paired_pole_power_norm C hS (p:=j+2) (by omega)).subtype
    (fun q : ℤ => q ≠ 0)
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    ?_ (show Summable (fun q : {q : ℤ // q ≠ 0} =>
      (K*‖A‖^(j+2))*‖(pairedPoleDenom C S q)⁻¹‖^(j+2)) from hpow.mul_left _)
  intro q
  let B := pairedPoleDenom C S q
  have hb : B ≠ 0 := pairedPoleDenom_ne_zero C hS q
  have ha : A ≠ B := (pairedPoleDenom_injective C hS).ne q.property.symm
  have hv1 : A/B ≠ 1 := by intro h; exact ha (by simpa using (div_eq_iff hb).mp h)
  have hba : B-A ≠ 0 := sub_ne_zero.mpr ha.symm
  have hd : 0 < ‖1-A/B‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hv1.symm)
  have hgap : 2*|S| ≤ ‖B-A‖ := pole_gap_norm_lower C q.property
  have he : (1-A/B)⁻¹ = 1+A/(B-A) := by field_simp [hb,hba,sub_ne_zero.mpr hv1.symm]
  have hrecip : 1/‖1-A/B‖ ≤ K := by
    rw [one_div,←norm_inv,he]
    calc
      _ ≤ ‖(1:ℂ)‖+‖A/(B-A)‖ := norm_add_le _ _
      _ ≤ K := by rw [norm_one,norm_div]; exact add_le_add_left
                    (div_le_div_of_nonneg_left (norm_nonneg A) hsep hgap) _
  have hnorm := principal_log_integral_bound j (principal_pole_ratio_norm_le C hS q) hv1
  have hj : 1 ≤ (j:ℝ)+1 := by have h : (0:ℝ) ≤ j := Nat.cast_nonneg j; linarith
  calc
    _ ≤ ‖A/B‖^(j+2)/(((j:ℝ)+1)*‖1-A/B‖) := hnorm
    _ ≤ ‖A/B‖^(j+2)/‖1-A/B‖ := div_le_div_of_nonneg_left (by positivity) hd
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hj hd.le)
    _ ≤ ‖A/B‖^(j+2)*K := by
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left (by simpa only [one_div] using hrecip) (by positivity)
    _ = _ := by rw [div_eq_mul_inv,norm_mul,mul_pow]; ring

theorem principal_lattice_factors_hasProd (j : ℕ) (C : ℝ) {S : ℝ} (hS : S ≠ 0) :
    let A := pairedPoleDenom C S 0
    let L := fun q : {q : ℤ // q ≠ 0} => principalLogIntegral j (A / pairedPoleDenom C S q)
    HasProd (fun q : {q : ℤ // q ≠ 0} =>
      ∑' n, PowerSeries.coeff (R := ℂ) n (1+occupiedPrimitive (j+2) C S 0 q) * A^n)
      (Complex.exp (∑' q, L q)) := by
  dsimp only
  have h := ((principal_log_lattice_summable j C hS).of_norm.hasSum).cexp
  apply h.congr_fun
  intro q
  exact (occupied_factor_hasSum_integral j C hS q.property.symm
    (principal_pole_ratio_norm_le C hS q)).tsum_eq


/-- At unit principal radius one power of the pole denominator cancels exactly. -/
theorem principal_log_lattice_single_bound (j : ℕ) (C : ℝ) {S : ℝ} (hS : S ≠ 0)
    (hunit : ‖pairedPoleDenom C S 0‖=1) {q : ℤ} (hq : q ≠ 0) :
    ‖principalLogIntegral j (pairedPoleDenom C S 0 / pairedPoleDenom C S q)‖ ≤
      ‖(pairedPoleDenom C S q)⁻¹‖^(j+1)/(((j:ℝ)+1)*(2*|(q:ℝ)| * |S|)) := by
  let A := pairedPoleDenom C S 0
  let B := pairedPoleDenom C S q
  have hb : B ≠ 0 := pairedPoleDenom_ne_zero C hS q
  have ha : A ≠ B := (pairedPoleDenom_injective C hS).ne hq.symm
  have hv1 : A/B ≠ 1 := by intro h; exact ha (by simpa using (div_eq_iff hb).mp h)
  have hBA : ‖B-A‖=2*|(q:ℝ)| * |S| := by
    dsimp only [A,B]
    rw [pairedPoleDenom_sub,norm_mul,norm_mul,norm_mul,Complex.norm_I,one_mul,
      show ‖(2:ℂ)‖=2 by norm_num,Int.cast_zero,sub_zero,Complex.norm_intCast,Complex.norm_real,
      Real.norm_eq_abs]
  have hid : 1-A/B = (B-A)/B := by field_simp
  have hQ := principal_log_integral_bound j (principal_pole_ratio_norm_le C hS q) hv1
  calc
    _ ≤ ‖A/B‖^(j+2)/(((j:ℝ)+1)*‖1-A/B‖) := hQ
    _ = _ := by
      rw [hid,norm_div,norm_div,hBA,show ‖A‖=1 from hunit,norm_inv,one_div]
      have hb' : ‖B‖ ≠ 0 := norm_ne_zero_iff.mpr hb
      change ‖B‖⁻¹ ^ (j+2) / _ = ‖B‖⁻¹ ^ (j+1) / _
      rw [pow_succ _ (j+1)]
      field_simp
      ring

/-- A scalar upper bound on the weighted signed-pole sum supplies the
lower bound for the real part of the actual principal product. -/
theorem principal_product_re_of_lattice_majorant (j : ℕ) (C : ℝ) {S η : ℝ}
    (hS : S ≠ 0) (hunit : ‖pairedPoleDenom C S 0‖=1) (he : η ≤ 81/100)
    (hmajor : Summable (fun q : {q : ℤ // q ≠ 0} =>
      ‖(pairedPoleDenom C S q)⁻¹‖^(j+1)/(((j:ℝ)+1)*(2*|((q:ℤ):ℝ)| * |S|))))
    (hbound : (∑' q : {q : ℤ // q ≠ 0},
      ‖(pairedPoleDenom C S q)⁻¹‖^(j+1)/(((j:ℝ)+1)*(2*|((q:ℤ):ℝ)| * |S|))) ≤ η) :
    Real.exp (-η) ≤ (∏' q : {q : ℤ // q ≠ 0}, ∑' n,
      PowerSeries.coeff (R := ℂ) n (1+occupiedPrimitive (j+2) C S 0 q) *
        (pairedPoleDenom C S 0)^n).re := by
  rw [(principal_lattice_factors_hasProd j C hS).tprod_eq]
  apply principal_disk_exp_re he
  exact (norm_tsum_le_tsum_norm (principal_log_lattice_summable j C hS)).trans
    (((principal_log_lattice_summable j C hS).tsum_le_tsum
      (fun q => principal_log_lattice_single_bound j C hS hunit q.property) hmajor).trans hbound)

#print axioms principal_log_lattice_single_bound
#print axioms principal_product_re_of_lattice_majorant

#print axioms principal_pole_ratio_norm_le
#print axioms principal_log_lattice_summable
#print axioms principal_lattice_factors_hasProd
end OpenMathResearch.LongCycleExcedances
