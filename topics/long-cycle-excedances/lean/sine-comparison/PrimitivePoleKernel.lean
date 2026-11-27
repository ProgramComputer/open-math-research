import PairedPoleConvergence
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real

def primitiveOddNumber (q : ℤ) : ℝ := 2*(q:ℝ)+1

theorem primitive_odd_abs_ge_one (q : ℤ) : (1:ℝ) ≤ |primitiveOddNumber q| := by
  have h : 1 ≤ |2*q+1| := by
    by_cases hi : 0 ≤ 2*q+1
    · rw [abs_of_nonneg hi]
      omega
    · rw [abs_of_neg (lt_of_not_ge hi)]
      omega
  unfold primitiveOddNumber
  exact_mod_cast h

def primitiveAngularPole (q : ℤ) (θ : ℝ) : ℂ :=
  (pairedPoleDenom (cos θ) (sin θ) q)⁻¹

private theorem primitive_pole_radius (q : ℤ) {θ : ℝ} (hS : 0 < sin θ) :
    let a := primitiveOddNumber q
    let ρ := ‖primitiveAngularPole q θ‖
    0 < ρ ∧ ρ^2 = (1+(a^2-1)*sin θ^2)⁻¹ := by
  let a := primitiveOddNumber q
  let w := pairedPoleDenom (cos θ) (sin θ) q
  let ρ := ‖primitiveAngularPole q θ‖
  have hw : w ≠ 0 := pairedPoleDenom_ne_zero _ hS.ne' q
  have hρ : 0 < ρ := norm_pos_iff.mpr (inv_ne_zero hw)
  have hwre : w.re = cos θ := by
    simp [w, pairedPoleDenom, Complex.add_re, Complex.mul_re, Complex.mul_im,
      ← Complex.ofReal_sin, ← Complex.ofReal_cos]
  have hwim : w.im = a*sin θ := by
    simp [a, primitiveOddNumber, w, pairedPoleDenom, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, ← Complex.ofReal_sin, ← Complex.ofReal_cos]
  have hwSq : Complex.normSq w = 1+(a^2-1)*sin θ^2 := by
    rw [Complex.normSq_apply, hwre, hwim]
    nlinarith only [Real.sin_sq_add_cos_sq θ]
  refine ⟨hρ,?_⟩
  change ‖w⁻¹‖^2 = _
  rw [norm_inv, inv_pow, Complex.sq_norm,hwSq]

theorem primitive_pow_bernoulli {ρ v c e : ℝ} (hρ : 0 < ρ) (hv : 0 ≤ v)
    (hs : ρ^2 = (1+v)⁻¹) {d : ℕ} (hd : 0 < d) (he : 2*(d:ℝ) ≤ e)
    (hc : 0 ≤ c) (hcv : c ≤ (e / (2*(d:ℝ)))*v) :
    ρ^e ≤ ((1+c)^d)⁻¹ := by
  have hd' : (0:ℝ) < d := by exact_mod_cast hd
  have hp : 1 ≤ e/(2*(d:ℝ)) := (le_div_iff₀ (by positivity)).mpr (by linarith only [he])
  have hb := (show 1+c ≤ 1+(e/(2*(d:ℝ)))*v by linarith only [hcv]).trans
    (one_add_mul_self_le_rpow_one_add (by linarith only [hv]) hp)
  have hb' := pow_le_pow_left₀ (by positivity : 0 ≤ 1+c) hb d
  have hv' : 0 < 1+v := by positivity
  have hc' : 0 < 1+c := by positivity
  have heq : ((1+v)^(e/(2*(d:ℝ))))^d = (ρ^e)⁻¹ := by
    have hbase : 1+v = (ρ^2)⁻¹ := by rw [hs,inv_inv]
    rw [←Real.rpow_mul_natCast hv'.le, hbase, Real.inv_rpow (sq_nonneg _),
      ←Real.rpow_natCast_mul hρ.le]
    congr 2
    field_simp [hd'.ne'] <;> ring
  rw [heq] at hb'
  have h := (inv_le_inv₀ (inv_pos.mpr (Real.rpow_pos_of_pos hρ _))
    (pow_pos hc' _)).mpr hb'
  simpa only [inv_inv] using h


theorem primitive_angular_bernoulli_kernel {n r : ℕ} (hn : 0 < n) (hr : 192 ≤ r)
    (q : ℤ) {θ y U : ℝ} (hS : 0 < sin θ)
    (hy : 0 ≤ y) (hyr : y ≤ (r:ℝ)/n) (hU : 0 ≤ U) (hUs : U ≤ (n:ℝ)*sin θ^2) :
    let ρ := ‖primitiveAngularPole q θ‖
    let v := primitiveOddNumber q ^ 2 - 1
    let c := y*U/192
    ρ^r ≤ ((1+c*v)^96)⁻¹ := by
  let ρ := ‖primitiveAngularPole q θ‖
  let v := primitiveOddNumber q ^ 2 - 1
  let c := y*U/192
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hr' : (192:ℝ) ≤ r := by exact_mod_cast hr
  have hv : 0 ≤ v := sub_nonneg.mpr (by
    simpa only [one_pow,sq_abs] using
      pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) (primitive_odd_abs_ge_one q) 2)
  have hvs : 0 ≤ v*sin θ^2 := mul_nonneg hv (sq_nonneg _)
  have ho := primitive_pole_radius q hS
  have hs : ρ^2 = (1+v*sin θ^2)⁻¹ := ho.2
  have ht : y*U ≤ (r:ℝ)*sin θ^2 := calc
    _ ≤ y*((n:ℝ)*sin θ^2) := mul_le_mul_of_nonneg_left hUs hy
    _ = (y*(n:ℝ))*sin θ^2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right ((le_div_iff₀ hn').mp hyr) (sq_nonneg _)
  have hcv : c*v ≤ ((r:ℝ)/192)*(v*sin θ^2) := calc
    _ = y*U*v/192 := by dsimp only [c]; ring
    _ ≤ (r:ℝ)*sin θ^2*v/192 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ht hv) (by norm_num)
    _ = _ := by ring
  have hc : 0 ≤ c*v := mul_nonneg (div_nonneg (mul_nonneg hy hU) (by norm_num)) hv
  have hr96 : 2*((96:ℕ):ℝ) ≤ (r:ℝ) := by
    norm_num only [Nat.cast_ofNat]
    linarith only [hr']
  have he96 : (r:ℝ)/(2*((96:ℕ):ℝ)) = (r:ℝ)/192 := by norm_num
  change ρ^r ≤ ((1+c*v)^96)⁻¹
  rw [← Real.rpow_natCast]
  exact primitive_pow_bernoulli ho.1 hvs hs (by decide : 0 < 96) hr96 hc (by rwa [he96])

#print axioms primitive_angular_bernoulli_kernel
end OpenMathResearch.LongCycleExcedances
