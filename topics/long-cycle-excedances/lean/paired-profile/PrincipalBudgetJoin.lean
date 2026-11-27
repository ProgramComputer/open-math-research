import PrincipalLatticeProduct
import PrimitivePoleKernel
import ReflectedLogBudget
import ReflectedLogSum

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real

private theorem principal_angular_unit (θ : ℝ) :
    ‖pairedPoleDenom (cos θ) (sin θ) 0‖ = 1 := by
  have h : ‖pairedPoleDenom (cos θ) (sin θ) 0‖^2 = 1 := by
    rw [Complex.sq_norm,Complex.normSq_apply]
    simp [pairedPoleDenom,Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,
        ← Complex.ofReal_sin,← Complex.ofReal_cos]
    nlinarith only [sin_sq_add_cos_sq θ]
  nlinarith only [h,norm_nonneg (pairedPoleDenom (cos θ) (sin θ) 0)]

def principalAngularLogNorm (j : ℕ) (θ : ℝ) (q : {q : ℤ // q ≠ 0}) : ℝ :=
  ‖principalLogIntegral j
    (pairedPoleDenom (cos θ) (sin θ) 0 / pairedPoleDenom (cos θ) (sin θ) q)‖

private theorem weighted_log_bound {n j : ℕ} (hn : 0 < n) (hr : 192 ≤ j+1)
    {θ h A : ℝ} (hS : 0 < sin θ) (hangle : 6/5 ≤ (n:ℝ)*sin θ^2)
    (hh : 0 < h) (hyr : 40*h ≤ ((j:ℝ)+1)/n) (hA : 0 < A) (hAS : A ≤ ((j:ℝ)+1)*sin θ)
    (q : {q : ℤ // q ≠ 0}) :
    principalAngularLogNorm j θ q ≤
      ((1+h*(q:ℤ)*((q:ℤ)+1:ℝ))^96)⁻¹/(2*|((q:ℤ):ℝ)| * A) := by
  have hw := primitive_angular_bernoulli_kernel (r:=j+1) hn hr q hS
    (y:=40*h) (by positivity) (by simpa using hyr) (U:=6/5) (by norm_num) hangle
  have hid : 1 + 40*h*(6/5)/192 * (primitiveOddNumber q^2-1) =
        1+h*(q:ℤ)*((q:ℤ)+1:ℝ) := by unfold primitiveOddNumber; ring
  change ‖(pairedPoleDenom (cos θ) (sin θ) q)⁻¹‖^(j+1) ≤ _ at hw
  rw [hid] at hw
  have hq : (0:ℝ) < |((q:ℤ):ℝ)| := abs_pos.mpr (by exact_mod_cast q.property)
  have hd : 2*|((q:ℤ):ℝ)| * A ≤ ((j:ℝ)+1)*(2*|((q:ℤ):ℝ)| * |sin θ|) := by
    rw [abs_of_pos hS]
    nlinarith only [mul_nonneg hq.le (sub_nonneg.mpr hAS)]
  have hsingle := principal_log_lattice_single_bound j (cos θ) hS.ne'
    (principal_angular_unit θ) q.property
  apply hsingle.trans
  exact div_le_div₀ (by positivity) hw (by positivity) hd

theorem principal_angular_budget {n j : ℕ} (hn : 0 < n) (hr : 192 ≤ j+1)
    {θ h A η : ℝ} (hS : 0 < sin θ) (hangle : 6/5 ≤ (n:ℝ)*sin θ^2)
    (hh : 0 < h) (hyr : 40*h ≤ ((j:ℝ)+1)/n) (hA : 0 < A) (hAS : A ≤ ((j:ℝ)+1)*sin θ)
    (hnum : (1 + ∑' i, reflectedLogWeight h (i+1))/(2*A) ≤ η) :
    (∑' q, principalAngularLogNorm j θ q) ≤ η := by
  apply reflected_log_bound_of_pair (principal_log_lattice_summable j (cos θ) hS.ne')
    hh hA _ _ hnum
  · have h := weighted_log_bound hn hr hS hangle hh hyr hA hAS (negLogIndex 0)
    simpa [principalAngularLogNorm,negLogIndex] using h
  · intro i
    have hp := weighted_log_bound hn hr hS hangle hh hyr hA hAS (posLogIndex i)
    have hm := weighted_log_bound hn hr hS hangle hh hyr hA hAS (negLogIndex (i+1))
    apply (add_le_add hp hm).trans_eq
    simp only [posLogIndex,negLogIndex,Int.cast_add,Int.cast_one,Int.cast_natCast,Int.cast_negSucc,Nat.cast_add,Nat.cast_one,
      abs_neg,abs_of_nonneg (by positivity : (0:ℝ) ≤ (i:ℝ)+1),
      abs_of_nonneg (by positivity : (0:ℝ) ≤ (i:ℝ)+1+1)]
    let t : ℝ := i+1
    have ht : 0 < t := by dsimp [t]; positivity
    change ((1+h*t*(t+1))^96)⁻¹ / (2*t*A) +
      ((1+h*(-(t+1))*(-(t+1)+1))^96)⁻¹ / (2*(t+1)*A) = _
    rw [show 1+h*(-(t+1))*(-(t+1)+1)=1+h*t*(t+1) by ring]
    simp only [reflectedLogWeight,Nat.cast_add,Nat.cast_one]
    change _ = ((1/t+1/(t+1))/(1+h*t*(t+1))^96)/(2*A)
    generalize (1+h*t*(t+1))^96 = b
    by_cases hb : b=0
    · simp [hb]
    · field_simp [ht.ne',hA.ne',hb,show t+1 ≠ 0 by positivity] <;> ring

private theorem size_budgets {n j : ℕ} {X h A θ : ℝ}
    (hn : 10000 ≤ n) (hX : 0 < X) (hkn : (n:ℝ) ≤ X*((j:ℝ)+2))
    (hS : 0 < sin θ) (hangle : 6/5 ≤ (n:ℝ)*sin θ^2)
    (hc : 40*h ≤ 1/X-1/10000) (hA : A ≤ (5477/50)*(1/X-1/10000)) :
    40*h ≤ ((j:ℝ)+1)/n ∧ A ≤ ((j:ℝ)+1)*sin θ := by
  have hn' : (10000:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := by linarith
  have hfrac : 1/X ≤ ((j:ℝ)+2)/n := by
    apply (div_le_div_iff₀ hX hn0).mpr
    linarith
  have hrec : 1/(n:ℝ) ≤ 1/10000 := one_div_le_one_div_of_le (by norm_num) hn'
  have hy : 1/X-1/10000 ≤ ((j:ℝ)+1)/n := by
    calc
      _ ≤ ((j:ℝ)+2)/n-1/n := sub_le_sub hfrac hrec
      _ = _ := by ring
  refine ⟨hc.trans hy,?_⟩
  have hns : (5477/50:ℝ) ≤ n*sin θ := by
    have hsq := mul_le_mul_of_nonneg_left hangle hn0.le
    nlinarith only [hsq,hn',mul_pos hn0 hS, sq_nonneg (n*sin θ - 5477/50)]
  apply hA.trans
  have hpos : 0 ≤ ((j:ℝ)+1)/n := by positivity
  calc
    _ ≤ (5477/50)*(((j:ℝ)+1)/n) := mul_le_mul_of_nonneg_left hy (by norm_num)
    _ ≤ ((n:ℝ)*sin θ)*(((j:ℝ)+1)/n) := mul_le_mul_of_nonneg_right hns hpos
    _ = _ := by field_simp <;> ring

theorem actual_principal_real_bound_all {n j : ℕ} {θ : ℝ}
    (hn : 10000 ≤ n) (hkn : n ≤ 48*(j+2)) (hS : 0 < sin θ)
    (hangle : 6/5 ≤ (n:ℝ)*sin θ^2) :
    Real.exp (-(4/5)) ≤ (∏' q : {q : ℤ // q ≠ 0}, ∑' m,
      PowerSeries.coeff (R := ℂ) m (1+occupiedPrimitive (j+2) (cos θ) (sin θ) 0 q) *
        (pairedPoleDenom (cos θ) (sin θ) 0)^m).re := by
  rw [(principal_lattice_factors_hasProd j (cos θ) hS.ne').tprod_eq]
  apply principal_disk_exp_re (by norm_num)
  apply (norm_tsum_le_tsum_norm (principal_log_lattice_summable j (cos θ) hS.ne')).trans
  have hb := size_budgets (X:=48) (h:=1/1940) (A:=227/100) hn (by norm_num)
    (by exact_mod_cast hkn) hS hangle (by norm_num) (by norm_num)
  exact principal_angular_budget (n:=n) (j:=j) (by omega) (by omega) hS hangle
    (by norm_num) hb.1 (by norm_num) hb.2 reflected_log_all_budget

theorem actual_principal_real_bound_low {n j : ℕ} {θ : ℝ}
    (hn : 10000 ≤ n) (hkn : n ≤ 10*(j+2)) (hS : 0 < sin θ)
    (hangle : 6/5 ≤ (n:ℝ)*sin θ^2) :
    Real.exp (-(1/10)) ≤ (∏' q : {q : ℤ // q ≠ 0}, ∑' m,
      PowerSeries.coeff (R := ℂ) m (1+occupiedPrimitive (j+2) (cos θ) (sin θ) 0 q) *
        (pairedPoleDenom (cos θ) (sin θ) 0)^m).re := by
  rw [(principal_lattice_factors_hasProd j (cos θ) hS.ne').tprod_eq]
  apply principal_disk_exp_re (by norm_num)
  apply (norm_tsum_le_tsum_norm (principal_log_lattice_summable j (cos θ) hS.ne')).trans
  have hb := size_budgets (X:=10) (h:=1/405) (A:=109/10) hn (by norm_num)
    (by exact_mod_cast hkn) hS hangle (by norm_num) (by norm_num)
  exact principal_angular_budget (n:=n) (j:=j) (by omega) (by omega) hS hangle
    (by norm_num) hb.1 (by norm_num) hb.2 reflected_log_low_budget

#print axioms actual_principal_real_bound_all
#print axioms actual_principal_real_bound_low
end OpenMathResearch.LongCycleExcedances
