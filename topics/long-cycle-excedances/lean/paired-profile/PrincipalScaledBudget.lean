import PrincipalBudgetJoin
import PrincipalHarmonic

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real
open scoped PowerSeries

private theorem principal_exp_small : exp (1/10) < 10/9 := by
  have hid : exp (1/10)^10 = exp 1 := by rw [←Real.exp_nat_mul]; norm_num
  by_contra! h
  have he := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 10/9) h 10
  rw [hid] at he
  have hlt : exp 1 < (10/9:ℝ)^10 := by linarith only [Real.exp_one_lt_d9]
  exact (not_lt_of_ge he) hlt

private theorem principal_exp_large : exp (4/5) < 1113/500 := by
  have he : exp 1 < (27183/10000:ℝ) := by linarith only [Real.exp_one_lt_d9]
  have hpow := pow_lt_pow_left₀ he (exp_pos _).le (by decide : (4:ℕ) ≠ 0)
  have hprec : (27183/10000:ℝ)^4 < (1113/500:ℝ)^5 := by norm_num
  have hid : exp (4/5)^5 = exp 1^4 := by
    rw [←Real.exp_nat_mul,←Real.exp_nat_mul]
    norm_num
  by_contra! h
  exact (not_lt_of_ge (hid ▸ pow_le_pow_left₀ (by norm_num) h 5)) (hpow.trans hprec)

def originalScaledPrincipal (j : ℕ) (θ : ℝ) : ℝ :=
  2*(j+2:ℕ)*exp (-cycleHarmonic ((j+2)-1)) * (∏' q : {q : ℤ // q ≠ 0}, ∑' m,
    PowerSeries.coeff (R := ℂ) m (1+occupiedPrimitive (j+2) (cos θ) (sin θ) 0 q) *
      (pairedPoleDenom (cos θ) (sin θ) 0)^m).re

theorem original_scaled_principal_all {n j : ℕ} {θ : ℝ} (hn : 10000 ≤ n)
    (hkn : n ≤ 48*(j+2)) (hS : 0 < sin θ) (hangle : 6/5 ≤ (n:ℝ)*sin θ^2) :
    6000/12243 < originalScaledPrincipal j θ := by
  have hp := principal_harmonic_prefactor (k:=j+2) (by omega)
  have hr := actual_principal_real_bound_all hn hkn hS hangle
  have hinv : (500/1113:ℝ) < exp (-(4/5)) := by
    rw [exp_neg,← one_div,lt_div_iff₀ (exp_pos _)]
    linarith only [principal_exp_large]
  have h := mul_lt_mul_of_pos_right hp (lt_of_lt_of_le (exp_pos _) hr)
  have h' := mul_lt_mul_of_pos_left (hinv.trans_le hr) (by norm_num : (0:ℝ)<12/11)
  apply lt_of_eq_of_lt _ (h'.trans h)
  norm_num

theorem original_scaled_principal_low {n j : ℕ} {θ : ℝ} (hn : 10000 ≤ n)
    (hkn : n ≤ 10*(j+2)) (hS : 0 < sin θ) (hangle : 6/5 ≤ (n:ℝ)*sin θ^2) :
    54/55 < originalScaledPrincipal j θ := by
  have hp := principal_harmonic_prefactor (k:=j+2) (by omega)
  have hr := actual_principal_real_bound_low hn hkn hS hangle
  have hinv : (9/10:ℝ) < exp (-(1/10)) := by
    rw [exp_neg,← one_div,lt_div_iff₀ (exp_pos _)]
    linarith only [principal_exp_small]
  have h := mul_lt_mul_of_pos_right hp (lt_of_lt_of_le (exp_pos _) hr)
  have h' := mul_lt_mul_of_pos_left (hinv.trans_le hr) (by norm_num : (0:ℝ)<12/11)
  apply lt_of_eq_of_lt _ (h'.trans h)
  norm_num

#print axioms original_scaled_principal_all
#print axioms original_scaled_principal_low
end OpenMathResearch.LongCycleExcedances
