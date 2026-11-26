import CatalanStrictPeaksNearPoleSeries
import Mathlib.Tactic.FieldSimp

/-!
# The formal inverse square root for the Catalan cutoff

The inverse branch is specified by a coefficient recurrence. The Euler
derivation turns that recurrence into a first-order identity and verifies
the square-root and reciprocal equations in the formal series ring.
-/

namespace CatalanStrictPeaks.NearPoleSeries

open Finset
open scoped BigOperators

local notation "S" => PowerSeries ℝ
local notation "x" => (PowerSeries.X : S)
local notation "c" => PowerSeries.C ℝ

noncomputable def invRootCoeff : ℕ → ℝ
  | 0 => 1
  | 1 => -1/4
  | n+2 => -(((2*(n:ℝ)+3)/2)*invRootCoeff (n+1) +
      (2*(n:ℝ)+2)*(9/16)*invRootCoeff n)/(2*((n:ℝ)+2))

noncomputable def Ri : S := PowerSeries.mk invRootCoeff

noncomputable def R : S := Q * Ri

@[simp] theorem coeff_Ri (n : ℕ) :
    PowerSeries.coeff ℝ n Ri = invRootCoeff n := PowerSeries.coeff_mk _ _

@[simp] theorem invRootCoeff_zero : invRootCoeff 0 = 1 := rfl

@[simp] theorem invRootCoeff_one : invRootCoeff 1 = -1/4 := rfl

theorem invRootCoeff_succ_succ (n : ℕ) :
    invRootCoeff (n+2) = -(((2*(n:ℝ)+3)/2)*invRootCoeff (n+1) +
      (2*(n:ℝ)+2)*(9/16)*invRootCoeff n)/(2*((n:ℝ)+2)) := rfl

private noncomputable def theta (f : S) : S :=
  PowerSeries.mk fun n => (n : ℝ) * PowerSeries.coeff ℝ n f

@[simp] private theorem coeff_theta (n : ℕ) (f : S) :
    PowerSeries.coeff ℝ n (theta f) = (n : ℝ) * PowerSeries.coeff ℝ n f :=
  PowerSeries.coeff_mk _ _

private theorem theta_mul (f g : S) :
    theta (f*g) = theta f*g + f*theta g := by
  ext n
  simp only [coeff_theta, map_add, PowerSeries.coeff_mul]
  rw [mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro i hi
  have hij : (i.1 : ℝ) + (i.2 : ℝ) = (n : ℝ) := by
    exact_mod_cast Finset.mem_antidiagonal.mp hi
  rw [← hij]
  ring

private theorem theta_Q :
    theta Q = c (1/2)*x + c (9/8)*x^2 := by
  ext n
  simp only [Q, coeff_theta, map_add, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X, PowerSeries.coeff_X_pow, PowerSeries.coeff_one]
  by_cases h₀ : n = 0
  · norm_num [h₀]
  by_cases h₁ : n = 1
  · norm_num [h₁]
  by_cases h₂ : n = 2
  · norm_num [h₂]
  simp [h₀, h₁, h₂]

private theorem coeff_x_mul (f : S) (n : ℕ) :
    PowerSeries.coeff ℝ n (x*f) =
      if 1 ≤ n then PowerSeries.coeff ℝ (n-1) f else 0 := by
  simpa only [pow_one] using PowerSeries.coeff_X_pow_mul' f 1 n

private theorem theta_Ri_equation : 2*Q*theta Ri + theta Q*Ri = 0 := by
  rw [theta_Q]
  have hs :
      2*Q*theta Ri + (c (1/2)*x + c (9/8)*x^2)*Ri =
        c 2 * theta Ri + c 2*(c (1/2)*(x*theta Ri)) +
        c 2*(c (9/16)*(x^2*theta Ri)) + c (1/2)*(x*Ri) + c (9/8)*(x^2*Ri) := by
    unfold Q
    rw [map_ofNat]
    ring
  rw [hs]
  ext n
  simp only [map_add, PowerSeries.coeff_C_mul, coeff_x_mul,
    PowerSeries.coeff_X_pow_mul', coeff_theta, coeff_Ri, map_zero]
  obtain _ | _ | n := n
  · norm_num
  · norm_num
  · rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega)]
    have hden : (2 : ℝ)*((n : ℝ)+2) ≠ 0 := by
      exact mul_ne_zero (by norm_num) (ne_of_gt (add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) (by norm_num)))
    have he := (eq_div_iff hden).mp (invRootCoeff_succ_succ n)
    simp only [show n.succ.succ - 1 = n+1 by omega,
      show n.succ.succ - 2 = n by omega, Nat.cast_succ]
    linear_combination he

@[simp] theorem constantCoeff_Q : PowerSeries.constantCoeff ℝ Q = 1 := by
  simp [Q]

@[simp] theorem constantCoeff_Ri : PowerSeries.constantCoeff ℝ Ri = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_Ri, invRootCoeff_zero]

@[simp] theorem constantCoeff_R : PowerSeries.constantCoeff ℝ R = 1 := by
  simp [R]

private theorem Q_mul_Ri_sq : Q*Ri^2 = 1 := by
  have h : theta (Q*Ri^2) = 0 := by
    simp only [pow_two, theta_mul]
    linear_combination Ri*theta_Ri_equation
  ext n
  cases n with
  | zero => simp [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  | succ n =>
    have hh := congrArg (PowerSeries.coeff ℝ (n+1)) h
    simp only [coeff_theta, map_zero] at hh
    rw [PowerSeries.coeff_one, if_neg (Nat.succ_ne_zero n)]
    exact (mul_eq_zero.mp hh).resolve_left (by exact_mod_cast Nat.succ_ne_zero n)

theorem R_mul_Ri : R*Ri = 1 := by
  simpa only [R, pow_two, mul_assoc] using Q_mul_Ri_sq

theorem R_sq : R^2 = Q := by
  unfold R
  rw [mul_pow, pow_two Q, mul_assoc, Q_mul_Ri_sq, mul_one]

/-- Pole formula for the original word evaluator with the explicit branch. -/
theorem F_tau_eq_radical : F_tau = H R * geo a :=
  F_tau_eq constantCoeff_R R_sq

/-- Pole formula for the strict-peak-variable derivative with the explicit branch. -/
theorem DtF_tau_eq_radical :
    DtF_tau = (c (1/2)*x)*geo a + 4*B Ri*geo b -
      3*B Ri*geo a - x*H R*(geo a)^2 :=
  DtF_tau_eq constantCoeff_R R_sq R_mul_Ri


end CatalanStrictPeaks.NearPoleSeries
