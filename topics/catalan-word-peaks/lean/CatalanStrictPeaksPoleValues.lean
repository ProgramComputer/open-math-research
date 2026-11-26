import CatalanStrictPeaksPoleSeriesBounds
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Values of the two formal pole numerators

Absolute summability lets us evaluate the checked formal radical identities.
The already positive value of the inverse branch selects the positive square
root. All required polynomial evaluations are finite.
-/

namespace CatalanStrictPeaks.NearPoleSeries

local notation "S" => PowerSeries ℝ
local notation "x" => (PowerSeries.X : S)
local notation "c" => PowerSeries.C ℝ
local notation "cf" => PowerSeries.coeff ℝ

/-- Evaluating by a convergent Taylor series with explicitly specified sum. -/
abbrev PoleHasSum (P : S) (t y : ℝ) := HasSum (fun n => cf n P * t^n) y

private theorem eval_X_mul {P : S} {t y : ℝ} (hp : PoleHasSum P t y) :
    PoleHasSum (x*P) t (t*y) := by
  have h : HasSum (fun n => cf (n+1) (x*P) * t^(n+1)) (t*y) := by
    refine (hp.mul_left t).congr_fun ?_
    intro n
    rw [PowerSeries.coeff_succ_X_mul, pow_succ]
    ring
  simpa only [Finset.sum_range_one, PowerSeries.coeff_zero_eq_constantCoeff, map_mul,
    PowerSeries.constantCoeff_X, zero_mul, pow_zero, mul_one, add_zero] using
    (hasSum_nat_add_iff (f := fun n => cf n (x*P) * t^n) 1).mp h

private theorem eval_C_mul {P : S} {t y v : ℝ} (hp : PoleHasSum P t y) :
    PoleHasSum (c v*P) t (v*y) := by
  simpa only [PoleHasSum, PowerSeries.coeff_C_mul, mul_assoc] using hp.mul_left v

private theorem eval_sub {P T : S} {t y z : ℝ}
    (hp : PoleHasSum P t y) (hq : PoleHasSum T t z) : PoleHasSum (P-T) t (y-z) := by
  simpa only [PoleHasSum, map_sub, sub_mul] using hp.sub hq

private theorem eval_add {P T : S} {t y z : ℝ}
    (hp : PoleHasSum P t y) (hq : PoleHasSum T t z) : PoleHasSum (P+T) t (y+z) := by
  simpa only [PoleHasSum, map_add, add_mul] using hp.add hq

private theorem eval_one (t : ℝ) : PoleHasSum (1 : S) t 1 := by
  refine (hasSum_ite_eq (0 : ℕ) (1 : ℝ)).congr_fun ?_
  intro n
  by_cases hn : n = 0
  · simp [hn]
  · simp [PowerSeries.coeff_one, hn]

private theorem eval_x (t : ℝ) : PoleHasSum x t t := by
  simpa only [mul_one] using eval_X_mul (eval_one t)

private theorem eval_x_sq (t : ℝ) : PoleHasSum (x^2) t (t^2) := by
  simpa only [pow_two] using eval_X_mul (eval_x t)

private theorem eval_X_cancel {P : S} {t y : ℝ} (ht : t ≠ 0)
    (hp : PoleHasSum (x*P) t y) : PoleHasSum P t (y/t) := by
  have h := (hasSum_nat_add_iff' 1).mpr hp
  simp only [Finset.sum_range_one, PowerSeries.coeff_zero_eq_constantCoeff, map_mul,
    PowerSeries.constantCoeff_X, zero_mul, pow_zero, mul_one, sub_zero] at h
  refine (h.mul_right t⁻¹).congr_fun ?_
  intro n
  rw [PowerSeries.coeff_succ_X_mul, pow_succ]
  field_simp
  ring

theorem value_one (t : ℝ) : poleValue 1 t = 1 := (eval_one t).tsum_eq

theorem value_Q (t : ℝ) : poleValue Q t = 1 + t/2 + (9/16)*t^2 := by
  have h := eval_add (eval_add (eval_one t) (eval_C_mul (v := 1/2) (eval_x t)))
    (eval_C_mul (v := 9/16) (eval_x_sq t))
  unfold Q
  convert h.tsum_eq using 1
  ring

theorem poleValue_R_mul_Ri {t : ℝ}
    (hR : Summable (fun n => ‖cf n R * t^n‖))
    (hi : Summable (fun n => ‖cf n Ri * t^n‖)) :
    poleValue R t * poleValue Ri t = 1 := by
  rw [← value_mul hR hi, R_mul_Ri, value_one]

theorem poleValue_R_sq {t : ℝ}
    (hR : Summable (fun n => ‖cf n R * t^n‖)) :
    poleValue R t ^ 2 = 1 + t/2 + (9/16)*t^2 := by
  rw [pow_two, ← value_mul hR hR, ← pow_two, R_sq, value_Q]

theorem poleValue_R_pos {t : ℝ}
    (hR : Summable (fun n => ‖cf n R * t^n‖))
    (hi : Summable (fun n => ‖cf n Ri * t^n‖)) (hip : 0 < poleValue Ri t) :
    0 < poleValue R t := by
  have h := (eq_div_iff hip.ne').mpr (poleValue_R_mul_Ri hR hi)
  rw [h]
  positivity

private theorem eq_of_sq_eq_pos {u v : ℝ} (hu : 0 < u) (hv : 0 < v)
    (h : u^2 = v^2) : u = v := by
  have hprod : (u-v)*(u+v) = 0 := by
    linear_combination h
  exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right (add_pos hu hv).ne')

theorem poleValue_R_at_a : poleValue R (16/27) = 11/9 := by
  have hR := absSummable_R (t := 16/27) (by norm_num) (by norm_num)
  have hi := absSummable_Ri (t := 16/27) (by norm_num) (by norm_num)
  have hip := poleValue_Ri_pos (t := 16/27) (by norm_num) (by norm_num) (by norm_num)
  apply eq_of_sq_eq_pos (poleValue_R_pos hR hi hip) (by norm_num)
  rw [poleValue_R_sq hR]
  norm_num

theorem poleValue_Ri_at_a : poleValue Ri (16/27) = 9/11 := by
  have hR := absSummable_R (t := 16/27) (by norm_num) (by norm_num)
  have hi := absSummable_Ri (t := 16/27) (by norm_num) (by norm_num)
  have h := poleValue_R_mul_Ri hR hi
  rw [poleValue_R_at_a] at h
  linarith

private theorem sqrt3_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)

private theorem sq_sqrt3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

theorem poleValue_R_at_b : poleValue R (4/9) = 2/Real.sqrt 3 := by
  have hR := absSummable_R (t := 4/9) (by norm_num) (by norm_num)
  have hi := absSummable_Ri (t := 4/9) (by norm_num) (by norm_num)
  have hip := poleValue_Ri_pos (t := 4/9) (by norm_num) (by norm_num) (by norm_num)
  apply eq_of_sq_eq_pos (poleValue_R_pos hR hi hip) (div_pos (by norm_num) sqrt3_pos)
  rw [poleValue_R_sq hR, div_pow (2:ℝ) (Real.sqrt 3), sq_sqrt3]
  norm_num

theorem poleValue_Ri_at_b : poleValue Ri (4/9) = Real.sqrt 3/2 := by
  have hR := absSummable_R (t := 4/9) (by norm_num) (by norm_num)
  have hi := absSummable_Ri (t := 4/9) (by norm_num) (by norm_num)
  have h := poleValue_R_mul_Ri hR hi
  rw [poleValue_R_at_b] at h
  apply mul_left_cancel₀ ((div_pos (by norm_num : (0:ℝ) < 2) sqrt3_pos).ne')
  rw [h]
  field_simp [sqrt3_pos.ne']

/-- The value of the numerator after cancelling the removable factor x. -/
theorem H_eval {P : S} {t y : ℝ} (hP : PowerSeries.constantCoeff ℝ P = 1)
    (ht : t ≠ 0) (hy : PoleHasSum P t y) :
    PoleHasSum (H P) t ((1-a*t^2-(1-b*t)*y)/(2*t)) := by
  have hM : PoleHasSum (poleB*P) t (y-b*(t*y)) := by
    unfold poleB
    rw [sub_mul, one_mul, mul_assoc]
    exact eval_sub hy (eval_C_mul (v := b) (eval_X_mul hy))
  have hh := eval_C_mul (v := 1/2)
    (eval_sub (eval_sub (eval_one t) (eval_C_mul (v := a) (eval_x_sq t))) hM)
  rw [← X_mul_H hP] at hh
  convert eval_X_cancel ht hh using 1
  ring

/-- The value of the derivative numerator. -/
theorem B_eval {P : S} {t y : ℝ} (hy : PoleHasSum P t y) :
    PoleHasSum (B P) t (t*(1+a*t^2)*y/2) := by
  have hxx := eval_X_mul (eval_X_mul hy)
  have hh := eval_C_mul (v := 1/2)
    (eval_X_mul (eval_add hy (eval_C_mul (v := a) hxx)))
  have heq : B P = c (1/2)*(x*(P+c a*(x*(x*P)))) := by
    change c (1/2)*x*(1+c a*x^2)*P = _
    ring
  rw [heq]
  convert hh using 1
  ring

theorem hasSum_H_at_a : PoleHasSum (H R) (16/27) (11/16) := by
  have hR := absSummable_R (t := 16/27) (by norm_num) (by norm_num)
  have hs := hR.of_norm.hasSum
  change PoleHasSum R (16/27) (poleValue R (16/27)) at hs
  rw [poleValue_R_at_a] at hs
  convert H_eval constantCoeff_R (by norm_num : (16/27 : ℝ) ≠ 0) hs using 1
  norm_num [a, b]

theorem hasSum_H_at_b : PoleHasSum (H R) (4/9) (3/4) := by
  have hR := absSummable_R (t := 4/9) (by norm_num) (by norm_num)
  have hs := hR.of_norm.hasSum
  change PoleHasSum R (4/9) (poleValue R (4/9)) at hs
  rw [poleValue_R_at_b] at hs
  convert H_eval constantCoeff_R (by norm_num : (4/9 : ℝ) ≠ 0) hs using 1
  norm_num [a, b]

theorem hasSum_B_at_a : PoleHasSum (B Ri) (16/27) (344/891) := by
  have hi := absSummable_Ri (t := 16/27) (by norm_num) (by norm_num)
  have hs := hi.of_norm.hasSum
  change PoleHasSum Ri (16/27) (poleValue Ri (16/27)) at hs
  rw [poleValue_Ri_at_a] at hs
  convert B_eval hs using 1
  norm_num [a]

theorem hasSum_B_at_b : PoleHasSum (B Ri) (4/9) (4*Real.sqrt 3/27) := by
  have hi := absSummable_Ri (t := 4/9) (by norm_num) (by norm_num)
  have hs := hi.of_norm.hasSum
  change PoleHasSum Ri (4/9) (poleValue Ri (4/9)) at hs
  rw [poleValue_Ri_at_b] at hs
  convert B_eval hs using 1
  norm_num [a]
  ring


end CatalanStrictPeaks.NearPoleSeries
