import CatalanStrictPeaksPoleRadical
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Absolute convergence at the two Catalan poles

The inverse square root has a two-step recurrence. Its coefficients from
degree one are bounded by a geometric sequence with ratio 5/4 and leading
factor 1/4. This gives convergence of both radicals at the poles and proves
that the inverse radical takes the positive real branch there.
-/

namespace CatalanStrictPeaks.NearPoleSeries

open PowerSeries
open scoped BigOperators

private lemma recurrence_bound {c : ℕ → ℝ}
    (c0 : c 0 = 1) (c1 : c 1 = -1/4)
    (rec : ∀ n : ℕ, c (n+2) = -(((2*(n:ℝ)+3)/2)*c (n+1) +
      ((2*(n:ℝ)+2)*(9/16))*c n)/(2*((n:ℝ)+2))) :
    ∀ n : ℕ, |c (n+1)| ≤ (1/4 : ℝ)*(5/4)^n := by
  have hs (n : ℕ) : |c (n+2)| ≤ (1/2 : ℝ)*|c (n+1)| + (9/16 : ℝ)*|c n| := by
    rw [rec, abs_div, abs_neg, abs_of_pos (show (0:ℝ)<2*((n:ℝ)+2) by positivity)]
    apply (div_le_iff₀ (by positivity)).mpr
    calc
      _ ≤ |((2*(n:ℝ)+3)/2)*c (n+1)| + |((2*(n:ℝ)+2)*(9/16))*c n| := abs_add_le _ _
      _ ≤ _ := by
        rw [abs_mul, abs_mul, abs_of_nonneg (show (0:ℝ)≤(2*(n:ℝ)+3)/2 by positivity),
          abs_of_nonneg (show (0:ℝ)≤(2*(n:ℝ)+2)*(9/16) by positivity)]
        nlinarith only [abs_nonneg (c n), abs_nonneg (c (n+1))]
  intro n
  induction n using Nat.twoStepInduction with
  | zero => norm_num [c1, abs_div]
  | one => norm_num [rec 0, c0, c1, abs_div]
  | more n h0 h1 =>
    have step := hs (n+1)
    calc
      _ ≤ (1/2 : ℝ)*|c (n+1+1)| + (9/16 : ℝ)*|c (n+1)| := step
      _ ≤ (1/2 : ℝ)*((1/4)*(5/4)^(n+1))+(9/16)*((1/4)*(5/4)^n) := by gcongr
      _ ≤ _ := by rw [pow_succ (5/4:ℝ) (n+1), pow_succ (5/4:ℝ) n]; nlinarith [pow_pos (by norm_num : (0:ℝ)<5/4) n]

/-- The convergent coefficient evaluation used at the two positive poles. -/
noncomputable def poleValue (f : PowerSeries ℝ) (t : ℝ) : ℝ := ∑' n, coeff ℝ n f * t^n

lemma absolute_from_geometric {f : PowerSeries ℝ} {A t : ℝ}
    (hf : ∀ n, |coeff ℝ n f| ≤ A*(5/4:ℝ)^n) (ht : 0 ≤ t) (hT : (5/4:ℝ)*t < 1) :
    Summable (fun n => |coeff ℝ n f| *t^n) ∧
      ∑' n, |coeff ℝ n f| *t^n ≤ A/(1-(5/4)*t) := by
  have hnon : 0 ≤ (5/4 : ℝ)*t := by positivity
  have hg := (summable_geometric_of_lt_one hnon hT).mul_left A
  have bound (n : ℕ) : |coeff ℝ n f| *t^n ≤ A*((5/4)*t)^n := by
    rw [mul_pow, ← mul_assoc]; gcongr; exact hf n
  have hh := Summable.of_nonneg_of_le (fun n => mul_nonneg (abs_nonneg _) (pow_nonneg ht n)) bound hg
  refine ⟨hh, (hh.tsum_le_tsum bound hg).trans_eq ?_⟩
  rw [tsum_mul_left, tsum_geometric_of_lt_one hnon hT]
  rfl

private lemma positive_value {f : PowerSeries ℝ} {t : ℝ}
    (h0 : coeff ℝ 0 f = 1)
    (hsmall : ∀ n : ℕ, |coeff ℝ (n+1) f| ≤ (1/4:ℝ)*(5/4)^n)
    (ht : 0 ≤ t) (hT : (5/4:ℝ)*t < 1) (hgap : (t/4)/(1-5/4*t) < 1) :
    0 < poleValue f t := by
  have hnon : 0 ≤ (5/4:ℝ)*t := by positivity
  have hg := (summable_geometric_of_lt_one hnon hT).mul_left (t/4)
  have bound (n : ℕ) : ‖coeff ℝ (n+1) f * t^(n+1)‖ ≤ (t/4)*((5/4)*t)^n := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg ht _), pow_succ, mul_pow]
    calc
      _ ≤ ((1/4:ℝ)*(5/4)^n)*(t^n*t) := by gcongr; exact hsmall n
      _ = _ := by ring
  have hnorm := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) bound hg
  have htail := hnorm.of_norm
  have hbound := (norm_tsum_le_tsum_norm hnorm).trans (hnorm.tsum_le_tsum bound hg)
  rw [tsum_mul_left, tsum_geometric_of_lt_one hnon hT, ← div_eq_mul_inv, Real.norm_eq_abs] at hbound
  have hsum : Summable (fun n => coeff ℝ n f * t^n) := (summable_nat_add_iff 1).mp htail
  rw [poleValue, hsum.tsum_eq_zero_add, h0, pow_zero, mul_one]
  linarith [(abs_lt.mp (hbound.trans_lt hgap)).1]

lemma value_mul {f g : PowerSeries ℝ} {t : ℝ}
    (hf : Summable (fun n => ‖coeff ℝ n f * t^n‖))
    (hg : Summable (fun n => ‖coeff ℝ n g * t^n‖)) :
    poleValue (f*g) t = poleValue f t * poleValue g t := by
  unfold poleValue
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf hg]
  apply tsum_congr
  intro n
  rw [coeff_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  have he := Finset.mem_antidiagonal.mp hij
  rw [← he, pow_add]
  ring

lemma coeff_Ri_tail (n : ℕ) :
    |coeff ℝ (n+1) Ri| ≤ (1/4 : ℝ)*(5/4)^n := by
  simpa only [coeff_Ri] using
    recurrence_bound invRootCoeff_zero invRootCoeff_one invRootCoeff_succ_succ n

private lemma coeff_Ri_unit (n : ℕ) :
    |coeff ℝ n Ri| ≤ (5/4:ℝ)^n := by
  cases n with
  | zero => norm_num
  | succ n =>
    have h := coeff_Ri_tail n
    rw [pow_succ]
    nlinarith [pow_pos (by norm_num : (0:ℝ)<5/4) n]

lemma coeff_Ri_bound (n : ℕ) :
    |coeff ℝ n Ri| ≤ 3*(5/4:ℝ)^n := by
  linarith [coeff_Ri_unit n, pow_pos (by norm_num : (0:ℝ)<5/4) n]

private lemma coeff_R_expansion (n : ℕ) :
    coeff ℝ n R = coeff ℝ n Ri +
      (1/2 : ℝ)*(if 1 ≤ n then coeff ℝ (n-1) Ri else 0) +
      (9/16 : ℝ)*(if 2 ≤ n then coeff ℝ (n-2) Ri else 0) := by
  have he : R = Ri + PowerSeries.C ℝ (1/2)*(X^1*Ri) + PowerSeries.C ℝ (9/16)*(X^2*Ri) := by
    unfold R Q
    ring
  rw [he]
  simp only [map_add, coeff_C_mul, coeff_X_pow_mul']

lemma coeff_R_bound (n : ℕ) :
    |coeff ℝ n R| ≤ 2*(5/4:ℝ)^n := by
  rw [coeff_R_expansion]
  obtain _ | _ | n := n
  · norm_num
  · norm_num [abs_div]
  · simp only [if_pos (show 1 ≤ n.succ.succ by omega),
      if_pos (show 2 ≤ n.succ.succ by omega), Nat.succ_sub_one,
      show n.succ.succ-2=n by omega]
    calc
      _ ≤ |coeff ℝ (n+2) Ri| + |(1/2:ℝ)*coeff ℝ (n+1) Ri| +
        |(9/16:ℝ)*coeff ℝ n Ri| :=
          (abs_add_le _ _).trans (add_le_add_right (abs_add_le _ _) _)
      _ ≤ (5/4:ℝ)^(n+2) + (1/2)*(5/4)^(n+1) + (9/16)*(5/4)^n := by
        rw [abs_mul, abs_mul]
        rw [abs_of_pos (by norm_num : (0 : ℝ) < 1/2), abs_of_pos (by norm_num : (0 : ℝ) < 9/16)]
        gcongr <;> apply coeff_Ri_unit
      _ ≤ _ := by
        change _ ≤ 2*(5/4:ℝ)^(n+2)
        rw [pow_succ (5/4:ℝ) (n+1), pow_succ (5/4:ℝ) n]
        nlinarith [pow_pos (by norm_num : (0:ℝ)<5/4) n]

private lemma absSummable_at {f : PowerSeries ℝ} {A t : ℝ}
    (hf : ∀ n, |coeff ℝ n f| ≤ A*(5/4:ℝ)^n) (ht : 0 ≤ t) (hT : (5/4:ℝ)*t < 1) :
    Summable (fun n => ‖coeff ℝ n f * t^n‖) := by
  simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg ht _)] using
    (absolute_from_geometric hf ht hT).1

lemma absSummable_R {t : ℝ} (ht : 0 ≤ t) (hT : (5/4:ℝ)*t < 1) :
    Summable (fun n => ‖coeff ℝ n R * t^n‖) := absSummable_at coeff_R_bound ht hT

lemma absSummable_Ri {t : ℝ} (ht : 0 ≤ t) (hT : (5/4:ℝ)*t < 1) :
    Summable (fun n => ‖coeff ℝ n Ri * t^n‖) := absSummable_at coeff_Ri_bound ht hT

lemma poleValue_Ri_pos {t : ℝ} (ht : 0 ≤ t) (hT : (5/4:ℝ)*t < 1)
    (hgap : (t/4)/(1-5/4*t)<1) : 0 < poleValue Ri t :=
  positive_value (by simp) coeff_Ri_tail ht hT hgap

end CatalanStrictPeaks.NearPoleSeries
