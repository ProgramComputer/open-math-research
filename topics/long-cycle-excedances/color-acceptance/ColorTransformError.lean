import ColorAcceptanceSeries
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset PowerSeries
open scoped Polynomial

theorem bar_choices_le_words (m r : ℕ) : (m+r).choose m ≤ (m+1)^r := by
  induction r with
  | zero => simp
  | succ r ih =>
    have he := Nat.choose_mul_succ_eq (m+r) m
    rw [show m+r+1-m=r+1 by omega] at he
    apply Nat.le_of_mul_le_mul_right _ (Nat.succ_pos r)
    calc
      _ = (m+r).choose m*(m+r+1) := he.symm
      _ ≤ (m+1)^r*((m+1)*(r+1)) := Nat.mul_le_mul ih (by nlinarith [Nat.zero_le (m*r)])
      _ = _ := by rw [pow_succ]; simp only [Nat.succ_eq_add_one]; ring

/-- Coefficients of the positive binomial transform, grouped by extra bars. -/
theorem color_extra_bars (P : ℝ[X]) {n : ℕ} (hn : 0 < n) (p : ℕ) :
    coeff (R := ℝ) p (colorTransform n P) - P.coeff p =
      ∑ j ∈ range p, P.coeff (p-(j+1))*(((n-1+(j+1)).choose (n-1)):ℝ) := by
  let f (s : ℕ) := P.coeff s * (((n-1+(p-s)).choose (n-1)):ℝ)
  rw [colorTransform_coeff P hn]
  change (∑ s ∈ range (p+1), f s)-P.coeff p=_
  rw [←sum_range_reflect f (p+1),sum_range_succ']
  simp only [Nat.add_sub_cancel,Nat.sub_zero]
  have hp : f p = P.coeff p := by simp [f]
  rw [hp,add_sub_cancel_right]
  apply sum_congr rfl
  intro j hj
  have hjp : j+1 ≤ p := mem_range.mp hj
  simp only [f,Nat.sub_sub_self hjp]

private theorem power_rank_decay {p r : ℕ} (hp : 0 < p) (hr : r ≤ p) :
    ((p-r:ℕ):ℝ)/(p:ℝ) ≤ (1-1/(p:ℝ))^r := by
  have hp' : (1:ℝ) ≤ p := by exact_mod_cast hp
  have hi : 1/(p:ℝ) ≤ 1 := (div_le_one (by positivity)).2 hp'
  have h := one_add_mul_le_pow (show (-2:ℝ) ≤ -(1/(p:ℝ)) by linarith) r
  rw [Nat.cast_sub hr,sub_div,div_self (by positivity : (p:ℝ) ≠ 0)]
  simpa only [← sub_eq_add_neg,mul_neg,mul_one_div] using h

/-- A rational error bound for the normalized coefficient obtained by
retaining only the unbarred term of the positive transform. -/
theorem color_transform_error (P : ℝ[X]) {n p : ℕ} (hn : 0 < n) (hp : 0 < p)
    (hP : ∀ i, 0 ≤ P.coeff i ∧ P.coeff i ≤ (i:ℝ)^n) :
    let η := (n:ℝ)*(1-1/(p:ℝ))^n
    0 ≤ (coeff (R := ℝ) p (colorTransform n P) - P.coeff p)/(p:ℝ)^n ∧
    (coeff (R := ℝ) p (colorTransform n P) - P.coeff p)/(p:ℝ)^n ≤
      ∑ j ∈ range p, η^(j+1) := by
  dsimp only
  rw [color_extra_bars P hn,Finset.sum_div]
  have hpn : 0 < (p:ℝ)^n := by positivity
  constructor
  · exact sum_nonneg fun j _ => div_nonneg (mul_nonneg (hP _).1 (by positivity)) hpn.le
  · apply sum_le_sum
    intro j hj
    let r := j+1
    have hr : r ≤ p := mem_range.mp hj
    have hB : (((n-1+r).choose (n-1)):ℝ) ≤ (n:ℝ)^r := by
      have hB := bar_choices_le_words (n-1) r
      rw [Nat.sub_add_cancel hn] at hB
      exact_mod_cast hB
    have hpow := pow_le_pow_left₀ (by positivity) (power_rank_decay hp hr) n
    rw [div_pow] at hpow
    have hv := div_le_div_of_nonneg_right (hP (p-r)).2 hpn.le
    have hc := mul_le_mul (hv.trans hpow) hB (by positivity)
      (pow_nonneg (pow_nonneg (sub_nonneg.mpr ((div_le_one (by positivity : (0:ℝ)<p)).2
        (by exact_mod_cast hp))) r) n)
    change P.coeff (p-r)*(((n-1+r).choose (n-1)):ℝ)/(p:ℝ)^n ≤ ((n:ℝ)*(1-1/(p:ℝ))^n)^r
    rw [mul_div_right_comm, mul_pow, mul_comm ((n:ℝ)^r),
      pow_right_comm (1-1/(p:ℝ)) n r]
    exact hc

/-- If the normalized color count is a probability, the approximation has
a rational bound at every rank, including when the geometric ratio exceeds one. -/
theorem color_transform_error_twice (P : ℝ[X]) {n p : ℕ} (hn : 0 < n) (hp : 0 < p)
    (hP : ∀ i, 0 ≤ P.coeff i ∧ P.coeff i ≤ (i:ℝ)^n)
    (hcount : coeff (R := ℝ) p (colorTransform n P) ≤ (p:ℝ)^n) :
    (coeff (R := ℝ) p (colorTransform n P)-P.coeff p)/(p:ℝ)^n ≤
      2*((n:ℝ)*(1-1/(p:ℝ))^n) := by
  let η := (n:ℝ)*(1-1/(p:ℝ))^n
  have hx : 0 ≤ 1-1/(p:ℝ) := sub_nonneg.mpr ((div_le_one (by positivity)).2
    (by exact_mod_cast hp))
  have he : 0 ≤ η := mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx _)
  change _ ≤ 2*η
  by_cases hhalf : η < 1/2
  · apply (color_transform_error P hn hp hP).2.trans
    change (∑ j ∈ range p, η^(j+1)) ≤ 2*η
    simp_rw [pow_succ]
    rw [←sum_mul]
    apply mul_le_mul_of_nonneg_right _ he
    have hgeom := geom_sum_mul_neg η p
    have hsum : 0 ≤ ∑ j ∈ range p, η^j := sum_nonneg fun _ _ => pow_nonneg he _
    have ht : (∑ j ∈ range p, η^j)*(1/2) ≤ (∑ j ∈ range p, η^j)*(1-η) :=
      mul_le_mul_of_nonneg_left (by linarith) hsum
    linarith [pow_nonneg he p]
  · have hc : (coeff (R := ℝ) p (colorTransform n P)-P.coeff p)/(p:ℝ)^n ≤ 1 := by
      apply (div_le_one (by positivity)).2
      linarith [(hP p).1]
    exact hc.trans (by linarith)

#print axioms color_transform_error_twice
#print axioms bar_choices_le_words
#print axioms color_extra_bars
#print axioms color_transform_error
end OpenMathResearch.LongCycleExcedances
