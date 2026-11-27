import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset Real

def expPrefix (L : ℕ) (u : ℝ) : ℝ := ∑ j ∈ range (L+1), u^j / j.factorial

theorem expPrefix_nonneg (L : ℕ) {u : ℝ} (hu : 0 ≤ u) : 0 ≤ expPrefix L u :=
  sum_nonneg fun j _ => by positivity

theorem expPrefix_half_bound (L : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    expPrefix L u ≤ (2:ℝ)^L * exp (u/2) := by
  apply le_trans _ (mul_le_mul_of_nonneg_left
    (Real.sum_le_exp_of_nonneg (show 0 ≤ u/2 by positivity) (L+1)) (by positivity))
  rw [mul_sum]
  apply sum_le_sum
  intro j hj
  have hjL : j ≤ L := by have := mem_range.mp hj; omega
  have h := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (show (1:ℝ)≤2 by norm_num) hjL)
    (show 0 ≤ (u/2)^j/(j.factorial:ℝ) by positivity)
  calc
    _ = (2:ℝ)^j*((u/2)^j/(j.factorial:ℝ)) := by
      rw [← mul_div_assoc, ← mul_pow, show 2*(u/2)=u by ring]
    _ ≤ _ := h

private theorem two_le_exp_seven_tenths : (2:ℝ) ≤ exp (7/10) := by
  refine le_trans ?_ (Real.sum_le_exp_of_nonneg (show (0:ℝ)≤7/10 by norm_num) 4)
  norm_num [sum_range_succ,Nat.factorial]

/-- Each positive frequency contributes to either a harmonic sum of length k
or an absolutely summable geometric tail, uniformly over all x ≥ 10. -/
theorem discrete_low_mode {L k a : ℕ} {R x : ℝ} (ha : 1 ≤ a) (hk : 1 ≤ k)
    (hL : L ≤ k) (hx : 10 ≤ x) (hR : 0 ≤ R)
    (hsmall : 16*(L:ℝ) ≤ x^2)
    (hdelta : R-x ≤ 5/x+x/(40*(k:ℝ))) (hratio : R ≤ (53/50)*x) :
    exp (-((a:ℝ)*x)) * expPrefix L ((a:ℝ)*R) / a ≤
      (if a ≤ k then 3/(a:ℝ) else 0) + (1/2:ℝ)^a := by
  have ha' : (1:ℝ) ≤ a := by exact_mod_cast ha
  have hapos : (0:ℝ) < a := by linarith
  have hk' : (0:ℝ) < k := by exact_mod_cast (show 0<k by omega)
  have hL' : (L:ℝ) ≤ k := by exact_mod_cast hL
  have hx' : 0 < x := by linarith
  have harg : 0 ≤ (a:ℝ)*R := mul_nonneg hapos.le hR
  by_cases near : (a:ℝ)*x ≤ 2*(L:ℝ)
  · have hak : a ≤ k := by
      exact_mod_cast (show (a:ℝ) ≤ k by nlinarith [mul_nonneg hapos.le (sub_nonneg.mpr hx)])
    rw [if_pos hak]
    have h1 : (a:ℝ)*(5/x) ≤ 5/8 := by
      rw [← mul_div_assoc, div_le_iff₀ hx']
      have hb : 8*(a:ℝ) ≤ x := by
        by_contra! h
        nlinarith only [near, hsmall, mul_pos (sub_pos.mpr h) hx']
      linarith
    have h2 : (a:ℝ)*(x/(40*(k:ℝ))) ≤ 1/20 := by
      rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
      linarith
    have hsum : (a:ℝ)*(R-x) ≤ 1 := by
      have hp := mul_le_mul_of_nonneg_left hdelta hapos.le
      rw [mul_add] at hp
      linarith
    have hb := mul_le_mul_of_nonneg_left (Real.sum_le_exp_of_nonneg harg (L+1)) (exp_pos (-((a:ℝ)*x))).le
    change exp _*expPrefix L _ ≤ _ at hb
    rw [← exp_add] at hb
    have h3 : -((a:ℝ)*x)+(a:ℝ)*R ≤ 1 := by linarith only [hsum]
    have hv := (hb.trans (exp_le_exp.mpr h3)).trans (Real.exp_one_lt_d9.le.trans (by norm_num : (2.7182818286:ℝ) ≤ 3))
    exact (div_le_div_of_nonneg_right hv hapos.le).trans (le_add_of_nonneg_right (by positivity))
  · have hpow : (2:ℝ)^L ≤ exp ((7/10)*(L:ℝ)) := by
      convert pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) two_le_exp_seven_tenths L using 1
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    have hbound := mul_le_mul_of_nonneg_left
      ((expPrefix_half_bound L harg).trans (mul_le_mul_of_nonneg_right hpow (exp_pos _).le))
      (exp_pos (-((a:ℝ)*x))).le
    rw [← exp_add, ← exp_add] at hbound
    have ht : -((a:ℝ)*x) + ((7/10)*(L:ℝ) + (a:ℝ)*R/2) ≤ -(a:ℝ) := by
      nlinarith [mul_le_mul_of_nonneg_left hratio hapos.le, mul_le_mul_of_nonneg_left hx hapos.le,
        lt_of_not_ge near]
    have he : exp (-(a:ℝ)) ≤ (1/2:ℝ)^a := by
      rw [show -(a:ℝ) = (a:ℝ)*(-1) by ring, exp_nat_mul]
      apply pow_le_pow_left₀ (exp_pos _).le
      rw [Real.exp_neg]
      rw [← one_div]
      exact one_div_le_one_div_of_le (by norm_num) (by linarith [Real.add_one_le_exp (1:ℝ)])
    have hv := (hbound.trans (exp_le_exp.mpr ht)).trans he
    have hd := div_le_self (mul_nonneg (exp_pos (-((a:ℝ)*x))).le (expPrefix_nonneg L harg)) ha'
    apply (hd.trans hv).trans
    exact le_add_of_nonneg_left (by split <;> positivity)

/-- Uniform absolute bound for all low powers, including the mode tail to infinity. -/
theorem discrete_low_frequency_sum {L k : ℕ} {R x : ℝ} (hk : 1 ≤ k)
    (hL : L ≤ k) (hx : 10 ≤ x) (hR : 0 ≤ R) (hsmall : 16*(L:ℝ) ≤ x^2)
    (hdelta : R-x ≤ 5/x+x/(40*(k:ℝ))) (hratio : R ≤ (53/50)*x) :
    (∑' i : ℕ, exp (-(((i+1:ℕ):ℝ)*x)) * expPrefix L (((i+1:ℕ):ℝ)*R) / (i+1:ℕ)) ≤
      3 * (∑ i ∈ range k, (1:ℝ)/(i+1:ℕ)) + 1 := by
  let a (i : ℕ) : ℝ := exp (-(((i+1:ℕ):ℝ)*x)) * expPrefix L (((i+1:ℕ):ℝ)*R) / (i+1:ℕ)
  let b (i : ℕ) : ℝ := if i < k then 3/(i+1:ℕ) else 0
  have hn (i) : 0 ≤ a i := div_nonneg (mul_nonneg (exp_pos _).le
    (expPrefix_nonneg _ (mul_nonneg (by positivity) hR))) (by positivity)
  have hm (i) : a i ≤ b i + (1/2:ℝ)^(i+1) := by
    simpa only [a,b,Nat.succ_le_iff] using
      discrete_low_mode (Nat.succ_pos i) hk hL hx hR hsmall hdelta hratio
  apply Real.tsum_le_of_sum_range_le hn
  intro N
  have bound := sum_le_sum (s := range N) (fun i _ => hm i)
  rw [sum_add_distrib] at bound
  apply bound.trans
  apply add_le_add
  · have he : (∑ i ∈ range N, b i) = ∑ i ∈ (range N).filter (· < k), (3:ℝ)/(i+1:ℕ) := by
      rw [sum_filter]
    rw [he,mul_sum]
    simp only [mul_one_div]
    apply sum_le_sum_of_subset_of_nonneg
    · intro i hi
      exact mem_range.mpr (mem_filter.mp hi).2
    · intros; positivity
  · have hh (M : ℕ) : (∑ i ∈ range M, (1/2:ℝ)^(i+1)) + (1/2:ℝ)^M = 1 := by
      induction M with
      | zero => norm_num
      | succ M ih =>
        rw [sum_range_succ, pow_succ (1/2:ℝ) M]
        linarith
    linarith [hh N, show 0 ≤ (1/2:ℝ)^N by positivity]

#print axioms discrete_low_frequency_sum
#print axioms expPrefix_half_bound
#print axioms discrete_low_mode
end OpenMathResearch.LongCycleExcedances
