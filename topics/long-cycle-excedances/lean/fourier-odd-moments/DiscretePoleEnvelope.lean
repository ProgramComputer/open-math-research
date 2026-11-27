import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances

open scoped BigOperators Real

/-- The rational comparison weight for a pole of height p. -/
def discretePoleWeight (B p : ℝ) : ℝ := B^2/(B+p^2)^2

def discretePoleHeight (i : ℕ) : ℝ := 2*(i:ℝ)+3

private theorem telescoping_prefix (f : ℕ → ℝ) (N : ℕ) :
    (∑ i ∈ Finset.range N, (f i - f (i+1))) = f 0 - f N := by
  induction N with
  | zero => simp
  | succ n hn =>
    rw [Finset.sum_range_succ,hn]
    ring

/-- Natural Bernoulli at a quarter of the cutoff gives the square-decay
comparison. The hypothesis on a² is the literal normalized pole norm. -/
theorem discrete_pole_decay {k : ℕ} (hk : 100 ≤ k) {x S p a : ℝ}
    (hx : 44 ≤ x) (hsize : 1 ≤ x*(k:ℝ)*S^2) (hp : 3 ≤ p)
    (ha : 0 ≤ a) (haq : a^2 = (1+(p^2-1)*S^2)⁻¹) :
    a^(k-1) ≤ discretePoleWeight (5*x) p := by
  let m := (k-1)/4
  let d := (p^2-1)*S^2
  let B := 5*x
  have hx0 : 0 < x := by linarith
  have hB : 0 < B := by dsimp [B]; positivity
  have hp0 : 0 ≤ p := by linarith
  have hd : 0 ≤ d := mul_nonneg (by nlinarith only [hp,sq_nonneg (p-3)]) (sq_nonneg S)
  have hq : 0 < 1+d := by positivity
  have hmexp : 4*m ≤ k-1 := by dsimp only [m]; omega
  have hm : (6/25:ℝ)*(k:ℝ) ≤ (m:ℝ) := by
    have hi : 6*k ≤ 25*m := by dsimp only [m]; omega
    have hir : (6:ℝ)*(k:ℝ) ≤ 25*(m:ℝ) := by exact_mod_cast hi
    linarith only [hir]
  have hgap : (8/9:ℝ)*p^2 ≤ p^2-1 := by nlinarith only [hp,sq_nonneg (p-3)]
  have hks : 1/x ≤ (k:ℝ)*S^2 := by
    apply (div_le_iff₀ hx0).2
    nlinarith only [hsize]
  have hmd : p^2/B ≤ (m:ℝ)*d := by
    have hmul := mul_le_mul hm hgap (by positivity) (Nat.cast_nonneg m)
    have hscaled := mul_le_mul_of_nonneg_right hmul (sq_nonneg S)
    have hgrowth := mul_le_mul_of_nonneg_left hks (show 0 ≤ (16/75:ℝ)*p^2 by positivity)
    have hsmall : p^2/B ≤ (16/75:ℝ)*p^2*(1/x) := by
      dsimp only [B]
      have hq0 : 0 < 5*x := by positivity
      apply (div_le_iff₀ hq0).2
      have heq : (16/75:ℝ)*p^2*(1/x)*(5*x) = (16/15:ℝ)*p^2 := by
        field_simp [hx0.ne']
        ring
      rw [heq]
      nlinarith only [sq_nonneg p]
    refine hsmall.trans (hgrowth.trans ?_)
    dsimp only [d]
    nlinarith only [hscaled]
  have hpowbound : 1+p^2/B ≤ (1+d)^m := by
    have hBern := one_add_mul_le_pow (show -2 ≤ d by linarith) m
    exact (show 1+p^2/B ≤ 1+(m:ℝ)*d by linarith only [hmd]).trans hBern
  have haone : a ≤ 1 := by
    have hs : a^2 ≤ 1 := by
      rw [haq]
      exact (inv_le_one₀ hq).2 (by linarith)
    nlinarith only [ha,hs,sq_nonneg (a-1)]
  have hinv : ((1+d)^m)⁻¹ ≤ (1+p^2/B)⁻¹ :=
    inv_anti₀ (by positivity) hpowbound
  calc
    a^(k-1) ≤ a^(4*m) := pow_le_pow_of_le_one ha haone hmexp
    _ = ((a^2)^m)^2 := by
      rw [← pow_mul, ← pow_mul, show 4*m=2*(m*2) by omega]
    _ = (((1+d)^m)⁻¹)^2 := by rw [haq,inv_pow]
    _ ≤ ((1+p^2/B)⁻¹)^2 := pow_le_pow_left₀ (by positivity) hinv 2
    _ = discretePoleWeight B p := by
      have hden : 0 < B+p^2 := by positivity
      unfold discretePoleWeight
      have heq : (1+p^2/B)⁻¹ = B/(B+p^2) := by
        rw [show (1+p^2/B) = (B+p^2)/B by rw [add_div, div_self hB.ne'], inv_div]
      rw [heq,div_pow]

private def momentPrimitive (B p : ℝ) : ℝ := B^2/(B+p^2)

private theorem weighted_step {B p : ℝ} (hB : 0 < B) (hp : 3 ≤ p) :
    (8/3)*p*discretePoleWeight B p ≤
      momentPrimitive B (p-2)-momentPrimitive B p := by
  have hp0 : 0 ≤ p := by linarith
  have h0 : 0 < B+(p-2)^2 := by positivity
  have h1 : 0 < B+p^2 := by positivity
  have hsq : (p-2)^2 ≤ p^2 := by nlinarith only [hp]
  have hcommon :
      momentPrimitive B (p-2)-momentPrimitive B p =
        (4*(p-1)*B^2)/((B+(p-2)^2)*(B+p^2)) := by
    unfold momentPrimitive
    field_simp [h0.ne',h1.ne']
    ring
  rw [hcommon]
  calc
    _ ≤ 4*(p-1)*discretePoleWeight B p := by
      apply mul_le_mul_of_nonneg_right (by linarith)
      unfold discretePoleWeight
      positivity
    _ = (4*(p-1)*B^2)/(B+p^2)^2 := by unfold discretePoleWeight; ring
    _ ≤ _ := by
      have hp1 : 0 ≤ p - 1 := by linarith
      apply div_le_div_of_nonneg_left (by positivity) (mul_pos h0 h1)
      rw [pow_two (B+p^2)]
      exact mul_le_mul_of_nonneg_right (by linarith only [hsq]) h1.le

/-- First moment on the positive nonprincipal half of the lattice. -/
theorem discrete_pole_weighted_prefix {B : ℝ} (hB : 0 < B) (N : ℕ) :
    (∑ i ∈ Finset.range N, discretePoleHeight i * discretePoleWeight B (discretePoleHeight i)) ≤
      (3/8)*B := by
  let H : ℕ → ℝ := fun i => momentPrimitive B (2*(i:ℝ)+1)
  have hstep (i : ℕ) : discretePoleHeight i * discretePoleWeight B (discretePoleHeight i) ≤
      (3/8)*(H i - H (i+1)) := by
    have h := weighted_step (p:=discretePoleHeight i) hB (by unfold discretePoleHeight; linarith [Nat.cast_nonneg (α:=ℝ) i])
    have he : discretePoleHeight i-2 = 2*(i:ℝ)+1 := by unfold discretePoleHeight; ring
    have he' : discretePoleHeight i = 2*(((i+1:ℕ):ℝ))+1 := by unfold discretePoleHeight; push_cast; ring
    rw [he,he'] at h
    change (8/3)*(2*(((i+1:ℕ):ℝ))+1)*discretePoleWeight B (2*(((i+1:ℕ):ℝ))+1) ≤ H i-H (i+1) at h
    rw [← he'] at h
    linarith only [h]
  have hH0 : H 0 ≤ B := by
    change B^2/(B+(2*((0:ℕ):ℝ)+1)^2) ≤ B
    apply (div_le_iff₀ (by positivity)).2
    norm_num
    nlinarith only [hB]
  have hHN : 0 ≤ H N := by unfold H momentPrimitive; positivity
  calc
    _ ≤ ∑ i ∈ Finset.range N, (3/8)*(H i-H (i+1)) :=
      Finset.sum_le_sum (fun i _ => hstep i)
    _ = (3/8)*(H 0-H N) := by rw [← Finset.mul_sum, telescoping_prefix]
    _ ≤ _ := by linarith only [hH0,hHN]

private theorem zeroth_step {L p : ℝ} (hL : 0 < L) (hp : 3 ≤ p) :
    2*discretePoleWeight (3*L^2) p ≤
      (9/4)*L^2*((L+p-2)⁻¹-(L+p)⁻¹) := by
  have hp0 : 0 ≤ p := by linarith
  have hsum : 0 < L+p := by positivity
  have hprev : 0 < L+p-2 := by linarith
  have hbase : 0 < 3*L^2+p^2 := by positivity
  have hcmp : 3*L^2/(3*L^2+p^2) ≤ 3*L/(2*(L+p)) := by
    apply (div_le_div_iff₀ hbase (by positivity)).2
    nlinarith only [mul_nonneg hL.le (sq_nonneg (p-L))]
  have hsq := pow_le_pow_left₀ (by positivity) hcmp 2
  have hrew : (3*L/(2*(L+p)))^2 = (9/4)*L^2/(L+p)^2 := by
    field_simp [hsum.ne']
    ring
  have hstep : 2/(L+p)^2 ≤ (L+p-2)⁻¹-(L+p)⁻¹ := by
    have he : (L+p-2)⁻¹-(L+p)⁻¹ = 2/((L+p-2)*(L+p)) := by
      field_simp [hprev.ne',hsum.ne']
    rw [he]
    apply div_le_div_of_nonneg_left (by norm_num) (mul_pos hprev hsum)
    rw [pow_two]
    exact mul_le_mul_of_nonneg_right (by linarith) hsum.le
  rw [hrew,div_pow,← discretePoleWeight] at hsq
  calc
    _ ≤ 2*((9/4)*L^2/(L+p)^2) := by linarith only [hsq]
    _ = (9/4)*L^2*(2/(L+p)^2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hstep (by positivity)

/-- Zeroth moment on both nonprincipal halves of the lattice. -/
theorem discrete_pole_unweighted_prefix {L : ℝ} (hL : 0 < L) (N : ℕ) :
    2*(∑ i ∈ Finset.range N, discretePoleWeight (3*L^2) (discretePoleHeight i)) ≤
      (9/4)*L^2/(L+1) := by
  let H : ℕ → ℝ := fun i => (L+2*(i:ℝ)+1)⁻¹
  have hstep (i : ℕ) : 2*discretePoleWeight (3*L^2) (discretePoleHeight i) ≤
      (9/4)*L^2*(H i-H (i+1)) := by
    have h := zeroth_step (p:=discretePoleHeight i) hL (by unfold discretePoleHeight; linarith [Nat.cast_nonneg (α:=ℝ) i])
    have hprev : L+discretePoleHeight i-2 = L+2*(i:ℝ)+1 := by unfold discretePoleHeight; ring
    have hnext : L+discretePoleHeight i = L+2*(((i+1:ℕ):ℝ))+1 := by unfold discretePoleHeight; push_cast; ring
    rw [hprev,hnext] at h
    exact h
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ i ∈ Finset.range N, (9/4)*L^2*(H i-H (i+1)) :=
      Finset.sum_le_sum (fun i _ => hstep i)
    _ = (9/4)*L^2*(H 0-H N) := by rw [← Finset.mul_sum,telescoping_prefix]
    _ ≤ (9/4)*L^2*H 0 := by
      have hHN : 0 ≤ H N := by unfold H; positivity
      exact mul_le_mul_of_nonneg_left (by linarith only [hHN]) (by positivity)
    _ = (9/4)*L^2/(L+1) := by simp [H,div_eq_mul_inv]

#print axioms discrete_pole_decay
#print axioms discrete_pole_weighted_prefix
#print axioms discrete_pole_unweighted_prefix
end OpenMathResearch.LongCycleExcedances
