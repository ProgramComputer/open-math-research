import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset

/-- Pair the signed odd denominators labeled by t and -(t+1). -/
def reflectedLogWeight (h : ℝ) (t : ℕ) : ℝ :=
  (1/(t:ℝ)+1/((t:ℝ)+1))/(1+h*t*((t:ℝ)+1))^96

def reflectedLogTailScale (h : ℝ) (L : ℕ) : ℝ :=
  1/(h*(1+h*L*((L:ℝ)+1))^95)

private theorem tail_fraction_identity {x h b : ℝ} (hx : 0 < x) (hh : 0 < h) (hb : 0 < b) :
    (1/x+1/(x+1))/(b*(h*x*(x+1))) =
      (1/(h*b))*(1/x^2-1/(x+1)^2) := by
  field_simp [hh.ne',hx.ne',hb.ne',show x+1 ≠ 0 by positivity]
  ring

theorem reflected_log_weight_step {h : ℝ} (hh : 0 < h) {L t : ℕ} (hL : 0 < L)
    (hLt : L ≤ t) :
    reflectedLogWeight h t ≤ reflectedLogTailScale h L *
      (1/(t:ℝ)^2-1/((t:ℝ)+1)^2) := by
  let B (u : ℕ) : ℝ := 1+h*u*((u:ℝ)+1)
  have ht : (0:ℝ) < t := by exact_mod_cast (lt_of_lt_of_le hL hLt)
  have hLt' : (L:ℝ) ≤ t := by exact_mod_cast hLt
  have hB (u : ℕ) : 0 < B u := by dsimp [B]; positivity
  have hmono : B L ≤ B t := by
    apply add_le_add le_rfl
    exact mul_le_mul (mul_le_mul_of_nonneg_left hLt' hh.le) (by linarith)
      (by positivity) (by positivity)
  have hden : B L^95*(h*t*((t:ℝ)+1)) ≤ B t^96 := by
    rw [pow_succ (B t) 95]
    exact mul_le_mul (pow_le_pow_left₀ (hB L).le hmono 95)
      (by dsimp [B]; linarith) (by positivity) (by positivity)
  have hlhs : 0 < B L^95*(h*t*((t:ℝ)+1)) := by positivity
  calc
    _ ≤ (1/(t:ℝ)+1/((t:ℝ)+1))/(B L^95*(h*t*((t:ℝ)+1))) :=
      div_le_div_of_nonneg_left (by positivity) hlhs hden
    _ = _ := by
      change _ = 1/(h*(B L)^95)*(1/(t:ℝ)^2-1/((t:ℝ)+1)^2)
      exact tail_fraction_identity ht hh (pow_pos (hB L) 95)

theorem reflected_log_partial_tail {h : ℝ} (hh : 0 < h) {L : ℕ} (hL : 0 < L) (N : ℕ) :
    ∑ i ∈ range N, reflectedLogWeight h (L+i) ≤
      reflectedLogTailScale h L*(1/(L:ℝ)^2-1/((L+N:ℕ):ℝ)^2) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ]
    have hr := add_le_add ih (reflected_log_weight_step hh hL (Nat.le_add_right L N))
    apply hr.trans_eq
    push_cast
    ring

theorem reflected_log_tail {h : ℝ} (hh : 0 < h) {L : ℕ} (hL : 0 < L) :
    Summable (fun i => reflectedLogWeight h (L+i)) ∧
      (∑' i, reflectedLogWeight h (L+i)) ≤ reflectedLogTailScale h L/(L:ℝ)^2 := by
  have hnn (i : ℕ) : 0 ≤ reflectedLogWeight h (L+i) := by
    unfold reflectedLogWeight
    positivity
  have hs (N : ℕ) : ∑ i ∈ range N, reflectedLogWeight h (L+i) ≤
      reflectedLogTailScale h L/(L:ℝ)^2 := by
    apply (reflected_log_partial_tail hh hL N).trans
    rw [div_eq_mul_inv (reflectedLogTailScale h L)]
    apply mul_le_mul_of_nonneg_left
    · simp only [one_div]; exact sub_le_self _ (inv_nonneg.mpr (sq_nonneg ((L+N:ℕ):ℝ)))
    · unfold reflectedLogTailScale; positivity
  exact ⟨summable_of_sum_range_le hnn hs, Real.tsum_le_of_sum_range_le hnn hs⟩

theorem reflected_log_all {h : ℝ} (hh : 0 < h) (N : ℕ) :
    Summable (fun i => reflectedLogWeight h (i+1)) ∧
      (∑' i, reflectedLogWeight h (i+1)) ≤
        (∑ i ∈ range N, reflectedLogWeight h (i+1)) +
          reflectedLogTailScale h (N+1)/((N+1:ℕ):ℝ)^2 := by
  have htail := reflected_log_tail hh (Nat.zero_lt_succ N)
  have hs : Summable (fun i => reflectedLogWeight h (i+1)) := by
    rw [← summable_nat_add_iff N]
    simpa only [Nat.succ_eq_add_one,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using htail.1
  refine ⟨hs,?_⟩
  rw [←hs.sum_add_tsum_nat_add N]
  apply add_le_add le_rfl
  simpa only [Nat.succ_eq_add_one,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using htail.2

#print axioms reflected_log_all
end OpenMathResearch.LongCycleExcedances
