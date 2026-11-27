import FourierResolventDerivative
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset Set Metric

/-- Removing one more Taylor coefficient gains one power of w/p, including
at w=0. -/
theorem next_pole_remainder (d : ℕ) {p w : ℂ} (hp : p ≠ 0) (hw : p-w ≠ 0) :
    w^(d+1)/(p^(d+1)*(p-w)) = w^d/(p^d*(p-w)) - w^d/p^(d+1) := by
  rw [pow_succ,pow_succ]
  field_simp [hp,hw,pow_ne_zero d hp]
  ring

theorem pole_remainder_summable {ι : Type*} (P : ι → ℂ) (d : ℕ) (hp : ∀ i, P i ≠ 0)
    (hs : Summable (fun i => 1/‖P i‖^(d+1))) {U : Set ℂ} (hU : IsOpen U)
    (havoid : ∀ i, P i ∉ U) {w : ℂ} (hw : w ∈ U) :
    Summable (fun i => w^d/(P i^d*(P i-w))) := by
  obtain ⟨δ,M,hd,hM,_,hbound⟩ := local_pole_ratio P hU havoid hw
  apply (hs.mul_left (‖w‖^d*M)).of_norm_bounded
  intro i
  have hsep : P i-w ≠ 0 := sub_ne_zero.mpr (fun e => havoid i (e ▸ hw))
  have hnorm := norm_pos_iff.mpr (hp i)
  rw [norm_div,norm_mul,norm_pow,norm_pow,←mul_div_assoc,mul_one,
    div_le_div_iff₀ (mul_pos (pow_pos hnorm _) (norm_pos_iff.mpr hsep)) (pow_pos hnorm _)]
  calc
    _ = (‖w‖^d*‖P i‖^d)*‖P i‖ := by rw [pow_succ]; ring
    _ ≤ (‖w‖^d*‖P i‖^d)*(M*‖P i-w‖) :=
      mul_le_mul_of_nonneg_left (hbound i w (mem_ball_self hd)) (by positivity)
    _ = _ := by ring

/-- The entire Taylor subtraction is obtained from the anchored term by
telescoping absolutely summable series. Index m corresponds to cutoff m+2. -/
theorem anchoredPoleSum_taylor_remainder {ι : Type*} (P : ι → ℂ) (hp : ∀ i, P i ≠ 0)
    (hs : ∀ m : ℕ, Summable (fun i => 1/‖P i‖^(m+2))) {U : Set ℂ} (hU : IsOpen U)
    (havoid : ∀ i, P i ∉ U) {w : ℂ} (hw : w ∈ U) (m : ℕ) :
    anchoredPoleSum P w = (∑ j ∈ range m, w^(j+1)*(∑' i, (1:ℂ)/P i^(j+2))) +
      ∑' i, w^(m+1)/(P i^(m+1)*(P i-w)) := by
  induction m with
  | zero => simp [anchoredPoleSum]
  | succ m ih =>
    have sep i : P i-w ≠ 0 := sub_ne_zero.mpr (fun e => havoid i (e ▸ hw))
    have hprev := pole_remainder_summable P (m+1) hp (hs m) hU havoid hw
    have hmom : Summable (fun i => (1:ℂ)/P i^(m+2)) :=
      Summable.of_norm (by simpa only [norm_div,norm_one,norm_pow] using hs m)
    have hnext :
        (∑' i, w^(m+2)/(P i^(m+2)*(P i-w))) =
        (∑' i, w^(m+1)/(P i^(m+1)*(P i-w))) - w^(m+1)*(∑' i, (1:ℂ)/P i^(m+2)) := by
      rw [←tsum_mul_left,←hprev.tsum_sub (hmom.mul_left (w^(m+1)))]
      apply tsum_congr
      intro i
      simpa only [mul_one_div] using next_pole_remainder (m+1) (hp i) (sep i)
    rw [sum_range_succ,hnext,ih]
    ring

#print axioms pole_remainder_summable
#print axioms anchoredPoleSum_taylor_remainder
end OpenMathResearch.LongCycleExcedances
