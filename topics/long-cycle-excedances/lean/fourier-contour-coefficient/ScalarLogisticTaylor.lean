import AnchoredPoleTaylor

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace OpenMathResearch.LongCycleExcedances

/-- Assemble the constant logistic coefficient with the signed-pole Taylor
tail, including a norm-summability witness for a subsequent Cauchy product. -/
theorem scalar_logistic_taylor {ι : Type*} (P : ι → ℂ) {r : ℝ}
    {w : ℂ} (hr : 0 < r) (hw : ‖w‖ < r) (hP : ∀ i, r ≤ ‖P i‖)
    (hs : Summable fun i => 1/‖P i‖^2)
    (c : ℕ → ℂ) (hc : ∀ i : ℕ, c (i+1) = ∑' l, 1/(P l)^(i+2)) :
    Summable (fun n : ℕ => ‖c n*w^n‖) ∧
    HasSum (fun n : ℕ => c n*w^n) (c 0 + ∑' i, w/(P i*(P i-w))) := by
  obtain ⟨hn,ha⟩ := anchored_pole_taylor P hr hw hP hs
  constructor
  · apply (summable_nat_add_iff 1).mp
    simpa only [hc] using hn
  · apply (hasSum_nat_add_iff' 1).mp
    simpa only [hc, Finset.sum_range_one, pow_zero, mul_one, add_sub_cancel_left] using ha

/-- There is no conditional rearrangement in the coefficient product. -/
theorem scalar_taylor_cauchy {a b : ℕ → ℂ} {u v w : ℂ}
    (ha : HasSum (fun n => a n*w^n) u) (hb : HasSum (fun n => b n*w^n) v)
    (hna : Summable (fun n => ‖a n*w^n‖)) (hnb : Summable (fun n => ‖b n*w^n‖)) :
    HasSum (fun n => (∑ i ∈ Finset.antidiagonal n, a i.1*b i.2)*w^n) (u*v) := by
  let A (n : ℕ) := a n*w^n
  let B (n : ℕ) := b n*w^n
  have hs := summable_mul_of_summable_norm (f := A) (g := B) hna hnb
  have h := summable_sum_mul_antidiagonal_of_summable_mul (f := A) (g := B) hs
  have he := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm (f := A) (g := B) hna hnb
  have heq : (∑' i, A i)*(∑' i, B i) = u*v := by
    rw [ha.tsum_eq,hb.tsum_eq]
  have hsum : HasSum (fun n => ∑ i ∈ Finset.antidiagonal n, A i.1*B i.2) (u*v) := by
    rw [←heq, he]
    exact h.hasSum
  convert hsum using 1
  funext n
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.mem_antidiagonal.mp hi,pow_add]
  ring

#print axioms scalar_logistic_taylor
#print axioms scalar_taylor_cauchy
end OpenMathResearch.LongCycleExcedances
