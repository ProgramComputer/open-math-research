import OpenMathResearch.FiniteTailMoments
import BalancedOccupiedTilt

namespace BalancedEventual.OccupiedPhase

open Finset
open scoped BigOperators

noncomputable section

private theorem probability_step {d r s : ℕ} (hs : s ≤ d) (v : ℝ) :
    probability d r v (s + 1) * ((s : ℝ) + 1) =
      probability d r v s * ((d : ℝ) - s) * v := by
  have hb : (d.choose (s + 1) : ℝ) * ((s : ℝ) + 1) =
      (d.choose s : ℝ) * ((d : ℝ) - s) := by
    rw [← Nat.cast_sub hs]
    exact_mod_cast Nat.choose_succ_right_eq d s
  simp only [probability, rowWeight, pow_succ]
  calc
    _ = ((d.choose (s + 1) : ℝ) * ((s : ℝ) + 1)) * (v ^ s * v) / mass d r v := by ring
    _ = _ := by rw [hb]; ring

/-- Summation by parts for the truncated binomial. The term at the cap is
the contribution removed by truncation. -/
theorem weighted_shift {d r : ℕ} (hrd : r ≤ d) (v : ℝ) (g : ℕ → ℝ) :
    ∑ s ∈ range (r + 1), probability d r v s * s * g s =
      v * ((∑ s ∈ range (r + 1),
        probability d r v s * ((d : ℝ) - s) * g (s + 1)) -
        probability d r v r * ((d : ℝ) - r) * g (r + 1)) := by
  calc
    _ = ∑ s ∈ range r, probability d r v (s + 1) * ((s : ℝ) + 1) * g (s + 1) := by
      rw [Finset.sum_range_succ']
      simp
    _ = ∑ s ∈ range r, v * (probability d r v s * ((d : ℝ) - s) * g (s + 1)) := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [probability_step ((Finset.mem_range.mp hs).le.trans hrd)]
      ring
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_range_succ]; ring

private def secondMoment (d r : ℕ) (v : ℝ) : ℝ :=
  ∑ s ∈ range (r + 1), probability d r v s * (s : ℝ) ^ 2

private theorem variance_eq_moment_sub_mean_sq (d r : ℕ) {v : ℝ} (hv : 0 < v) :
    variance d r v = secondMoment d r v - mean d r v ^ 2 := by
  unfold variance secondMoment
  calc
    _ = ∑ s ∈ range (r + 1),
        (probability d r v s * (s : ℝ) ^ 2 -
        (probability d r v s * s) * (2 * mean d r v) +
        probability d r v s * mean d r v ^ 2) := by
      apply Finset.sum_congr rfl
      intro s _
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
        ← Finset.sum_mul, sum_probability d r hv]
      change _ - mean d r v * (2 * mean d r v) + 1 * mean d r v ^ 2 = _
      ring

private theorem mean_balance {d r : ℕ} (hrd : r ≤ d) {v : ℝ} (hv : 0 < v) :
    (1 + v) * mean d r v = v * ((d : ℝ) - probability d r v r * ((d : ℝ) - r)) := by
  have hh := weighted_shift hrd v (fun _ => 1)
  simp only [mul_one] at hh
  have heq : (∑ s ∈ range (r + 1), probability d r v s * ((d : ℝ) - s)) =
      (d : ℝ) - mean d r v := by
    simp only [mean, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
      sum_probability d r hv, one_mul]
  rw [heq] at hh
  change mean d r v = _ at hh
  linear_combination hh

private theorem second_balance {d r : ℕ} (hrd : r ≤ d) (v : ℝ) :
    secondMoment d r v - mean d r v =
      v * ((d : ℝ) * mean d r v - secondMoment d r v -
        probability d r v r * ((d : ℝ) - r) * (r : ℝ)) := by
  have hh := weighted_shift hrd v (fun s => (s : ℝ) - 1)
  simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] at hh
  have h1 : (∑ s ∈ range (r + 1), probability d r v s * s * ((s : ℝ) - 1)) =
      secondMoment d r v - mean d r v := by
    unfold mean secondMoment
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro s _
    ring
  have h2 : (∑ s ∈ range (r + 1), probability d r v s * ((d : ℝ) - s) * s) =
      (d : ℝ) * mean d r v - secondMoment d r v := by
    unfold mean secondMoment
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro s _
    ring
  rwa [h1, h2] at hh

/-- The exact variance loss of the truncated binomial relative to its
mean multiplied by the failure probability of one untruncated trial. -/
theorem variance_balance {d r : ℕ} (hrd : r ≤ d) {v : ℝ} (hv : 0 < v) :
    (1 + v) * variance d r v =
      mean d r v - v * probability d r v r * ((d : ℝ) - r) * ((r : ℝ) - mean d r v) := by
  rw [variance_eq_moment_sub_mean_sq d r hv]
  linear_combination second_balance hrd v - mean d r v * mean_balance hrd hv

private theorem scaled_variance_le_mean {d r : ℕ} (hrd : r ≤ d) {v : ℝ} (hv : 0 < v) :
    (1 + v) * variance d r v ≤ mean d r v := by
  have hD : (r : ℝ) ≤ d := by exact_mod_cast hrd
  have hB : 0 ≤ probability d r v r * ((d : ℝ) - r) :=
    mul_nonneg (probability_nonneg d r r hv) (sub_nonneg.mpr hD)
  rw [variance_balance hrd hv]
  apply sub_le_self
  rw [mul_assoc v]
  exact mul_nonneg (mul_nonneg hv.le hB) (sub_nonneg.mpr (mean_le d r hv))

/-- The capped binomial has variance at most d/4, uniformly over the tilt. -/
theorem variance_le_dimension_quarter {d r : ℕ} (hrd : r ≤ d) {v : ℝ} (hv : 0 < v) :
    variance d r v ≤ (d : ℝ) / 4 := by
  have hD : (r : ℝ) ≤ d := by exact_mod_cast hrd
  have hB : 0 ≤ probability d r v r * ((d : ℝ) - r) :=
    mul_nonneg (probability_nonneg d r r hv) (sub_nonneg.mpr hD)
  have hv' : 0 < 1 + v := by linarith
  have h1 := scaled_variance_le_mean hrd hv
  have h2 : (1 + v) * mean d r v ≤ v * (d : ℝ) := by
    rw [mean_balance hrd hv]
    exact mul_le_mul_of_nonneg_left (sub_le_self _ hB) hv.le
  have h3 : (1 + v) * ((1 + v) * variance d r v) ≤ v * (d : ℝ) :=
    (mul_le_mul_of_nonneg_left h1 hv'.le).trans h2
  have h4 : v * (d : ℝ) ≤ (1 + v) * ((1 + v) * ((d : ℝ) / 4)) := by
    nlinarith [mul_nonneg (Nat.cast_nonneg d) (sq_nonneg (1 - v))]
  exact le_of_mul_le_mul_left (le_of_mul_le_mul_left (h3.trans h4) hv') hv'

/-- Truncation gives variance at most the mean. -/
theorem variance_le_mean {d r : ℕ} (hrd : r ≤ d) {v : ℝ} (hv : 0 < v) :
    variance d r v ≤ mean d r v := by
  have h1 := scaled_variance_le_mean hrd hv
  have hV : 0 ≤ variance d r v := by
    unfold variance
    exact Finset.sum_nonneg fun s _ =>
      mul_nonneg (probability_nonneg d r s hv) (sq_nonneg _)
  nlinarith [mul_nonneg hv.le hV]

theorem variance_le_mean_times_one_add_mean {d r : ℕ} (hrd : r ≤ d) {v : ℝ} (hv : 0 < v) :
    variance d r v ≤ mean d r v * (1 + mean d r v) :=
  (variance_le_mean hrd hv).trans (by nlinarith [sq_nonneg (mean d r v)])

#print axioms variance_le_mean
#print axioms variance_le_mean_times_one_add_mean
#print axioms weighted_shift
#print axioms variance_balance
#print axioms variance_le_dimension_quarter

/-- The reflected size law, extended by zero beyond its support. -/
def deficitProbability (d r : ℕ) (v : ℝ) (j : ℕ) : ℝ :=
  if j ≤ r then probability d r v (r-j) else 0

private theorem deficit_nonneg (d r j : ℕ) {v : ℝ} (hv : 0 < v) :
    0 ≤ deficitProbability d r v j := by
  unfold deficitProbability
  split
  · exact probability_nonneg d r _ hv
  · exact le_rfl

private def deficitRatio (d r : ℕ) (v : ℝ) (j : ℕ) : ℝ :=
  ((r : ℝ) - j) / (v * ((d : ℝ) - r + j + 1))

private theorem deficitRatio_step {d r j : ℕ} (hrd : r ≤ d) (hj : j < r)
    {v : ℝ} (hv : 0 < v) :
    deficitProbability d r v (j+1) = deficitRatio d r v j * deficitProbability d r v j := by
  have hd : (r : ℝ) ≤ d := by exact_mod_cast hrd
  have hden : 0 < v * ((d : ℝ) - r + j + 1) := by
    exact mul_pos hv (by linarith [Nat.cast_nonneg (α := ℝ) j])
  have hj' : j+1 ≤ r := hj
  simp only [deficitProbability, if_pos hj', if_pos hj.le, deficitRatio, div_mul_eq_mul_div]
  apply (eq_div_iff hden.ne').2
  have hstep := probability_step (r := r) (s := r-(j+1))
    (show r-(j+1) ≤ d by omega) v
  have heq : r-(j+1)+1 = r-j := by omega
  have hcast : ((r-(j+1) : ℕ) : ℝ) = (r : ℝ) - ((j : ℝ)+1) := by
    rw [Nat.cast_sub hj', Nat.cast_add, Nat.cast_one]
  rw [hcast, heq] at hstep
  linear_combination -hstep

private theorem deficitRatio_antitone {d r i j : ℕ} (hrd : r ≤ d) (hij : i ≤ j)
    (hj : j < r) {v : ℝ} (hv : 0 < v) :
    deficitRatio d r v j ≤ deficitRatio d r v i := by
  unfold deficitRatio
  have hd : (r : ℝ) ≤ d := by exact_mod_cast hrd
  have hi : (i : ℝ) ≤ j := by exact_mod_cast hij
  have hj' : (j : ℝ) ≤ r := by exact_mod_cast hj.le
  have hdi : 0 < v * ((d : ℝ) - r + i + 1) := by
    exact mul_pos hv (by linarith [Nat.cast_nonneg (α := ℝ) i])
  have hdj : 0 < v * ((d : ℝ) - r + j + 1) := by
    exact mul_pos hv (by linarith [Nat.cast_nonneg (α := ℝ) j])
  apply (div_le_div_iff₀ hdj hdi).2
  exact mul_le_mul (by linarith)
    (mul_le_mul_of_nonneg_left (by linarith) hv.le) hdi.le (by linarith)

private theorem deficit_cross {d r : ℕ} (hrd : r ≤ d) {v : ℝ} (hv : 0 < v)
    (a i j : ℕ) (hij : i ≤ j) :
    deficitProbability d r v (a+j) * deficitProbability d r v i ≤
      deficitProbability d r v (a+i) * deficitProbability d r v j := by
  induction a with
  | zero => simp [mul_comm]
  | succ a ih =>
    by_cases hj : a+j < r
    · have hi : a+i < r := by omega
      have hd : (r : ℝ) ≤ d := by exact_mod_cast hrd
      have hj' : ((a+j : ℕ) : ℝ) ≤ r := by exact_mod_cast hj.le
      have hq : 0 ≤ deficitRatio d r v (a+j) := by
        unfold deficitRatio
        exact div_nonneg (sub_nonneg.mpr hj') (mul_nonneg hv.le
          (by linarith [Nat.cast_nonneg (α := ℝ) (a+j)]))
      rw [show a.succ+j = a+j+1 by omega, show a.succ+i = a+i+1 by omega,
        deficitRatio_step hrd hj hv, deficitRatio_step hrd hi hv, mul_assoc, mul_assoc]
      exact (mul_le_mul_of_nonneg_left ih hq).trans
        (mul_le_mul_of_nonneg_right (deficitRatio_antitone hrd (by omega) hj hv)
          (mul_nonneg (deficit_nonneg _ _ _ hv) (deficit_nonneg _ _ _ hv)))
    · have hz : ¬ a.succ+j ≤ r := by omega
      rw [show deficitProbability d r v (a.succ+j) = 0 by simp [deficitProbability, hz], zero_mul]
      exact mul_nonneg (deficit_nonneg _ _ _ hv) (deficit_nonneg _ _ _ hv)

private theorem sum_deficit_eq_reflect (d r : ℕ) (v : ℝ) (f : ℕ → ℝ) :
    ∑ j ∈ range (r+1), deficitProbability d r v j * f j =
      ∑ j ∈ range (r+1), probability d r v j * f (r-j) := by
  conv_rhs =>
    rw [← Finset.sum_range_reflect (fun j => probability d r v j * f (r-j)) (r+1)]
  simp only [Nat.add_sub_cancel]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j ≤ r := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  rw [deficitProbability, if_pos hj', show r - (r-j) = j by omega]

/-- The law of the deficit obeys the log-concave variance bound. -/
theorem variance_le_deficit_times_one_add_deficit {d r : ℕ} (hrd : r ≤ d)
    {v : ℝ} (hv : 0 < v) :
    variance d r v ≤ ((r : ℝ) - mean d r v) * (1 + ((r : ℝ) - mean d r v)) := by
  let p := deficitProbability d r v
  have hp : ∀ i > r, p i = 0 := fun i hi => by simp [p, deficitProbability, not_le_of_gt hi]
  have h1 : OpenMathResearch.FiniteTailMoments.tail p r 0 = 1 := by
    simp only [OpenMathResearch.FiniteTailMoments.tail, Nat.zero_add, p]
    simpa only [mul_one] using
      (sum_deficit_eq_reflect d r v (fun _ => 1)).trans
        (by simpa only [mul_one] using sum_probability d r hv)
  have hμ : (∑ j ∈ range (r+1), p j * (j : ℝ)) = (r : ℝ) - mean d r v := by
    change (∑ j ∈ range (r+1), deficitProbability d r v j * (j : ℝ)) = _
    rw [sum_deficit_eq_reflect d r v (fun j => (j : ℝ))]
    calc
      _ = ∑ j ∈ range (r+1), (probability d r v j * (r : ℝ) - probability d r v j * j) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [Nat.cast_sub (Nat.le_of_lt_succ (Finset.mem_range.mp hj)), mul_sub]
      _ = _ := by rw [Finset.sum_sub_distrib, ← Finset.sum_mul, sum_probability d r hv, one_mul]; rfl
  have hV := OpenMathResearch.FiniteTailMoments.variance_le_mean_one_add_mean hp h1
    (deficit_cross hrd hv)
  dsimp only at hV
  rw [hμ] at hV
  refine le_trans (le_of_eq ?_) hV
  change variance d r v = ∑ j ∈ range (r+1), deficitProbability d r v j *
    ((j : ℝ) - ((r : ℝ) - mean d r v)) ^ 2
  rw [sum_deficit_eq_reflect d r v (fun j => ((j : ℝ) - ((r : ℝ) - mean d r v)) ^ 2)]
  unfold variance
  apply Finset.sum_congr rfl
  intro j hj
  rw [Nat.cast_sub (Nat.le_of_lt_succ (Finset.mem_range.mp hj))]
  ring

/-- All three variance inputs for the balanced-array tilt estimate are now
supplied by the actual finite law, with no additional variance hypotheses. -/
theorem phase_deviation_unconditional (n : ℕ) {d r : ℕ} {v : ℝ}
    (hr : 1 ≤ r) (hrd : r < d) (hv : 0 < v) :
    |phase n d r v / Real.pi - (n : ℝ) * mean d r v / d| ≤
      4 * Real.pi ^ 2 * ((n : ℝ) / d * min (mean d r v) ((r : ℝ) - mean d r v)) /
        Real.sqrt d + ((d : ℝ) - 1) / 2 :=
  phase_deviation_le_min_mean_deficit n hr hrd hv
    (variance_le_dimension_quarter hrd.le hv)
    (variance_le_mean_times_one_add_mean hrd.le hv)
    (variance_le_deficit_times_one_add_deficit hrd.le hv)

#print axioms variance_le_deficit_times_one_add_deficit
#print axioms phase_deviation_unconditional

end

end BalancedEventual.OccupiedPhase
