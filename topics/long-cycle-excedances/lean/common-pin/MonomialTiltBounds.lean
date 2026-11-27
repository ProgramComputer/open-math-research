import RepositoryCoherentPoles

noncomputable section
namespace RepositoryQuotientAudit
open PowerSeries Finset LongCycleBounds.MarkedTwo LongCycleBounds.CycleProfile

private theorem monomial_exp_coeff (d j : ℕ) (hd : 0 < d) (a : ℝ) :
    coeff j (expOf (C a * (X : PowerSeries ℝ)^d)) =
      if d ∣ j then a^(j/d)/(j/d).factorial else 0 := by
  have hzero : constantCoeff (C a * (X : PowerSeries ℝ)^d) = 0 := by
    simp [zero_pow hd.ne']
  rw [expOf, coeff_subst' (.of_constantCoeff_zero' hzero)]
  have hterm (i : ℕ) :
      coeff i (PowerSeries.exp ℝ) • coeff j ((C a * (X : PowerSeries ℝ)^d)^i) =
        if j = d*i then a^i/(i.factorial:ℝ) else 0 := by
    rw [coeff_exp, smul_eq_mul, mul_pow, ← map_pow C, ← pow_mul, coeff_C_mul, coeff_X_pow]
    split_ifs <;> push_cast <;> ring
  simp_rw [hterm]
  by_cases hy : d ∣ j
  · rw [if_pos hy, finsum_eq_single _ (j/d), if_pos (Nat.mul_div_cancel' hy).symm]
    intro i hi
    apply if_neg
    intro h
    apply hi
    rw [h, Nat.mul_div_cancel_left _ hd]
  · rw [if_neg hy, finsum_eq_zero_of_forall_eq_zero]
    intro i
    apply if_neg
    intro he
    exact hy ⟨i, he⟩

theorem monomial_exp_scaled (d j : ℕ) (hd : 0 < d) (a ρ : ℝ) (f : PowerSeries ℝ) :
    scaledCoeff (expOf (C a * (X : PowerSeries ℝ)^d) * f) ρ j =
      shiftExp d (a*ρ^d) (scaledCoeff f ρ) j := by
  unfold scaledCoeff shiftExp
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, mul_sum]
  let G (i : ℕ) :=
    ρ^(j+1) * (coeff i (expOf (C a*(X : PowerSeries ℝ)^d)) * coeff (j-i) f)
  change (∑ i ∈ range (j+1), G i) = _
  have hfilter : (∑ i ∈ (range (j+1)).filter (d ∣ ·), G i) =
      ∑ i ∈ range (j+1), G i := by
    apply sum_subset (filter_subset _ _)
    intro i hi hnot
    have hnd : ¬ d ∣ i := fun H => hnot (mem_filter.mpr ⟨hi,H⟩)
    simp [G, monomial_exp_coeff _ _ hd, hnd]
  rw [← hfilter]
  refine sum_bij' (fun i _ => i/d) (fun h _ => d*h) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    have hi' := mem_range.mp (mem_filter.mp hi).1
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (Nat.le_of_lt_succ hi')))
  · intro h hh
    have hh' := Nat.le_of_lt_succ (mem_range.mp hh)
    have hle : d*h ≤ j := by
      simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hd).mp hh'
    exact mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le hle), dvd_mul_right _ _⟩
  · intro i hi
    exact Nat.mul_div_cancel' (mem_filter.mp hi).2
  · intro h _
    exact Nat.mul_div_cancel_left _ hd
  · intro i hi
    have hh := (mem_filter.mp hi).2
    have hi' := Nat.le_of_lt_succ (mem_range.mp (mem_filter.mp hi).1)
    have he := Nat.mul_div_cancel' hh
    have hp : ρ^(j+1) = ρ^(d*(i/d)) * ρ^(j-i+1) := by
      rw [← pow_add, he]
      congr 1
      omega
    dsimp only [G]
    rw [monomial_exp_coeff _ _ hd, if_pos hh,
      show j-d*(i/d)=j-i by rw [he], mul_pow, hp, pow_mul]
    ring

/-- Absolute version of the supplying single-monomial estimate. -/
theorem signed_shiftExp_abs {M v : ℝ} (hM : 0 ≤ M)
    (d j : ℕ) (F : ℕ → ℝ) (hF : ∀ i ≤ j, |F i| ≤ M) :
    |shiftExp d v F j| ≤ M*Real.exp |v| := by
  unfold shiftExp
  apply (abs_sum_le_sum_abs ..).trans
  calc
    _ ≤ ∑ i ∈ range (j/d+1), (|v|^i/i.factorial)*M := by
      apply sum_le_sum
      intro i _
      rw [abs_mul, abs_div, abs_pow, abs_of_nonneg (by positivity : 0 ≤ (i.factorial:ℝ))]
      exact mul_le_mul_of_nonneg_left (hF _ (Nat.sub_le ..)) (by positivity)
    _ ≤ _ := by
      rw [← sum_mul, mul_comm M]
      exact mul_le_mul_of_nonneg_right (Real.sum_le_exp_of_nonneg (abs_nonneg _) _) hM


def finiteTilt (g : ℕ → ℝ) (m : ℕ) : PowerSeries ℝ :=
  ∑ i ∈ range m, C (g (i+1))*(X : PowerSeries ℝ)^(i+1)

private theorem finiteTilt_constant (g : ℕ → ℝ) (m : ℕ) :
    constantCoeff (finiteTilt g m) = 0 := by
  unfold finiteTilt
  rw [map_sum]
  simp

/-- Coefficient envelope for the exponential of an arbitrary finite log tilt. -/
theorem finiteTilt_exp_bound (g : ℕ → ℝ) (m : ℕ) (ρ : ℝ) (hρ : 0 ≤ ρ) (j : ℕ) :
    |scaledCoeff (expOf (finiteTilt g m)) ρ j| ≤
      ρ * Real.exp (∑ i ∈ range m, |g (i+1)*ρ^(i+1)|) := by
  induction m generalizing j with
  | zero =>
    have hzero : expOf (0 : PowerSeries ℝ) = 1 := by
      apply PowerSeries.ext
      intro i
      rw [show (0 : PowerSeries ℝ) = C 0 * X^1 by simp,
        monomial_exp_coeff _ _ (by decide), coeff_one]
      by_cases he : i = 0
      · subst i
        simp
      · simp [Nat.one_dvd, he, zero_pow he]
    simp only [finiteTilt, range_zero, sum_empty, hzero, Real.exp_zero, mul_one]
    unfold scaledCoeff
    rw [coeff_one]
    by_cases hj : j=0
    · subst j
      simp [abs_of_nonneg hρ]
    · simp [hj, hρ]
  | succ m ih =>
    have hstep : finiteTilt g (m+1) =
        finiteTilt g m + C (g (m+1)) * (X : PowerSeries ℝ)^(m+1) := by
      simp [finiteTilt, sum_range_succ]
    rw [hstep, expOf_add (finiteTilt_constant g m) (by simp),
      mul_comm (expOf (finiteTilt g m)),
      monomial_exp_scaled _ _ (Nat.succ_pos _) _ _ _, sum_range_succ, Real.exp_add]
    have hM : 0 ≤ ρ * Real.exp (∑ i ∈ range m, |g (i+1)*ρ^(i+1)|) :=
      mul_nonneg hρ (Real.exp_pos _).le
    calc
      _ ≤ (ρ * Real.exp (∑ i ∈ range m, |g (i+1)*ρ^(i+1)|)) *
          Real.exp |g (m+1)*ρ^(m+1)| :=
        signed_shiftExp_abs hM _ _ _ (fun i _ => ih i)
      _ = _ := by ring


private theorem coeff_finiteTilt (g : ℕ → ℝ) (m j : ℕ) :
    coeff j (finiteTilt g m) = if 1 ≤ j ∧ j ≤ m then g j else 0 := by
  induction m with
  | zero =>
    simp only [finiteTilt, range_zero, sum_empty, map_zero]
    rw [if_neg (by omega : ¬(1 ≤ j ∧ j ≤ 0))]
  | succ m ih =>
    have h : finiteTilt g (m+1) =
        finiteTilt g m + C (g (m+1)) * (X : PowerSeries ℝ)^(m+1) := by
      simp [finiteTilt, sum_range_succ]
    rw [h, map_add, ih, coeff_C_mul, coeff_X_pow]
    by_cases he : j=m+1
    · subst j
      simp
    · have hh : (1 ≤ j ∧ j ≤ m+1) ↔ (1 ≤ j ∧ j ≤ m) := by omega
      simp [he, hh]

def cutoffLogCoefficient (k : ℕ) (t : ℝ) (j : ℕ) : ℝ :=
  if j = 1 then -t/(1-t)
  else if 2 ≤ j ∧ j < k then -LongCycleBounds.Band.moment j t / (j.factorial:ℝ)
  else 0

private theorem coherentTilt_exp_finite {k : ℕ} (hk : 2 ≤ k) (t : ℝ) :
    coherentTilt k t = expOf (finiteTilt (cutoffLogCoefficient k t) (k-1)) := by
  have hlin (a : ℝ) : linearExp a = expOf (C a*(X : PowerSeries ℝ)^1) := by
    apply PowerSeries.ext
    intro j
    rw [monomial_exp_coeff _ _ (by decide)]
    simp [linearExp]
  unfold coherentTilt
  rw [hlin, ← expOf_add (by simp)
    (by rw [← coeff_zero_eq_constantCoeff_apply, original_rescaled_logTilt_coeff]; simp)]
  congr 1
  apply PowerSeries.ext
  intro j
  rw [map_add, coeff_C_mul, coeff_X_pow, original_rescaled_logTilt_coeff, coeff_finiteTilt]
  by_cases h0 : j = 0
  · subst j
    simp
  by_cases h1 : j = 1
  · subst j
    have hk' : 1 ≤ k-1 := by omega
    simp [cutoffLogCoefficient, hk']
  have h₂ : 2 ≤ j := by omega
  have he : j ≤ k-1 ↔ j < k := by omega
  by_cases hjk : j < k <;> simp [cutoffLogCoefficient, h1, h₂, (by omega : 1 ≤ j), he, hjk]

/-- Concrete coefficient envelope for the common-cutoff numerator, expressed
using the finite logarithm on the chosen radius. -/
theorem original_coherentTilt_coeff_bound {k : ℕ} (hk : 2 ≤ k) (t R : ℝ)
    (hR : 0 < R) (j : ℕ) :
    |coeff j (coherentTilt k t)| ≤
      Real.exp (∑ i ∈ range (k-1), |cutoffLogCoefficient k t (i+1)*R^(i+1)|) / R^j := by
  have h := finiteTilt_exp_bound (cutoffLogCoefficient k t) (k-1) R hR.le j
  rw [← coherentTilt_exp_finite hk] at h
  unfold scaledCoeff at h
  rw [abs_mul, abs_of_nonneg (pow_nonneg hR.le _), pow_succ] at h
  apply (le_div_iff₀ (pow_pos hR _)).2
  apply le_of_mul_le_mul_left _ hR
  simpa only [mul_assoc, mul_left_comm, mul_comm] using h

#print axioms original_coherentTilt_coeff_bound
end RepositoryQuotientAudit
