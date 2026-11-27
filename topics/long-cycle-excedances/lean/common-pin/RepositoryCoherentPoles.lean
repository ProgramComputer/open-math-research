import LongCycleBounds.CycleProfileLogistic
import LongCycleBounds.BandMoments
import LongCycleBounds.PartialFractions

noncomputable section
namespace RepositoryQuotientAudit

open PowerSeries Finset LongCycles LongCycleBounds
open LongCycleBounds.CycleProfile LongCycleBounds.MarkedTwo
open scoped Real

/-- Finite-cycle correction to the formal logistic series. -/
def coherentTilt (k : ℕ) (t : ℝ) : PowerSeries ℝ :=
  linearExp (-t/(1-t)) * expOf (rescale (1/(1-t)) (logTilt (profile k 0) t))

/-- The common formal coefficient identity for the actual permutation row. -/
theorem original_logistic_coefficient (n k : ℕ) (hk : 2 ≤ k) (t : ℝ)
    (hlo : -1 ≤ t) (hhi : t ≤ 0) :
    coeff n (coherentTilt k t * logistic t) =
      (enumerator n k).eval t / ((1-t)^(n+1)*n.factorial) := by
  have heq := normalized_coefficient (profile k 0) t n
  rw [normalized_logistic _ _ hlo hhi, coeff_C_mul, row_zero n hk] at heq
  have ht : (1:ℝ)-t ≠ 0 := by linarith
  have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  apply (eq_div_iff (mul_ne_zero (pow_ne_zero _ ht) hf)).mpr
  have hcross := (eq_div_iff (mul_ne_zero (pow_ne_zero _ ht) hf)).mp heq
  unfold coherentTilt
  rw [mul_assoc, pow_succ]
  linear_combination hcross

/-- Past degree one, the logarithm removes exactly the inadmissible cycle moments. -/
theorem original_rescaled_logTilt_coeff (k a : ℕ) (t : ℝ) :
    coeff a (rescale (1/(1-t)) (logTilt (profile k 0) t)) =
      if 2 ≤ a ∧ a < k then
        -Band.moment a t / (a.factorial:ℝ) else 0 := by
  rw [coeff_rescale, logTilt, coeff_mk]
  by_cases ha : a < 2
  · simp [ha, not_le_of_gt ha]
  · have h₂ : 2 ≤ a := le_of_not_gt ha
    by_cases hk : a < k
    · simp [ha, h₂, hk, profile, Band.moment]
      ring
    · simp [ha, h₂, hk, profile]

/-- The signed pole with index l in the complete odd-pole lattice. -/
def coherentPole (x : ℝ) (l : ℤ) : ℂ :=
  (x : ℂ) + (2 * (l : ℂ) + 1) * π * Complex.I

private theorem pole_abs_bound (x : ℝ) (l : ℤ) :
    0 < |(l:ℝ)+1/2| ∧ |(l:ℝ)+1/2| ≤ ‖coherentPole x l‖ := by
  have ho : (2*l+1 : ℤ) ≠ 0 := by omega
  have ho' : (2*(l:ℝ)+1) ≠ 0 := by exact_mod_cast ho
  refine ⟨abs_pos.mpr (by intro e; apply ho'; linarith), ?_⟩
  refine le_trans ?_ (Complex.abs_im_le_norm _)
  unfold coherentPole
  rw [Complex.add_im, Complex.ofReal_im, zero_add, Complex.mul_I_im]
  have hh : (2 * (l : ℂ) + 1) * (π : ℂ) = (((2 * (l : ℝ) + 1) * π : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hh, Complex.ofReal_re, show (2*(l : ℝ)+1)*π = ((l : ℝ)+1/2)*(2*π) by ring,
    abs_mul, abs_of_pos (by positivity : 0 < 2*π)]
  exact le_mul_of_one_le_right (abs_nonneg _) (by linarith [Real.pi_gt_three])

theorem summable_coherentPole_pow (x : ℝ) {p : ℕ} (hp : 2 ≤ p) :
    Summable (fun l : ℤ => (1:ℂ) / coherentPole x l ^ p) := by
  have hs : Summable (fun l : ℤ ↦ 1 / |(l : ℝ) + 1/2| ^ p) := by
    simpa using (Real.summable_one_div_int_add_rpow (1/2) (p : ℝ)).mpr (by exact_mod_cast
      (show 1 < p by omega))
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun l => norm_nonneg _) _ hs
  intro l
  have hl := pole_abs_bound x l
  simp only [norm_div, norm_one, norm_pow]
  exact one_div_le_one_div_of_le (pow_pos hl.1 _) (pow_le_pow_left₀ hl.1.le hl.2 _)

private theorem logistic_coeff_pole (x : ℝ) (hx : 0 ≤ x) {j : ℕ} (hj : 1 ≤ j) :
    ((coeff j (logistic (-Real.exp (-x))) : ℝ) : ℂ) = oddPoleSum (j+1) x := by
  have hf : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
  unfold logistic
  rw [coeff_mk, Complex.ofReal_div]
  simp only [logisticMoment, if_neg (by omega : j ≠ 0), sub_neg_eq_add]
  rw [eulerian_eq_oddPoleSum j hj x hx, Complex.ofReal_natCast]
  field_simp

private theorem logistic_coeff_zero (t : ℝ) :
    coeff 0 (logistic t) = 1/(1-t) := by simp [logistic, logisticMoment]

private theorem finite_to_pole_sum (T : PowerSeries ℝ) (x : ℝ) {n q : ℕ} (hnq : n ≤ q) :
    (∑ j ∈ range n, ((coeff j T : ℝ) : ℂ) * oddPoleSum (q-j+1) x) =
      ∑' l : ℤ, ∑ j ∈ range n, ((coeff j T : ℝ) : ℂ) * (1 / coherentPole x l ^ (q-j+1)) := by
  have hs (j : ℕ) (hj : j ∈ range n) :
      Summable (fun l : ℤ => ((coeff j T : ℝ) : ℂ) * (1 / coherentPole x l ^ (q-j+1))) :=
    (summable_coherentPole_pow x (by have := mem_range.mp hj; omega)).mul_left _
  rw [Summable.tsum_finsetSum hs]
  apply sum_congr rfl
  intro j hj
  rw [tsum_mul_left]
  rfl

/-- Each coefficient separates off the zero-order logistic term. The remaining
absolutely convergent sum carries the same truncated multiplier at each pole. -/
theorem coherent_product_coefficient (T : PowerSeries ℝ) (x : ℝ) (hx : 0 ≤ x) (n : ℕ) :
    ((coeff n (T * logistic (-Real.exp (-x))) : ℝ) : ℂ) =
      ((coeff n T / (1 + Real.exp (-x)) : ℝ) : ℂ) +
        ∑' l : ℤ, ∑ j ∈ range n, ((coeff j T : ℝ) : ℂ) * (1 / coherentPole x l ^ (n-j+1)) := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    sum_range_succ, Nat.sub_self, logistic_coeff_zero, Complex.ofReal_add]
  simp only [sub_neg_eq_add]
  rw [mul_one_div (coeff n T) (1 + Real.exp (-x))]
  rw [add_comm, Complex.ofReal_sum, ← finite_to_pole_sum T x le_rfl]
  congr 1
  apply sum_congr rfl
  intro j hj
  have hp : 1 ≤ n-j := by have := mem_range.mp hj; omega
  rw [Complex.ofReal_mul, logistic_coeff_pole x hx hp]

/-- Two adjacent formal coefficients share the same truncated multiplier. The
new coefficient has the two separately displayed highest tilt terms. -/
theorem coherent_successor_coefficient (T : PowerSeries ℝ) (x : ℝ) (hx : 0 ≤ x) (n : ℕ) :
    ((coeff (n+1) (T * logistic (-Real.exp (-x))) : ℝ) : ℂ) =
      ((coeff (n+1) T / (1 + Real.exp (-x)) : ℝ) : ℂ) +
        ((coeff n T : ℝ) : ℂ) * oddPoleSum 2 x +
        ∑' l : ℤ, ∑ j ∈ range n, ((coeff j T : ℝ) : ℂ) * (1 / coherentPole x l ^ ((n+1)-j+1)) := by
  rw [coherent_product_coefficient T x hx, ← finite_to_pole_sum T x le_rfl, sum_range_succ,
    show n+1-n+1 = 2 by omega, finite_to_pole_sum T x (Nat.le_succ n)]
  ring


/-- The two literal adjacent original rows have one common pole truncation. -/
theorem original_coherent_row_pair (n k : ℕ) (hk : 2 ≤ k) (x : ℝ) (hx : 0 ≤ x) :
    let t := -Real.exp (-x)
    let T := coherentTilt k t
    (((enumerator n k).eval t / ((1-t)^(n+1)*n.factorial) : ℝ) : ℂ) =
      ((coeff n T / (1 + Real.exp (-x)) : ℝ) : ℂ) +
        (∑' l : ℤ, ∑ j ∈ range n, ((coeff j T : ℝ) : ℂ) * (1 / coherentPole x l ^ (n-j+1))) ∧
    (((enumerator (n+1) k).eval t / ((1-t)^(n+1+1)*(n+1).factorial) : ℝ) : ℂ) =
      ((coeff (n+1) T / (1 + Real.exp (-x)) : ℝ) : ℂ) +
        ((coeff n T : ℝ) : ℂ) * oddPoleSum 2 x +
        ∑' l : ℤ, ∑ j ∈ range n, ((coeff j T : ℝ) : ℂ) * (1 / coherentPole x l ^ ((n+1)-j+1)) := by
  dsimp only
  have hlo : -1 ≤ -Real.exp (-x) :=
    neg_le_neg (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx))
  have hhi : -Real.exp (-x) ≤ 0 := neg_nonpos.mpr (Real.exp_pos _).le
  rw [← original_logistic_coefficient n k hk _ hlo hhi,
    ← original_logistic_coefficient (n+1) k hk _ hlo hhi]
  exact ⟨coherent_product_coefficient _ x hx n, coherent_successor_coefficient _ x hx n⟩

#print axioms original_logistic_coefficient
#print axioms original_rescaled_logTilt_coeff
#print axioms coherent_product_coefficient
#print axioms coherent_successor_coefficient
#print axioms original_coherent_row_pair
end RepositoryQuotientAudit
