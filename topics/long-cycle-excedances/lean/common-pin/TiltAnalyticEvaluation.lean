import MonomialTiltBounds
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed

noncomputable section
namespace RepositoryQuotientAudit
open PowerSeries Finset LongCycleBounds.CycleProfile

def seriesValue (f : PowerSeries ℝ) (w : ℂ) : ℂ :=
  ∑' j, ((coeff j f : ℝ) : ℂ) * w^j

theorem seriesValue_mul {f g : PowerSeries ℝ} (w : ℂ)
    (hf : Summable (fun j => ‖((coeff j f : ℝ) : ℂ) * w^j‖))
    (hg : Summable (fun j => ‖((coeff j g : ℝ) : ℂ) * w^j‖)) :
    seriesValue f w * seriesValue g w = seriesValue (f*g) w := by
  unfold seriesValue
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf hg]
  refine tsum_congr fun n => ?_
  rw [coeff_mul, Complex.ofReal_sum, sum_mul]
  apply sum_congr rfl
  intro ij hij
  have he : ij.1 + ij.2 = n := by simpa using hij
  rw [Complex.ofReal_mul, ← he, pow_add]
  ring

theorem seriesValue_one (w : ℂ) : seriesValue 1 w = 1 := by
  unfold seriesValue
  rw [tsum_eq_single 0]
  · simp
  · intro i hi
    simp [coeff_one, hi]

theorem seriesValue_monomial_exp (d : ℕ) (hd : 0 < d) (a : ℝ) (w : ℂ) :
    seriesValue (expOf (C a * (X : PowerSeries ℝ)^d)) w =
        Complex.exp ((a : ℂ) * w^d) := by
  let f (j : ℕ) := ((coeff j (expOf (C a * (X : PowerSeries ℝ)^d)) : ℝ) : ℂ) * w^j
  have hi : Function.Injective (fun j : ℕ => d*j) := by
    intro i j h
    exact Nat.eq_of_mul_eq_mul_left hd h
  have hsupport : Function.support f ⊆ Set.range (fun j : ℕ => d*j) := by
    intro j hj
    by_contra h
    have hnd : ¬ d ∣ j := fun ⟨i, hi⟩ => h ⟨i, hi.symm⟩
    apply hj
    simp [f, monomial_exp_coeff _ _ hd, hnd]
  change (∑' j, f j) = _
  rw [← hi.tsum_eq hsupport, Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div]
  refine tsum_congr fun j => ?_
  simp [f, monomial_exp_coeff _ _ hd, Nat.mul_div_cancel_left _ hd, mul_pow, pow_mul]
  ring

private theorem finiteTiltSummable (g : ℕ → ℝ) (m : ℕ) (w : ℂ) :
    Summable (fun j => ‖((coeff j (expOf (finiteTilt g m)) : ℝ) : ℂ) * w^j‖) := by
  let R := ‖w‖+1
  have hR : 0 < R := by dsimp [R]; positivity
  let A := Real.exp (∑ i ∈ range m, |g (i+1)*R^(i+1)|)
  have hA : 0 < A := Real.exp_pos _
  have hbound (j : ℕ) : |coeff j (expOf (finiteTilt g m))| ≤ A / R^j := by
    have h := finiteTilt_exp_bound g m R hR.le j
    unfold LongCycleBounds.MarkedTwo.scaledCoeff at h
    rw [abs_mul, abs_of_nonneg (pow_nonneg hR.le _), pow_succ] at h
    apply (le_div_iff₀ (pow_pos hR _)).2
    apply le_of_mul_le_mul_left _ hR
    simpa only [mul_assoc, mul_left_comm, mul_comm] using h
  have hratio : ‖w‖/R < 1 := (div_lt_one hR).2 (by dsimp [R]; linarith)
  have hgeo := summable_geometric_of_lt_one (div_nonneg (norm_nonneg _) hR.le) hratio
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_ (hgeo.mul_left A)
  intro j
  rw [norm_mul, Complex.norm_real, norm_pow, div_pow]
  calc
    _ ≤ A / R^j * ‖w‖^j := mul_le_mul_of_nonneg_right (hbound j) (by positivity)
    _ = _ := by ring

theorem seriesValue_finiteTilt_exp (g : ℕ → ℝ) (m : ℕ) (w : ℂ) :
    seriesValue (expOf (finiteTilt g m)) w =
      Complex.exp (∑ i ∈ range m, (g (i+1) : ℂ) * w^(i+1)) := by
  induction m with
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
    simp only [finiteTilt, range_zero, sum_empty, hzero, seriesValue_one, Complex.exp_zero]
  | succ m ih =>
    have hstep : finiteTilt g (m+1) =
        finiteTilt g m + C (g (m+1)) * (X : PowerSeries ℝ)^(m+1) := by
      simp [finiteTilt, sum_range_succ]
    rw [hstep, expOf_add (finiteTilt_constant g m) (by simp), sum_range_succ, Complex.exp_add,
      ← seriesValue_mul w (finiteTiltSummable g m w) ?_,
      ih, seriesValue_monomial_exp (m+1) (by omega)]
    let single (j : ℕ) := if j=m+1 then g (m+1) else 0
    have hsingle : finiteTilt single (m+1) =
        C (g (m+1))*(X : PowerSeries ℝ)^(m+1) := by
      unfold finiteTilt
      rw [sum_eq_single m]
      · simp [single]
      · intro i hi hne
        have h : i+1 ≠ m+1 := by omega
        simp [single, h]
      · simp
    rw [← hsingle]
    exact finiteTiltSummable single (m+1) w

theorem seriesValue_original_coherentTilt {k : ℕ} (hk : 2 ≤ k) (t : ℝ) (w : ℂ) :
    seriesValue (coherentTilt k t) w =
      Complex.exp (∑ i ∈ range (k-1), (cutoffLogCoefficient k t (i+1) : ℂ) * w^(i+1)) := by
  rw [coherentTilt_exp_finite hk, seriesValue_finiteTilt_exp]

/-- Principal-pole amplitude lower bound using the same log-coefficient
mass as the formal Taylor majorant. -/
theorem norm_seriesValue_coherentTilt_ge {k : ℕ} (hk : 2 ≤ k) (t : ℝ) (w : ℂ)
    (R : ℝ) (hR : ‖w‖ ≤ R) :
    Real.exp (-(∑ i ∈ range (k-1), |cutoffLogCoefficient k t (i+1)*R^(i+1)|)) ≤
      ‖seriesValue (coherentTilt k t) w‖ := by
  rw [seriesValue_original_coherentTilt hk, Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  let u (i : ℕ) : ℂ := (cutoffLogCoefficient k t (i+1):ℂ)*w^(i+1)
  change -(∑ i ∈ range (k-1), |cutoffLogCoefficient k t (i+1)*R^(i+1)|) ≤
    (∑ i ∈ range (k-1), u i).re
  have hsum : ‖∑ i ∈ range (k-1), u i‖ ≤
      ∑ i ∈ range (k-1), |cutoffLogCoefficient k t (i+1)*R^(i+1)| := by
    refine (norm_sum_le _ _).trans ?_
    apply sum_le_sum
    intro i _
    have hR0 : 0 ≤ R := (norm_nonneg _).trans hR
    simp only [u, norm_mul, Complex.norm_real, norm_pow, abs_mul, abs_pow, abs_of_nonneg hR0]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hR _) (abs_nonneg _)
  have hre := Complex.abs_re_le_norm (∑ i ∈ range (k-1), u i)
  exact (neg_le_neg (hre.trans hsum)).trans (neg_abs_le _)

#print axioms seriesValue_original_coherentTilt
#print axioms norm_seriesValue_coherentTilt_ge
end RepositoryQuotientAudit
