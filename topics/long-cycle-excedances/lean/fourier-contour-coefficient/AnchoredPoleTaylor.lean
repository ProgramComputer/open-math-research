import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Filter

/-- On a disk smaller than every pole modulus, the anchored resolvent has an
absolutely summable Taylor series. The anchored constant is zero. -/
theorem anchored_pole_taylor {ι : Type*} (P : ι → ℂ) {r : ℝ} {w : ℂ}
    (hr : 0 < r) (hw : ‖w‖ < r) (hP : ∀ i, r ≤ ‖P i‖)
    (hs : Summable fun i => 1/‖P i‖^2) :
    Summable (fun n : ℕ => ‖(∑' i, 1/(P i)^(n+2))*w^(n+1)‖) ∧
    HasSum (fun n : ℕ => (∑' i, 1/(P i)^(n+2))*w^(n+1))
      (∑' i, w/(P i*(P i-w))) := by
  let A : ℕ → ι → ℂ := fun n i => (1/(P i)^(n+2))*w^(n+1)
  let q := ‖w‖/r
  have hq0 : 0 ≤ q := div_nonneg (norm_nonneg _) hr.le
  have hq1 : q < 1 := (div_lt_one hr).mpr hw
  have hpos (i : ι) : 0 < ‖P i‖ := hr.trans_le (hP i)
  have hne (i : ι) : P i ≠ 0 := norm_pos_iff.mp (hpos i)
  have he (n : ℕ) (i : ι) : A n i = (w/(P i)^2)*(w/P i)^n := by
    dsimp only [A]
    rw [pow_add (P i), pow_succ w]
    field_simp [hne i] <;> ring
  have hb (n : ℕ) (i : ι) :
      ‖A n i‖ ≤ q^n * (‖w‖*(1/‖P i‖^2)) := by
    rw [he, norm_mul, norm_pow, norm_div, norm_pow, norm_div]
    have h : ‖w‖/‖P i‖ ≤ q :=
      div_le_div_of_nonneg_left (norm_nonneg _) hr (hP i)
    have hh := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (div_nonneg (norm_nonneg _) (hpos i).le) h n)
      (div_nonneg (norm_nonneg w) (pow_nonneg (hpos i).le 2))
    simpa only [div_eq_mul_inv, one_mul, mul_comm _ (q^n)] using hh
  have hG : Summable fun n : ℕ => q^n := summable_geometric_of_lt_one hq0 hq1
  have hB : Summable fun i => ‖w‖*(1/‖P i‖^2) := hs.mul_left _
  have hmaj : Summable fun x : ℕ × ι => q^x.1*(‖w‖*(1/‖P x.2‖^2)) := by
    have eqG (n : ℕ) : ‖q^n‖ = q^n := Real.norm_of_nonneg (pow_nonneg hq0 _)
    have eqB (i : ι) : ‖‖w‖*(1/‖P i‖^2)‖ = ‖w‖*(1/‖P i‖^2) :=
      Real.norm_of_nonneg (by positivity)
    exact summable_mul_of_summable_norm
      (f := fun n : ℕ => q^n) (g := fun i : ι => ‖w‖*(1/‖P i‖^2))
      (hG.congr (fun n => (eqG n).symm)) (hB.congr (fun i => (eqB i).symm))
  have hAbs : Summable fun x : ℕ × ι => ‖A x.1 x.2‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun x => hb x.1 x.2) hmaj
  have hsum : Summable (Function.uncurry A) := hAbs.of_norm
  have hinner (i : ι) : (∑' n, A n i) = w/(P i*(P i - w)) := by
    simp_rw [he, tsum_mul_left]
    rw [tsum_geometric_of_norm_lt_one]
    · have hdiff : P i - w ≠ 0 := by
        intro e
        have hp := hP i
        rw [sub_eq_zero.mp e] at hp
        exact (not_le_of_gt hw) hp
      field_simp [hne i, hdiff] <;> ring
    · rw [norm_div, div_lt_one (hpos i)]
      exact hw.trans_le (hP i)
  have hfactor (n : ℕ) : (∑' i, A n i) = (∑' i, 1/(P i)^(n+2))*w^(n+1) :=
    tsum_mul_right
  have houter : Summable (fun n => ∑' i, A n i) := hsum.prod
  have hx : (∑' n, ∑' i, A n i) = ∑' i, w/(P i*(P i-w)) := by
    rw [←hsum.tsum_comm]
    exact tsum_congr hinner
  have heq : (fun n : ℕ => ∑' i, A n i) = _ := funext hfactor
  constructor
  · have hB : Summable (fun n : ℕ => ‖∑' i, A n i‖) :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
        (fun n => norm_tsum_le_tsum_norm (hAbs.prod_factor n)) hAbs.prod
    exact hB.congr (fun n => congrArg norm (hfactor n))
  · rw [←hx, ← heq]
    exact houter.hasSum

#print axioms anchored_pole_taylor
end OpenMathResearch.LongCycleExcedances
