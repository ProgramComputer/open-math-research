import RepositorySparseSector
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real

/-- A cutoff-only threshold for the logarithmic inequality. -/
theorem sparse_size_log_threshold {A t : ℝ} (hA : 0 < A) (hy : 4 ≤ log A)
    (ht : log A + log (log A) + 2 ≤ t) : log (A*t)+2/3 < t := by
  let y := log A
  let v := y + log y + 2
  have hy' : 4 ≤ y := hy
  have hy0 : 0 < y := by linarith
  have ly0 := log_nonneg (show 1 ≤ y by linarith)
  have hv : v ≤ t := ht
  have ht0 : 0 < t := by dsimp [v] at hv; linarith
  have hdiv : v/y ≤ 9/4 := by
    apply (div_le_iff₀ hy0).mpr
    dsimp [v]
    linarith [log_le_sub_one_of_pos hy0]
  have hweight : 0 ≤ 1-1/y := sub_nonneg.mpr ((div_le_one hy0).mpr (by linarith))
  have hdrop : v-v/y ≤ t-t/y := by
    simpa only [mul_sub,mul_one,mul_one_div] using mul_le_mul_of_nonneg_right hv hweight
  have hlog := log_le_sub_one_of_pos (div_pos ht0 hy0)
  rw [log_div ht0.ne' hy0.ne'] at hlog
  rw [log_mul hA.ne' ht0.ne']
  change y + log t + 2/3 < t
  change y + log y + 2 - v/y ≤ _ at hdrop
  linarith only [hlog,hdrop,hdiv]

theorem sparse_sector_from_cutoff_threshold {n k : ℕ} (hk : 8 ≤ k)
    (h : 6000*(k:ℝ)*(log (6000*(k:ℝ)) + log (log (6000*(k:ℝ))) + 2) ≤ n) :
    10000 ≤ n ∧ 30*log (n:ℝ)+20 < (n:ℝ)/(200*(k:ℝ)) := by
  let A := 6000*(k:ℝ)
  have hk' : (8:ℝ) ≤ k := by exact_mod_cast hk
  have hA : 0 < A := by dsimp [A]; positivity
  have e : exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
  have e4 := pow_le_pow_left₀ (exp_pos 1).le e 4
  have h4 : exp (4:ℝ) ≤ A := by
    rw [show (4:ℝ) = (4:ℕ)*(1:ℝ) by norm_num, exp_nat_mul]
    dsimp [A]
    linarith
  have hlog : 4 ≤ log A := (le_log_iff_exp_le hA).mpr h4
  have hlog' : 0 ≤ log (log A) := log_nonneg (by linarith)
  change A*(log A + log (log A) + 2) ≤ (n:ℝ) at h
  have hT : log A + log (log A)+2 ≤ (n:ℝ)/A := (le_div_iff₀ hA).mpr (by rw [mul_comm]; exact h)
  have base := sparse_size_log_threshold hA hlog hT
  rw [show A*((n:ℝ)/A)=(n:ℝ) by field_simp] at base
  constructor
  · have hAn : 6*A ≤ n :=
      (mul_le_mul_of_nonneg_right (show 6 ≤ log A + log (log A)+2 by linarith) hA.le).trans
        ((le_div_iff₀ hA).mp hT)
    dsimp [A] at hAn
    exact_mod_cast (show (10000:ℝ) ≤ n by linarith)
  · have he : (n:ℝ)/(200*(k:ℝ)) = 30*((n:ℝ)/A) := by dsimp [A]; field_simp; ring
    rw [he]
    linarith only [base]

#print axioms sparse_size_log_threshold
#print axioms sparse_sector_from_cutoff_threshold
end OpenMathResearch.LongCycleExcedances

namespace RepositoryQuotientAudit
open LongCycles LongCycleFinite Real OpenMathResearch.LongCycleExcedances

/-- For a fixed cutoff the lower size bound can be evaluated without knowing n. -/
theorem original_sparse_interlacing_from_cutoff {n k : ℕ} (hk : 8 ≤ k)
    (h : 6000*(k:ℝ)*(log (6000*(k:ℝ)) + log (log (6000*(k:ℝ))) + 2) ≤ n) :
    StrictNegativeInterlacing (enumerator n k).divX (enumerator (n+1) k).divX (n-2) ∧
      WeakRealInterlacing (enumerator n k) (enumerator (n+1) k) := by
  obtain ⟨hn,hs⟩ := sparse_sector_from_cutoff_threshold hk h
  exact original_sparse_sector_interlacing hn hk hs

#print axioms original_sparse_interlacing_from_cutoff
end RepositoryQuotientAudit
