import MiddleLevelSelection
import RepositoryMiddleCells
import OriginalAngularDerivative

set_option autoImplicit false
noncomputable section
namespace RepositoryQuotientAudit
open LongCycles OpenMathResearch.LongCycleExcedances Real Set

theorem original_principal_phase_at_zero {n k : ℕ} (hk : 2 ≤ k) :
    principalPhaseX n k 0 = (n:ℝ)*π/2 := by
  have ha : angleCoordinate (π/2) = 0 := by simp [angleCoordinate]
  have hg := angleLogTilt_center hk
  rw [angleLogTilt, ha] at hg
  unfold principalPhaseX poleAngle
  rw [zero_div, arctan_zero, sub_zero, hg]
  ring

/-- Select all complete middle cells above the join phase. The index grows
with root modulus, and every selected root has modulus greater than exp(-b). -/
theorem original_ordered_middle_roots {n k H : ℕ} (hn : 100 ≤ n) (hk : 7 ≤ k)
    (hkn : k ≤ n) {b : ℝ} (hb : 0 ≤ b) (hm : b^2+π^2 ≤ (n:ℝ)*π^2)
    (hsize : 30*log (n:ℝ)+20 < (n:ℝ)/(200*(k:ℝ)))
    (hjoin : principalPhaseX n k b < ((H+1:ℕ):ℝ)*π) :
    ∃ u : Fin (n/2-(H+1)) → ℝ, StrictMono u ∧
      ∀ i, exp (-b) < u i ∧ u i < 1 ∧
        (enumerator n k).eval (-u i) = 0 ∧
        0 < (-1:ℝ)^(H+1+i.val+1)*(enumerator (n+1) k).eval (-u i) := by
  have hcont : ContinuousOn (principalPhaseX n k) (Icc 0 b) := by
    intro x hx
    have h := actual_principalLogTilt_derivative (by omega : 2 ≤ k) x hx.1
    have hphase : ContinuousAt (principalPhaseX n k) x :=
      ((poleAngle_hasDerivAt x).continuousAt.const_mul ((n:ℝ)+1)).sub
        (Complex.continuous_im.continuousAt.comp h.continuousAt)
    exact hphase.continuousWithinAt
  have hcenter : ((n/2:ℕ):ℝ)*π ≤ principalPhaseX n k 0 := by
    rw [original_principal_phase_at_zero (by omega : 2 ≤ k)]
    have hcast : 2*((n/2:ℕ):ℝ) ≤ (n:ℝ) := by
      exact_mod_cast (show 2*(n/2) ≤ n by omega)
    nlinarith only [mul_le_mul_of_nonneg_right hcast pi_pos.le]
  have cells (j : ℕ) {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hv : v ≤ b)
      (hφu : principalPhaseX n k u = ((j+1:ℕ):ℝ)*π)
      (hφv : principalPhaseX n k v = (j:ℝ)*π) :
      ∃ x ∈ Ioo u v, (enumerator n k).eval (-exp (-x)) = 0 ∧
        0 < (-1:ℝ)^(j+1) * (enumerator (n+1) k).eval (-exp (-x)) := by
    have hv' : 0 ≤ v := hu.trans huv.le
    have hm' : v^2+π^2 ≤ (n:ℝ)*π^2 := by
      linarith only [pow_le_pow_left₀ hv' hv 2, hm]
    obtain ⟨⟨x, hx, hr⟩, hs⟩ :=
      original_middle_true_phase_cell hn hk hkn hu huv hm' hsize hφu hφv
    exact ⟨x, hx, hr, hs x hx hr⟩
  obtain ⟨z, hzmono, hz⟩ := ordered_middle_level_roots
    ((enumerator n k).eval) ((enumerator (n+1) k).eval)
    (principalPhaseX n k) hb (H+1) (n/2) hcont
    (original_middle_phase_strictAnti hk hkn b hm) hjoin hcenter cells
  refine ⟨fun i => -z i, fun _ _ h => neg_lt_neg (hzmono h), ?_⟩
  intro i
  obtain ⟨hi, hroot, hsign⟩ := hz i
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [neg_neg] using neg_lt_neg hi.2
  · simpa only [neg_neg] using neg_lt_neg hi.1
  · simpa only [neg_neg] using hroot
  · simpa only [neg_neg] using hsign

#print axioms original_principal_phase_at_zero
#print axioms original_ordered_middle_roots
end RepositoryQuotientAudit
