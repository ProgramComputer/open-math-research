import OriginalAngularCell
import AngularDerivative
import PhasePoleGeometry

noncomputable section
namespace RepositoryQuotientAudit
open Finset LongCycles OpenMathResearch.LongCycleExcedances
open scoped Real

private theorem centralPole_is_pure_imaginary (l : ℤ) :
    (starRingEnd ℂ) (coherentPole 0 l) = -coherentPole 0 l := by
  apply Complex.ext
  · simp [coherentPole, Complex.mul_re, Complex.mul_I_re, Complex.mul_im]
  · simp

private theorem oddPoleSum_center_real_zero {d : ℕ} (hd : 2 ≤ d) (ho : Odd d) :
    (LongCycleBounds.oddPoleSum d 0).re = 0 := by
  let u (l : ℤ) := (1:ℂ)/coherentPole 0 l^d
  have h (l : ℤ) : (u l).re = 0 := by
    have he : (starRingEnd ℂ) (u l) = -u l := by
      dsimp [u]
      rw [map_div₀, map_one, map_pow, centralPole_is_pure_imaginary, ho.neg_pow, div_neg]
    have hre := congrArg Complex.re he
    rw [Complex.conj_re, Complex.neg_re] at hre
    linarith
  have he := Complex.reCLM.map_tsum (summable_coherentPole_pow 0 hd)
  change (∑' l, u l).re = ∑' l, (u l).re at he
  change (∑' l, u l).re = _
  rw [he]
  simp [h]

theorem angleLogTilt_center {k : ℕ} (hk : 2 ≤ k) :
    (angleLogTilt k (π/2)).im = π/2 := by
  have hx : angleCoordinate (π/2) = 0 := by simp [angleCoordinate]
  unfold angleLogTilt principalLogTilt
  rw [hx, neg_zero, Real.exp_zero, Complex.im_sum, sum_eq_single 0]
  · have hfirst : cutoffLogCoefficient k (-1) 1 = (1:ℝ)/2 := by
      norm_num [cutoffLogCoefficient]
    have hw : coherentPole 0 0 = (π:ℂ)*Complex.I := by simp [coherentPole]
    rw [zero_add, pow_one, hfirst, hw]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, zero_add,
      Complex.mul_I_im, Complex.I_im]
    ring
  · intro j hj hj₀
    have hjk := mem_range.mp hj
    rcases Nat.even_or_odd (j+1) with hE | hO
    · let z := (cutoffLogCoefficient k (-1) (j+1):ℂ) * coherentPole 0 0^(j+1)
      have he : (starRingEnd ℂ) z = z := by
        dsimp only [z]
        rw [map_mul, Complex.conj_ofReal, map_pow, centralPole_is_pure_imaginary, hE.neg_pow]
      have hi := congrArg Complex.im he
      rw [Complex.conj_im] at hi
      change z.im = 0
      linarith
    · have hj₂ : 2 ≤ j+1 := by omega
      have hreal := oddPoleSum_center_real_zero hj₂ hO
      have hm := congrArg Complex.re (LongCycleBounds.Band.moment_poles (j+1) hj₂ 0 le_rfl)
      simp only [neg_zero, Real.exp_zero, Complex.ofReal_re, Complex.mul_re, Complex.natCast_re,
        Complex.natCast_im, zero_mul, sub_zero, hreal, mul_zero] at hm
      have hc : cutoffLogCoefficient k (-1) (j+1) = 0 := by
        simp [cutoffLogCoefficient, (by omega : j+1 ≠ 1), hj₂, (by omega : j+1 < k), hm, hj₀]
      simp [hc]
  · intro h
    exact (h (mem_range.mpr (by omega))).elim

theorem original_angular_phase_remainder {k : ℕ} (hk : 7 ≤ k) {θ : ℝ}
    (ha : π/6 ≤ θ) (hb : θ ≤ π/2)
    (hTail : let x := angleCoordinate θ; let w := coherentPole x 0
      ‖w^k*LongCycleBounds.oddPoleSum k x-1-(w/star w)^k‖ ≤ 2*(3/5:ℝ)^(k-2)) :
    DifferentiableAt ℝ (fun u => (angleLogTilt k u).im) θ ∧
    |deriv (fun u => (angleLogTilt k u).im) θ - 1 +
        Real.sin (((2*k-1:ℕ):ℝ)*θ)/Real.sin θ| ≤ 2*(3/5:ℝ)^(k-2)/Real.sin θ := by
  let x := angleCoordinate θ
  let w := coherentPole x 0
  let C := w^k * LongCycleBounds.oddPoleSum k x
  have hw : w = (x:ℂ)+(π:ℂ)*Complex.I := by simp [w,coherentPole]
  have hx := (angular_pole_geometry ha hb).1
  have hF := actual_principalLogTilt_derivative (by omega : 2 ≤ k) x hx
  have he : LongCycleBounds.oddPoleSum k x * w^(k-1) = C/w := by
    have hW : w ≠ 0 := norm_pos_iff.mp (coherentPole_near_pos x)
    dsimp only [C]
    rw [show w^k = w^(k-1)*w by rw [← pow_succ, show k-1+1=k by omega]]
    field_simp [hW] <;> ring
  change HasDerivAt (principalLogTilt k) ((logarithmCoeff eulerian 0 x:ℂ)+
    LongCycleBounds.oddPoleSum k x*w^(k-1)) x at hF
  rw [he,hw] at hF
  have hT : ‖C-1-(((x:ℂ)+(π:ℂ)*Complex.I)/star ((x:ℂ)+(π:ℂ)*Complex.I))^k‖ ≤
      2*(3/5:ℝ)^(k-2) := by rw [← hw]; exact hTail
  have h := angular_phase_remainder ha hb k hF hT
  have hc : ((2*k-1:ℕ):ℝ) = 2*(k:ℝ)-1 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    rfl
  rw [hc]
  exact h

theorem signed_original_high_angle_cell_of_pole_tail {n k j : ℕ} (hn : 0 < n)
    (hk : 7 ≤ k) (hsize : 100*(k:ℝ)*Real.log k ≤ n)
    (ha : π/6 ≤ (j:ℝ)*π/n) (hb : ((j+1:ℕ):ℝ)*π/n ≤ π/2)
    (hTail : ∀ θ ∈ Set.Icc (π/6) (π/2), let x := angleCoordinate θ
      let w := coherentPole x 0
      ‖w^k*LongCycleBounds.oddPoleSum k x-1-(w/star w)^k‖ ≤ 2*(3/5:ℝ)^(k-2)) :
    (∃ θ ∈ Set.Ioo ((j:ℝ)*π/n) (((j+1:ℕ):ℝ)*π/n), angleRow n k θ = 0) ∧
    (∀ θ ∈ Set.Icc ((j:ℝ)*π/n) (((j+1:ℕ):ℝ)*π/n),
      angleRow n k θ = 0 → 0 < (-1:ℝ)^(j+1) * angleRow (n+1) k θ) :=
  signed_original_high_angle_cell hn hk hsize ha hb (angleLogTilt_center (by omega))
    (fun θ h => (original_angular_phase_remainder hk h.1 h.2 (hTail θ h)).1)
    (fun θ h => (original_angular_phase_remainder hk h.1 h.2 (hTail θ h)).2)

/-- Each named complete high-angle cell contains a literal original-row
zero, and every old zero in that cell has the strict prescribed successor
sign. The bounds depend only on the original cutoff and the old size. -/
theorem original_high_angle_cells {n k j : ℕ} (hn : 0 < n)
    (hk : 7 ≤ k) (hsize : 100*(k:ℝ)*Real.log k ≤ n)
    (ha : π/6 ≤ (j:ℝ)*π/n) (hb : ((j+1:ℕ):ℝ)*π/n ≤ π/2) :
    (∃ θ ∈ Set.Ioo ((j:ℝ)*π/n) (((j+1:ℕ):ℝ)*π/n), angleRow n k θ = 0) ∧
    (∀ θ ∈ Set.Icc ((j:ℝ)*π/n) (((j+1:ℕ):ℝ)*π/n),
      angleRow n k θ = 0 → 0 < (-1:ℝ)^(j+1) * angleRow (n+1) k θ) := by
  apply signed_original_high_angle_cell_of_pole_tail hn hk hsize ha hb
  intro θ hθ
  let x := angleCoordinate θ
  have hw : coherentPole x 0 = (x:ℂ)+(π:ℂ)*Complex.I := by simp [coherentPole]
  have hr : ‖coherentPole x 0‖ ≤ 2*π := by
    rw [hw]
    exact (angular_pole_geometry hθ.1 hθ.2).2.2.1
  exact high_angle_scaled_far_bound x hk hr

#print axioms angleLogTilt_center
#print axioms original_angular_phase_remainder
#print axioms signed_original_high_angle_cell_of_pole_tail
#print axioms original_high_angle_cells
end RepositoryQuotientAudit
