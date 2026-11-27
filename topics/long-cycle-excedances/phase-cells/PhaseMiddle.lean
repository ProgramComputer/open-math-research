import PhasePoleGeometry

noncomputable section
namespace RepositoryQuotientAudit
open OpenMathResearch.LongCycleExcedances
open Real

theorem middle_slope_from_moment {n k : ℕ} (hk : 7 ≤ k) (hn : k ≤ n)
    (G : ℝ → ℂ) (b x : ℝ)
    (hG : HasDerivAt G ((b:ℂ) +
      (∑' l : ℤ, (1:ℂ)/(coherentPole x l)^k) * (coherentPole x 0)^(k-1)) x)
    (hmid : 1 ≤ (n:ℝ) * (π/‖coherentPole x 0‖)^2) :
    let r := ‖coherentPole x 0‖
    |deriv (fun u => ((n:ℝ)+1)*poleAngle u - (G u).im) x + n*π/r^2| <
      (32/35)*(n:ℝ)*π/r^2 := by
  let w := coherentPole x 0
  let r := ‖w‖
  let s := π/r
  let B := w^k * ∑' l : ℤ, (1:ℂ)/(coherentPole x l)^k
  have hr : 0 < r := coherentPole_near_pos x
  have hW : w ≠ 0 := norm_pos_iff.mp hr
  have hs : 0 < s := div_pos pi_pos hr
  have hwR : w.re = x := by simp [w, coherentPole, Complex.add_re, Complex.mul_I_re,
    Complex.mul_im, Complex.add_im]
  have hwI : w.im = π := by simpa [w] using coherentPole_im x 0
  have rsq : r^2=x^2+π^2 := by
    dsimp only [r]
    rw [Complex.sq_norm, Complex.normSq_apply, hwR, hwI]
    ring
  have him : (1/w).im = -s/r := by
    rw [one_div, Complex.inv_im, hwI, ← Complex.sq_norm]
    dsimp [s,r]
    ring
  have hA : -π/(x^2+π^2) = -s/r := by rw [← rsq]; dsimp [s]; ring
  have hB : B/w = (∑' l : ℤ, (1:ℂ)/(coherentPole x l)^k)*w^(k-1) := by
    unfold B
    apply (div_eq_iff hW).mpr
    rw [show k = (k-1)+1 by omega] at ⊢
    simp only [pow_succ]
    rw [show k - 1 + 1 - 1 = k - 1 by omega]
    ring
  have hGi := Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hG
  have hGim : HasDerivAt (fun u => (G u).im) (B/w).im x := by
    rw [hB]
    simpa only [Function.comp_def, Complex.imCLM_apply, Complex.add_im, Complex.ofReal_im,
      zero_add] using hGi
  have hphase : HasDerivAt (fun u => ((n:ℝ)+1)*poleAngle u - (G u).im)
      (((n:ℝ)+1)*(-π/(x^2+π^2)) - (B/w).im) x :=
    ((poleAngle_hasDerivAt x).const_mul ((n:ℝ)+1)).sub hGim
  have he := phase_slope_bound (by exact_mod_cast hk.trans hn) hr hs rfl him hmid
    (all_angle_scaled_remainder x hk)
  change |((n:ℝ)+1)*(-s/r) - (B/w).im + n*s/r| < (32/35)*(n:ℝ)*s/r at he
  change |deriv (fun u => ((n:ℝ)+1)*poleAngle u - (G u).im) x + n*π/r^2| < _
  rw [hphase.deriv, hA]
  convert he using 1 <;> dsimp only [s] <;> ring

#print axioms middle_slope_from_moment
end RepositoryQuotientAudit
