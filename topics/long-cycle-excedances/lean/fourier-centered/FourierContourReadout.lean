import FourierMinorSum
import FourierContourNormalization

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset

/-- Read the two real rows from the same normalized contour expansion. The
hypotheses on the complete pole sums are the finite conjugate-pair identities. -/
theorem signed_contour_readout (n : ℕ) (P : Finset ℂ) (N : ℂ → ℂ)
    (r R U C S old next : ℝ) (hS : 0 < S) (F G v v' p : ℂ) :
    let D := fun w : ℂ => (r:ℂ)/w-(C:ℂ)
    let b := fun w : ℂ => (N w/(U:ℂ))*((r:ℂ)/w)^(n+1)
    let a := b p
    let W := r/(2*U)*(r/R)^n
    let Y := r^(n+1)/(2*U)*old
    let Z := r^(n+2)/(2*U)*next
    (old:ℂ)=F/(R:ℂ)^n+∑ w ∈ P, N w/w^(n+1) →
    ((r*next-C*old:ℝ):ℂ)=G/(R:ℂ)^n+∑ w ∈ P, D w*(N w/w^(n+1)) →
    (∑ w ∈ P, b w).re/2=a.re+v.re →
    (∑ w ∈ P, D w*b w).re/2=S*a.im+v'.re →
    0 ≤ W → W*‖F‖ < 1/25 → W*‖G‖ < S/25 →
    ‖v‖ ≤ 1/12 → ‖v'‖ ≤ S/4 → ‖a‖=1 →
    |Y-a.re| < 37/300 ∧ |Z-C*Y-S*a.im| < 29/100*S ∧
      (Y=0 → 99/100 < |a.im| ∧ 0 < Z*a.im) := by
  intro D b a W Y Z ho ha hpair hpair' hW hF hG hv hv' hunit
  have hc₀ := normalize_contour_split n r R U P N (fun _ => 1) F (old:ℂ) (by simpa using ho)
  have hc₁ := normalize_contour_split n r R U P N D G ((r*next-C*old:ℝ):ℂ) ha
  dsimp only at hc₀ hc₁
  simp only [one_mul] at hc₀
  have oldeq : Y=W*F.re+(∑ w ∈ P, b w).re/2 := by
    have he := congrArg Complex.re hc₀
    simpa only [Complex.add_re, Complex.mul_re,Complex.ofReal_im,zero_mul,sub_zero, Complex.ofReal_re,Complex.div_ofNat_re] using he
  have adjeq : Z-C*Y=W*G.re+(∑ w ∈ P, D w*b w).re/2 := by
    have he := congrArg Complex.re hc₁
    rw [← normalize_adjacent_real n r U C old next]
    simpa only [Complex.add_re,Complex.mul_re,Complex.ofReal_im,zero_mul,sub_zero,Complex.ofReal_re,Complex.div_ofNat_re] using he
  have hboundary (A : ℂ) : |W*A.re| ≤ W*‖A‖ := by
    rw [abs_mul,abs_of_nonneg hW]
    exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) hW
  have hE := paired_fourier_error_margin (b:=W*F.re) (d:=W*G.re)
    (by linarith only [oldeq,hpair] : Y=a.re+v.re+W*F.re)
    (by linarith only [adjeq,hpair'] : Z-C*Y=S*a.im+v'.re+W*G.re)
    hv hv' ((hboundary F).trans_lt hF) ((hboundary G).trans_lt hG)
  refine ⟨hE.1,hE.2,?_⟩
  intro hzero
  rw [hzero,zero_sub,abs_neg] at hE
  exact paired_fourier_sign_at_zero hS hunit hE.1 (by simpa only [mul_zero,sub_zero] using hE.2)

#print axioms signed_contour_readout
end OpenMathResearch.LongCycleExcedances
