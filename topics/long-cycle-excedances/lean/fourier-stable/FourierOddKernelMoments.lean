import FourierOddKernelCalculus
import FourierOddPoleProduct

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Complex Real MeasureTheory Filter
open scoped Topology

set_option maxHeartbeats 2000000 in
/-- The four common-circle pole integrals in terms of the zeroth and first
absolute moments of their ordinary and squared gap weights. -/
theorem odd_kernel_moment_integrals (P t : ℤ → ℂ)
    (hP : ∀ l, (P l).im = (2*(l:ℝ)+1)*π) {R S : ℝ} (hR : 0 < R)
    (hg : ∀ l, ‖P l‖ ≠ R) (ht : ∀ l : ℤ, ‖t l‖ ≤ |2*(l:ℝ)+1| * S)
    {k : ℕ} (hk : 3 ≤ k) :
    let c := fun l => (R:ℂ)^k / (P l)^(k-1)
    let d := fun l => t l*c l
    let D := fun x => ∑' l, c l / (P l-circleMap 0 R x)
    let B := fun x => ∑' l, d l / (P l-circleMap 0 R x)
    let w := fun l => poleWeight (c l) (P l) R
    let v := fun l => squaredPoleWeight (c l) (P l) R
    (∫ x in (0:ℝ)..2*π, ‖D x*D x‖) ≤ 2*π*(∑' l, w l)^2 ∧
    (∫ x in (0:ℝ)..2*π, ‖oddKernelSlope P c R x‖) ≤ 2*π*(R*(∑' l, v l)) ∧
    (∫ x in (0:ℝ)..2*π, ‖D x*B x‖) ≤ 2*π*(S*(∑' l, w l)*(∑' l : ℤ, |2*(l:ℝ)+1| * w l)) ∧
    (∫ x in (0:ℝ)..2*π, ‖oddKernelSlope P d R x‖) ≤
      2*π*(R*S*(∑' l : ℤ, |2*(l:ℝ)+1| * v l)) := by
  intro c d D B w v
  obtain ⟨hs₀,hs₁⟩ := lattice_moment_weights P hP hR hk
  have hsd : Summable fun l => poleWeight (d l) (P l) R := by
    apply Summable.of_nonneg_of_le (fun l => div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))
      _ (hs₁.mul_right S)
    intro l
    change poleWeight (d l) (P l) R ≤ (|2*(l:ℝ)+1| * w l)*S
    have he : poleWeight (d l) (P l) R = ‖t l‖ * w l := by
      simp only [d,w,poleWeight,norm_mul,mul_div_assoc]
    rw [he]
    have hw : 0 ≤ w l := div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
    exact (mul_le_mul_of_nonneg_right (ht l) hw).trans_eq (mul_right_comm _ _ _)
  obtain ⟨_,hd₀⟩ := odd_kernel_calculus P c hP hR hg hs₀
  obtain ⟨_,hd₁⟩ := odd_kernel_calculus P d hP hR hg hsd
  have hnorm₀ (x : ℝ) : ‖deriv D x‖ = ‖oddKernelSlope P c R x‖ := by
    rw [(hd₀ x).deriv,norm_mul,norm_I,one_mul]
  have hnorm₁ (x : ℝ) : ‖deriv B x‖ = ‖oddKernelSlope P d R x‖ := by
    rw [(hd₁ x).deriv,norm_mul,norm_I,one_mul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · let e := Equiv.intEquivNat.symm
    have he : Tendsto e atTop cofinite := by
      rw [← Nat.cofinite_eq_atTop]
      exact e.injective.tendsto_cofinite
    have hfar := he.eventually (lattice_eventually_far P hP hR)
    have hg' (i : ℕ) : ‖(P ∘ e) i‖ ≠ R := hg (e i)
    have hw : Summable w := hs₀
    have h := complex_pole_product_bound (P ∘ e) (P ∘ e) (c ∘ e) (c ∘ e)
      hR hg' hg' hfar hfar (e.summable_iff.mpr hw) (e.summable_iff.mpr hw)
    have hfun (x : ℝ) : complexPoleKernel (P ∘ e) (c ∘ e) R x = D x :=
      e.tsum_eq (fun l => c l/(P l-circleMap 0 R x))
    simp_rw [hfun] at h
    change _ ≤ (2*π)*(∑' i, w (e i))*(∑' i, w (e i)) at h
    rw [e.tsum_eq w] at h
    exact h.trans_eq (by ring)
  · have h := odd_lattice_contrast_derivative P (fun _ => (1:ℂ)) hP hR hg
      (S := 1) (fun l => by simpa using odd_lattice_height_one_le l) hk
    dsimp only at h
    simp only [one_mul] at h
    change (∫ x in (0:ℝ)..2*π, ‖deriv D x‖) ≤ R*((∑' l, v l)*(2*π)) at h
    simp_rw [hnorm₀] at h
    exact h.trans_eq (by ring)
  · exact (odd_lattice_pole_product P t hP hR hg ht hk).trans_eq (by ring)
  · have h := odd_lattice_contrast_first_moment P t hP hR hg ht hk
    change (∫ x in (0:ℝ)..2*π, ‖deriv B x‖) ≤
      R*((∑' l : ℤ, |2*(l:ℝ)+1| * v l)*S*(2*π)) at h
    simp_rw [hnorm₁] at h
    exact h.trans_eq (by ring)

#print axioms odd_kernel_moment_integrals
end OpenMathResearch.LongCycleExcedances
