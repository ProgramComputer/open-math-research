import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset

/-- The previous-row cosine and the centered next-row sine follow from
one shared set of poles. The weighted minor bound suppresses every minor
displacement by the scale of the principal rotation. -/
theorem centered_pole_readout {ι : Type*} (s : Finset ι)
    {Y₀ Y₁ c S δ : ℝ} (hS : 0 < S) (hc : |c| ≤ 1)
    (hδ : δ ≤ S/50) (hδ' : δ ≤ 1/20)
    (a : ℂ) (ha : ‖a‖ = 1) (b z : ι → ℂ) (p : ι → ℝ)
    (hp : ∀ i ∈ s, 1 ≤ p i) (hminor : (∑ i ∈ s, p i*‖b i‖) ≤ 1/5)
    (hdisp : ∀ i ∈ s, ‖z i-(c:ℂ)‖ ≤ p i*S)
    (h₀ : |Y₀ - (a.re+∑ i ∈ s, (b i).re)| ≤ δ)
    (h₁ : |Y₁ - (c*a.re+S*a.im+∑ i ∈ s, (b i*z i).re)| ≤ δ) :
    |Y₀-a.re| ≤ 1/4 ∧ |Y₁-c*Y₀-S*a.im| ≤ S/4 ∧
      (Y₀ = 0 → 0 < Y₁*a.im) := by
  let E₀ := Y₀ - (a.re+∑ i ∈ s, (b i).re)
  let E₁ := Y₁ - (c*a.re+S*a.im+∑ i ∈ s, (b i*z i).re)
  have hminorRe : |∑ i ∈ s, (b i).re| ≤ 1/5 := by
    apply (abs_sum_le_sum_abs _ _).trans
    apply le_trans _ hminor
    apply sum_le_sum
    intro i hi
    exact (Complex.abs_re_le_norm _).trans
      (by simpa using mul_le_mul_of_nonneg_right (hp i hi) (norm_nonneg (b i)))
  have hold : |Y₀-a.re| ≤ 1/4 := by
    have he : Y₀-a.re = E₀ + ∑ i ∈ s, (b i).re := by dsimp [E₀]; ring
    rw [he]
    exact (abs_add_le _ _).trans (by
      have h : |E₀| ≤ δ := h₀
      linarith only [h,hminorRe,hδ'])
  have hshift : |∑ i ∈ s, (b i*(z i-(c:ℂ))).re| ≤ S/5 := by
    apply (abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ i ∈ s, (p i*‖b i‖)*S := by
        apply sum_le_sum
        intro i hi
        apply (Complex.abs_re_le_norm _).trans
        rw [norm_mul]
        have h := mul_le_mul_of_nonneg_left (hdisp i hi) (norm_nonneg (b i))
        simpa only [mul_assoc,mul_comm,mul_left_comm] using h
      _ = (∑ i ∈ s, p i*‖b i‖)*S := by rw [sum_mul]
      _ ≤ _ := by simpa [div_eq_mul_inv,mul_comm] using mul_le_mul_of_nonneg_right hminor hS.le
  have he : Y₁-c*Y₀-S*a.im = E₁-c*E₀+∑ i ∈ s, (b i*(z i-(c:ℂ))).re := by
    have heq : (∑ i ∈ s, (b i*(z i-(c:ℂ))).re) =
        ∑ i ∈ s, ((b i*z i).re - c*(b i).re) := by
      apply sum_congr rfl
      intro i _
      simp only [mul_sub,Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
      ring
    rw [heq,sum_sub_distrib,←mul_sum]
    dsimp [E₀,E₁]
    ring
  have hnew : |Y₁-c*Y₀-S*a.im| ≤ S/4 := by
    rw [he]
    have hE : |E₁-c*E₀| ≤ 2*δ := by
      have h₀' : |E₀| ≤ δ := h₀
      have h₁' : |E₁| ≤ δ := h₁
      have hprod : |c*E₀| ≤ δ := by
        rw [abs_mul]
        exact (mul_le_of_le_one_left (abs_nonneg _) hc).trans h₀'
      have hs : |E₁-c*E₀| ≤ |E₁|+|c*E₀| := by
        simpa only [sub_eq_add_neg,abs_neg] using abs_add_le E₁ (-(c*E₀))
      linarith only [hs,h₁',hprod]
    exact (abs_add_le _ _).trans (by linarith only [hE,hshift,hδ,hS])
  refine ⟨hold,hnew,?_⟩
  intro hzero
  rw [hzero,zero_sub,abs_neg] at hold
  rw [hzero,mul_zero,sub_zero] at hnew
  have hnorm := Complex.sq_norm a
  rw [ha, Complex.normSq_apply] at hnorm
  have hre := pow_le_pow_left₀ (abs_nonneg a.re) hold 2
  rw [sq_abs] at hre
  have him : (2:ℝ)/3 < |a.im| := by
    apply lt_of_not_ge
    intro h
    have hi := pow_le_pow_left₀ (abs_nonneg a.im) h 2
    rw [sq_abs] at hi
    nlinarith only [hnorm,hre,hi]
  rcases lt_or_ge 0 a.im with hi | hi
  · rw [abs_of_pos hi] at him
    have h := mul_lt_mul_of_pos_left him hS
    exact mul_pos (by linarith only [h,hS,(abs_le.mp hnew).1]) hi
  · rw [abs_of_nonpos hi] at him
    have h := mul_lt_mul_of_pos_left him hS
    exact mul_pos_of_neg_of_neg (by linarith only [h,hS,(abs_le.mp hnew).2])
      (by linarith only [him])

#print axioms centered_pole_readout
end OpenMathResearch.LongCycleExcedances
