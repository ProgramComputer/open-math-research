import FourierOriginalAngularRow
import FourierOddKernelCalculus
import FourierLatticeSplit
import FourierNormComparison
import FourierPoleContrast

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Complex Real MeasureTheory
open RepositoryQuotientAudit

/-- The original permutation-row generating function on the common circle. -/
def originalFourierTrace (k : ℕ) (s R x : ℝ) : ℂ :=
  let w := circleMap 0 R x
  seriesValue (coherentTilt k (-Real.exp (-s))) w / (1 + Complex.exp (w - s))

set_option maxHeartbeats 2500000 in
/-- Both signed Fourier estimates for the actual original numerator. The
amplitude and pole integrals are explicit; the angular equations are proved. -/
theorem original_fourier_coefficient_bounds {k : ℕ} (hk : 3 ≤ k)
    {s r R : ℝ} (hs : 0 ≤ s) (hr : 0 < r) (hR : 0 < R) (hr2 : r^2 = s^2+π^2)
    (hg : ∀ l : ℤ, ‖fourierRowPole s l‖ ≠ R)
    (n : ℤ) {M U₀ V₀ U₁ V₁ : ℝ} (hM : 0 ≤ M)
    (hmax : ∀ x, ‖originalFourierTrace k s R x‖ ≤ M) :
    let f := originalFourierTrace k s R
    let P := fourierRowPole s
    let c := fun l => (R:ℂ)^k / (P l)^(k-1)
    let t := fun l => (r:ℂ)/P l-(s/r:ℝ)
    let d := fun l => t l*c l
    let D := fun x => ∑' l, c l / (P l-circleMap 0 R x)
    let B := fun x => ∑' l, d l / (P l-circleMap 0 R x)
    let E₀ := oddKernelSlope P c R
    let E₁ := oddKernelSlope P d R
    let a := (r:ℂ)/(R:ℂ)
    let A := (∑' l, ((r:ℂ)/P l)*c l)/(R:ℂ)
    (∫ x in (0:ℝ)..2*π, ‖D x*D x‖) ≤ 2*π*U₀ →
    (∫ x in (0:ℝ)..2*π, ‖E₀ x‖) ≤ 2*π*V₀ →
    (∫ x in (0:ℝ)..2*π, ‖D x*B x‖) ≤ 2*π*U₁ →
    (∫ x in (0:ℝ)..2*π, ‖E₁ x‖) ≤ 2*π*V₁ →
    (∀ j : ℤ, ‖((j-k : ℤ):ℂ)*(j:ℂ)*normalizedFourierIntegral f j‖ ≤ M*(U₀+V₀)) ∧
    ‖((n-k : ℤ):ℂ)*(n:ℂ)*(a*normalizedFourierIntegral f (n+1)-
      (s/r:ℝ)*normalizedFourierIntegral f n)‖ ≤ M*(U₁+V₁) +
        ‖((n-k : ℤ):ℂ)*A*normalizedFourierIntegral f (n+1-k)‖ +
        ‖((n-k : ℤ):ℂ)*a*normalizedFourierIntegral f (n+1)‖ := by
  intro f P c t d D B E₀ E₁ a A hu₀ hv₀ hu₁ hv₁
  have hP (l : ℤ) : (P l).im = (2*(l:ℝ)+1)*π := by
    simp [P,fourierRowPole,Complex.add_im,Complex.mul_re,Complex.add_re]
  have hf (x : ℝ) : HasDerivAt f (I*circleWave (k:ℤ) x*(f x*D x)) x := by
    have hw : circleMap 0 R x ∉ Set.range P := by
      rintro ⟨l,hl⟩
      exact hg l ((congrArg norm hl).trans ((norm_circleMap_zero R x).trans (abs_of_pos hR)))
    simpa only [f,originalFourierTrace,D,c,P,circleWave,Int.cast_natCast] using
      original_row_angular_equation (by omega : 2 ≤ k) hs R x hw
  have hT (l : ℤ) : ‖t l‖ ≤ |2*(l:ℝ)+1| * (π/r) := by
    let C := s/r
    let S := π/r
    let m := 2*(l:ℝ)+1
    let z : ℂ := ⟨C,m*S⟩
    have hCS : C^2+S^2=1 := by
      dsimp only [C,S]
      rw [div_pow,div_pow,←add_div,←hr2,div_self (pow_ne_zero _ hr.ne')]
    have he : P l = (r:ℂ)*z := by
      apply Complex.ext
      · simp [P,fourierRowPole,z,Complex.mul_re,C,hr.ne']; field_simp
      · rw [hP l]
        simp [z,Complex.mul_im,S,m]
        field_simp
    have hratio : (r:ℂ)/P l = 1/z := by
      calc
        _ = ((r:ℂ)*1)/((r:ℂ)*z) := by rw [mul_one,←he]
        _ = _ := mul_div_mul_left _ _ (Complex.ofReal_ne_zero.mpr hr.ne')
    change ‖(r:ℂ)/P l-(C:ℂ)‖ ≤ |m| * S
    rw [hratio]
    exact normalized_lattice_contrast hCS (div_nonneg Real.pi_pos.le hr.le)
      (odd_lattice_height_one_le l)
  obtain ⟨hs₀,hs₁⟩ := lattice_moment_weights P hP hR hk
  have hsD : Summable fun l => poleWeight (d l) (P l) R := by
    apply Summable.of_nonneg_of_le (fun l => div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)) _
      (hs₁.mul_right (π/r))
    intro l
    have he : poleWeight (d l) (P l) R = ‖t l‖ * poleWeight (c l) (P l) R := by
      simp only [d,poleWeight,norm_mul,mul_div_assoc]
    change poleWeight (d l) (P l) R ≤ (|2*(l:ℝ)+1| * poleWeight (c l) (P l) R)*(π/r)
    rw [he]
    have hweight : 0 ≤ poleWeight (c l) (P l) R :=
      div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
    exact (mul_le_mul_of_nonneg_right (hT l) hweight).trans_eq (mul_right_comm _ _ _)
  obtain ⟨ce₀,hd⟩ := odd_kernel_calculus P c hP hR hg hs₀
  obtain ⟨ce₁,hb⟩ := odd_kernel_calculus P d hP hR hg hsD
  have hw (x : ℝ) : circleMap 0 R x = (R:ℂ)*circleWave 1 x := by
    simp [circleMap,circleWave,mul_comm]
  have hw0 : circleMap 0 R (2*π) = circleMap 0 R 0 := by
    rw [hw,hw,circleWave_period,circleWave_zero]
  have hf0 : f (2*π) = f 0 := by dsimp only [f,originalFourierTrace]; rw [hw0]
  have hd0 : D (2*π) = D 0 := by dsimp only [D]; rw [hw0]
  have hb0 : B (2*π) = B 0 := by dsimp only [B]; rw [hw0]
  have cd : Continuous D := continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)
  have hsplit (x : ℝ) : (a*circleWave (-1) x-(s/r:ℝ))*D x =
      B x+A*circleWave (-1) x :=
    odd_lattice_contrast_split P hP (r:ℂ) (s/r:ℝ) hR hg hk x
  exact ⟨fun j => fourier_old_coefficient_bound j k hf0 hd0 ce₀ hf hd hM hmax hu₀ hv₀,
    fourier_adjacent_coefficient_bound n k a (s/r:ℝ) A hf0 hb0 cd ce₁ hf hb hsplit hM hmax hu₁ hv₁⟩

#print axioms original_fourier_coefficient_bounds
end OpenMathResearch.LongCycleExcedances
