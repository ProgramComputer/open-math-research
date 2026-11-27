import AdjacentContour
import ScalarLogisticTaylor
import FourierAnchoredLogistic
import FourierRealAxis
import TiltAnalyticEvaluation

set_option autoImplicit false
noncomputable section
namespace RepositoryQuotientAudit
open Filter Set Metric Complex Finset PowerSeries LongCycles
open LongCycleBounds LongCycleBounds.MarkedTwo
open OpenMathResearch.LongCycleExcedances
open scoped Topology NNReal Real

/-- The entire numerator of the literal common-cutoff permutation row. -/
def contourNumerator (k : ℕ) (s : ℝ) (w : ℂ) : ℂ :=
  seriesValue (coherentTilt k (-Real.exp (-s))) w

/-- The actual complex generating function on the selected contour. -/
def contourRow (k : ℕ) (s : ℝ) (w : ℂ) : ℂ :=
  contourNumerator k s w / (1+exp (w-(s:ℂ)))

/-- The exact coefficient scaling for the original enumerator. -/
def contourCoeff (n k : ℕ) (s : ℝ) : ℂ :=
  (((enumerator n k).eval (-Real.exp (-s))) /
    ((1+Real.exp (-s))^(n+1)*(n.factorial:ℝ)) : ℝ)

private theorem pi_le_row_pole_norm (s : ℝ) (l : ℤ) :
    π ≤ ‖fourierRowPole s l‖ := by
  have hc : |(2*l+1:ℤ)| ≥ 1 := by
    by_cases hn : 0 ≤ (2*l+1:ℤ)
    · rw [abs_of_nonneg hn]
      omega
    · rw [abs_of_neg (lt_of_not_ge hn)]
      omega
  have hb : |2*(l:ℝ)+1| ≥ 1 := by exact_mod_cast hc
  have hi : (fourierRowPole s l).im = (2*(l:ℝ)+1)*π := by
    simp [fourierRowPole,Complex.add_im,Complex.mul_re,Complex.add_re]
  have h := Complex.abs_im_le_norm (fourierRowPole s l)
  rw [hi, abs_mul, abs_of_pos Real.pi_pos] at h
  exact (by nlinarith only [mul_le_mul_of_nonneg_right hb Real.pi_pos.le] :
    π ≤ |2*(l:ℝ)+1| * π).trans h

theorem finite_poles_in_circle (s R : ℝ) :
    ∃ P : Finset ℂ, ∀ p : ℂ, p ∈ P ↔ p ∈ Set.range (fourierRowPole s) ∧ ‖p‖ < R := by
  classical
  obtain ⟨M,hM⟩ := exists_nat_gt (R/π+1)
  let F := (Finset.Icc (-(M:ℤ)) (M:ℤ)).filter (fun l => ‖fourierRowPole s l‖ < R)
  refine ⟨F.image (fourierRowPole s), ?_⟩
  intro p
  rw [Finset.mem_image]
  constructor
  · rintro ⟨l,hl,rfl⟩
    exact ⟨⟨l,rfl⟩,(Finset.mem_filter.mp hl).2⟩
  · rintro ⟨⟨l,rfl⟩,hp⟩
    refine ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ?_,hp⟩,rfl⟩
    have hi : (fourierRowPole s l).im = (2*(l:ℝ)+1)*π := by
      simp [fourierRowPole,Complex.add_im,Complex.mul_re,Complex.add_re]
    have h := (Complex.abs_im_le_norm (fourierRowPole s l)).trans_lt hp
    rw [hi, abs_mul, abs_of_pos Real.pi_pos] at h
    have hg : |2*(l:ℝ)+1| < R/π := (lt_div_iff₀ Real.pi_pos).mpr h
    have had := abs_lt.mp hg
    exact ⟨by exact_mod_cast (show (-(M:ℝ)) ≤ l by linarith),
      by exact_mod_cast (show (l:ℝ) ≤ M by linarith)⟩

#print axioms finite_poles_in_circle

open private logistic_coeff_pole logistic_coeff_zero from RepositoryCoherentPoles in
open private finiteTiltSummable from TiltAnalyticEvaluation in
theorem contour_original_hasSum {k : ℕ} (hk : 2 ≤ k) {s : ℝ} (hs : 0 ≤ s) :
    ∀ᶠ w in 𝓝 (0:ℂ), HasSum (fun n => contourCoeff n k s*w^n) (contourRow k s w) := by
  let t := -Real.exp (-s)
  let T := coherentTilt k t
  let L := logistic t
  let c (n : ℕ) : ℂ := ((coeff n L : ℝ) : ℂ)
  have ht0 : t ≤ 0 := neg_nonpos.mpr (Real.exp_nonneg _)
  have ht1 : -1 ≤ t := by
    dsimp [t]
    exact neg_le_neg (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs))
  have hsmall : ∀ᶠ w : ℂ in 𝓝 0, ‖w‖ < π := by
    filter_upwards [ball_mem_nhds (0:ℂ) Real.pi_pos] with w hw
    simpa [mem_ball,dist_zero_right] using hw
  filter_upwards [hsmall] with w hw
  have hc (i : ℕ) : c (i+1) = ∑' l, 1/(fourierRowPole s l)^(i+2) := by
    simpa only [c,L,t,oddPoleSum,coherentPole,fourierRowPole] using
      logistic_coeff_pole s hs (j := i+1) (Nat.succ_pos i)
  obtain ⟨hLabs,hL⟩ := scalar_logistic_taylor (fourierRowPole s) Real.pi_pos hw
    (pi_le_row_pole_norm s) (rowPole_summable s 0) c hc
  have hwavoid : w ∉ range (fourierRowPole s) := by
    rintro ⟨l,rfl⟩
    exact (not_lt_of_ge (pi_le_row_pole_norm s l)) hw
  have ha := rowPole_anchored_of_real s (fourier_squared_poles_real_axis s) hwavoid
  change (∑' i, w/(fourierRowPole s i*(fourierRowPole s i-w))) = _ at ha
  have hLval : c 0 + (∑' i, w/(fourierRowPole s i*(fourierRowPole s i-w))) =
      1/(1+exp (w-(s:ℂ))) := by
    have h0 : c 0 = 1/(1+exp (-(s:ℂ))) := by
      simp [c,L,t,logistic_coeff_zero,Complex.ofReal_div,Complex.ofReal_exp]
    rw [h0,ha]
    have hne : 1+exp (w-(s:ℂ)) ≠ 0 :=
      fun h => hwavoid ((logistic_denominator_zero_iff s w).mp h)
    have hone : 1+exp (-(s:ℂ)) ≠ 0 := by
      have h := Real.exp_pos (-s)
      rw [← Complex.ofReal_neg, ← Complex.ofReal_exp, ← Complex.ofReal_one,
        ← Complex.ofReal_add]
      exact ofReal_ne_zero.mpr (by linarith)
    field_simp [hne,hone]
    <;> ring
  rw [hLval] at hL
  let b (n : ℕ) : ℂ := ((coeff n T : ℝ) : ℂ)
  have hTabs : Summable (fun n => ‖b n*w^n‖) := by
    dsimp only [b,T]
    rw [coherentTilt_exp_finite hk]
    exact finiteTiltSummable (cutoffLogCoefficient k t) (k-1) w
  have hT : HasSum (fun n => b n*w^n) (contourNumerator k s w) :=
    hTabs.of_norm.hasSum
  have he := scalar_taylor_cauchy hT hL hTabs hLabs
  change HasSum _ (contourNumerator k s w * (1/(1+exp (w-(s:ℂ))))) at he
  have hcoeff (n : ℕ) : (∑ i ∈ Finset.antidiagonal n, b i.1*c i.2) = contourCoeff n k s := by
    have h0 := original_logistic_coefficient n k hk t ht1 ht0
    rw [coeff_mul] at h0
    simpa [contourCoeff,b,c,T,L,t,map_sum,map_mul] using congrArg Complex.ofReal h0
  simpa only [hcoeff, contourRow, mul_one_div] using he

/-- On one regular positive radius, the actual permutation coefficient is the
Fourier integral plus the signed-pole residues. The normalization is literal. -/
theorem original_contour_coefficient {k : ℕ} (hk : 2 ≤ k) {s R : ℝ}
    (hs : 0 ≤ s) (hR : 0 < R) (P : Finset ℂ)
    (hregular : ∀ l : ℤ, ‖fourierRowPole s l‖ ≠ R)
    (hP : ∀ p : ℂ, p ∈ P ↔ p ∈ range (fourierRowPole s) ∧ ‖p‖ < R)
    (n : ℕ) :
    contourCoeff n k s =
      normalizedFourierIntegral (fun x => contourRow k s (circleMap 0 R x)) n/(R:ℂ)^n
        + ∑ p ∈ P, contourNumerator k s p/p^(n+1) := by
  have hρ : 0 < min π R/2 := div_pos (lt_min Real.pi_pos hR) (by norm_num)
  let ρ : ℝ≥0 := ⟨min π R/2,hρ.le⟩
  have hρR : (ρ:ℝ) ≤ R := by
    change min π R/2 ≤ R
    linarith [min_le_right π R]
  have hρpi : (ρ:ℝ) < π := by
    change min π R/2 < π
    linarith [min_le_left π R,Real.pi_pos]
  let g (w : ℂ) := ∑ j ∈ range (k-1),
    (cutoffLogCoefficient k (-Real.exp (-s)) (j+1) : ℂ)*w^(j+1)
  have hfun : contourNumerator k s = fun w => exp (g w) := by
    funext w
    exact seriesValue_original_coherentTilt hk _ _
  have hN (z : ℂ) : AnalyticAt ℂ (contourNumerator k s) z := by
    rw [hfun]
    have hg : AnalyticAt ℂ g z := by
      first | apply (range (k-1)).analyticAt_fun_sum | apply (range (k-1)).analyticAt_sum
      intro j _
      exact analyticAt_const.mul (analyticAt_id.pow _)
    exact analyticAt_cexp.comp hg
  exact logistic_contour_coefficient (show 0 < ρ from hρ) hρR P
    (by rintro _ ⟨l,rfl⟩; exact hρpi.trans_le (pi_le_row_pole_norm s l))
    (by rintro _ ⟨l,rfl⟩; exact hregular l) hP hN _ (contour_original_hasSum hk hs) n

/-- The actual same-radius signed adjacent coefficient identity. Both row
coefficients are evaluated at the same negative real parameter. -/
theorem original_contour_adjacent {k : ℕ} (hk : 2 ≤ k) {s R : ℝ}
    (hs : 0 ≤ s) (hR : 0 < R) (P : Finset ℂ)
    (hregular : ∀ l : ℤ, ‖fourierRowPole s l‖ ≠ R)
    (hP : ∀ p : ℂ, p ∈ P ↔ p ∈ range (fourierRowPole s) ∧ ‖p‖ < R)
    (n : ℕ) (r C : ℂ) :
    let f (i : ℕ) := normalizedFourierIntegral (fun x => contourRow k s (circleMap 0 R x)) i
    r*contourCoeff (n+1) k s-C*contourCoeff n k s =
      ((r/(R:ℂ))*f (n+1)-C*f n)/(R:ℂ)^n +
        ∑ p ∈ P, (r/p-C)*(contourNumerator k s p/p^(n+1)) := by
  intro f
  have hn (p : ℂ) (hp : p ∈ P) : p ≠ 0 := by
    obtain ⟨l, rfl⟩ := ((hP p).mp hp).1
    exact norm_pos_iff.mp (Real.pi_pos.trans_le (pi_le_row_pole_norm s l))
  apply adjacent_contour_split P (contourNumerator k s) n
    (Complex.ofReal_ne_zero.mpr hR.ne') hn
  · exact original_contour_coefficient hk hs hR P hregular hP n
  · exact original_contour_coefficient hk hs hR P hregular hP (n+1)

#print axioms original_contour_adjacent
#print axioms contour_original_hasSum
#print axioms original_contour_coefficient
end RepositoryQuotientAudit
