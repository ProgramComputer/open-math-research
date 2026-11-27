import SmallCutoffCauchyPair
import FourierOriginalCoefficientBounds
import RepositorySmallCutoffNumerator
import RepositoryEightNineNumerator

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real RepositoryQuotientAudit

/-- Uniform original-row boundary errors at the finite cutoffs, including
the signed old/next combination on the same separated circle. -/
theorem original_small_normalized_fourier_errors {k n : ℕ} (hn : 10000 ≤ n)
    (hk : 8 ≤ k) (hku : k≤99) {s : ℝ} (hs : 0≤s) :
    let x := (n:ℝ)/k
    let p := (s:ℂ)+(π:ℂ)*Complex.I
    let r := ‖p‖
    let c := min (1/25:ℝ) (4/x)
    let T := seriesValue (coherentTilt k (-Real.exp (-s)))
    let S := π/r
    1≤(n:ℝ)*S^2 →
    ∃ a ∈ ({2-2*c,2}:Set ℝ), ∃ R : ℝ, 0<R ∧ R^2=r^2*(1+a/(k:ℝ)) ∧
      (∀ l : ℤ, c*r^2/(k:ℝ) ≤ |R^2-‖fourierRowPole s l‖^2|) ∧
      let F := normalizedFourierIntegral (originalFourierTrace k s R)
      let W := r/(2*‖T p‖)*(r/R)^n
      W*‖F n‖ < 1/25 ∧ W*‖((r:ℂ)/(R:ℂ))*F ((n:ℤ)+1)-(s/r:ℝ)*F n‖ < S/25 := by
  intro x p r c T S hm
  have hnr : (10000:ℝ)≤n := by exact_mod_cast hn
  have hkr : (8:ℝ)≤k := by exact_mod_cast hk
  have hkur : (k:ℝ)≤100 := by exact_mod_cast (by omega : k≤100)
  have hk0 : (0:ℝ)<k := by linarith
  have hr2 : r^2=s^2+π^2 := by
    dsimp [r,p]; rw [Complex.sq_norm,Complex.normSq_apply]; simp; ring
  have hr : 0<r := by nlinarith [norm_nonneg p,sq_pos_of_pos pi_pos]
  have hS : 0≤S := div_nonneg pi_pos.le hr.le
  have hC : |s/r|≤1 := by
    rw [abs_of_nonneg (div_nonneg hs hr.le),div_le_one hr]
    apply le_of_sq_le_sq _ hr.le
    linarith only [hr2,sq_nonneg π]
  let G := numeratorLog k (fun j => (cutoffLogCoefficient k (-Real.exp (-s)) j : ℂ))
  have hT (w : ℂ) : T w = Complex.exp (G w) := seriesValue_original_coherentTilt (by omega) _ _
  have hU : 0<‖T p‖ := by rw [hT,Complex.norm_exp]; exact exp_pos _
  obtain ⟨a,ha,hal,hah,R,hR,hR2,hrR,hhi,hgap,hreg⟩ :=
    small_cutoff_selected_circle hnr hkr hkur hr hr2 hm
  refine ⟨a,ha,R,hR,hR2,hgap,?_⟩
  let M : ℝ := if 50≤k then 32 else if 10≤k then 60 else 65
  have hcases : ((k:ℝ)≤100 ∧ M≤32) ∨ ((k:ℝ)≤50 ∧ M≤60) ∨ ((k:ℝ)≤10 ∧ M≤100) := by
    by_cases hk50 : 50≤k
    · exact Or.inl ⟨hkur, by simp [M,hk50]⟩
    · by_cases hk10 : 10≤k
      · exact Or.inr (Or.inl ⟨by exact_mod_cast (by omega : k≤50),by simp [M,hk50,hk10]⟩)
      · exact Or.inr (Or.inr ⟨by exact_mod_cast (by omega : k≤10),by norm_num [M,hk50,hk10]⟩)
  apply small_cutoff_cauchy_pair hnr hk0 hr hrR hU hC hS hm hcases
    (small_cutoff_circle_decay hkr hr hR hal hah hR2 n) (originalFourierTrace k s R)
  intro y
  let w := circleMap 0 R y
  have hw : ‖w‖=R := (norm_circleMap_zero R y).trans (abs_of_pos hR)
  have hlo : r≤‖w‖ := hw ▸ hrR
  have hhi' : ‖w‖≤(1+1/(k:ℝ))*r := hw ▸ hhi
  change r*‖T w/(1+Complex.exp (w-s))‖/‖T p‖ ≤ _
  rw [hT,hT]
  apply small_cutoff_amplitude hnr hkr hkur hs G w hw hm hrR hhi (hreg w hw)
  rw [←hw]
  by_cases hk50 : 50≤k
  · simpa only [M,if_pos hk50] using
      (original_small_cutoff_fifty_contraction hk50 (by omega) hs w hlo hhi').le
  · by_cases hk10 : 10≤k
    · simpa only [M,if_neg hk50,if_pos hk10] using
        (original_small_cutoff_ten_contraction hk10 (by omega) hs w hlo hhi').le
    · simpa only [M,if_neg hk50,if_neg hk10] using
        (original_eight_nine_contraction hk (by omega) hs w hlo hhi').le

#print axioms original_small_normalized_fourier_errors
end OpenMathResearch.LongCycleExcedances
