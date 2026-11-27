import FourierOriginalAmplitude
import FourierOriginalCoefficientBounds
import FourierCoefficientSpecialization
import FourierLiteralKernelBudgets

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real RepositoryQuotientAudit

/-- The boundary contribution for the old row and the signed adjacent pair,
for the same radius and original generating function. -/
theorem original_normalized_fourier_errors {k n : ℕ} (hk : 100 ≤ k)
    {x s : ℝ} (hx : 48 ≤ x) (hn : (n:ℝ)=x*(k:ℝ)) (hs : 0 ≤ s) :
    let p := (s:ℂ)+(π:ℂ)*Complex.I
    let r := ‖p‖
    let c := min (1/25 : ℝ) (4/x)
    let T := seriesValue (coherentTilt k (-Real.exp (-s)))
    let S := π/r
    1 ≤ x*((k:ℝ)*S^2) →
    ∃ a ∈ ({2-2*c,2} : Set ℝ), ∃ R : ℝ, 0 < R ∧ R^2=r^2*(1+a/(k:ℝ)) ∧
      (∀ l : ℤ, c*r^2/(k:ℝ) ≤ |R^2-‖fourierRowPole s l‖^2|) ∧
      let F := normalizedFourierIntegral (originalFourierTrace k s R)
      let W := r/(2*‖T p‖)*(r/R)^n
      W*‖F n‖ < 1/25 ∧ W*‖((r:ℂ)/(R:ℂ))*F ((n:ℤ)+1)-(s/r:ℝ)*F n‖ < S/25 := by
  intro p r c T S hu
  have hk' : (100:ℝ) ≤ k := by exact_mod_cast hk
  have hK : (0:ℝ) < k := by linarith
  have hx0 : 0 < x := by linarith
  have hr2 : r^2 = s^2+π^2 := by
    dsimp [r,p]; rw [Complex.sq_norm,Complex.normSq_apply]; simp; ring
  have hr : 0 < r := by nlinarith [norm_nonneg p,sq_pos_of_pos Real.pi_pos]
  have hT : 0 < ‖T p‖ := by
    dsimp only [T]; rw [seriesValue_original_coherentTilt (by omega : 2 ≤ k)]
    exact norm_pos_iff.mpr (Complex.exp_ne_zero _)
  have hS : 0 < S := div_pos Real.pi_pos hr
  obtain ⟨a,ha,R,hR,hR2,hgap,hAmplitude⟩ := original_selected_circle_amplitude hk (by linarith : 44 ≤ x) hs hu
  have hgap' (l : ℤ) : c*r^2/(k:ℝ) ≤ |R^2-‖fourierRowPole s l‖^2| := hgap l
  have hc : 0 < c := lt_min (by norm_num) (by positivity)
  have hc' : c ≤ 1/25 := min_le_left _ _
  have ha' : a=2-2*c ∨ a=2 := ha
  have hlo : 48/25 ≤ a := by rcases ha' with h | h <;> linarith
  have hhi : a ≤ 2 := by rcases ha' with h | h <;> linarith
  have hRlo : r ≤ R := by
    have ha0 : 0 ≤ a/(k:ℝ) := div_nonneg (by linarith) hK.le
    nlinarith [mul_nonneg (sq_nonneg r) ha0]
  have hRhi : R ≤ (1+1/(k:ℝ))*r := by
    apply (sq_le_sq₀ hR.le (by positivity)).mp
    calc
      R^2 = r^2*(1+a/(k:ℝ)) := hR2
      _ ≤ r^2*(1+2/(k:ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg r)
        gcongr
      _ ≤ r^2*(1+2/(k:ℝ))+(r/(k:ℝ))^2 := le_add_of_nonneg_right (sq_nonneg _)
      _ = _ := by ring
  have he : (n:ℝ)/(k:ℝ)=x := by rw [hn,mul_div_cancel_right₀ _ hK.ne']
  have hg (l : ℤ) : ‖fourierRowPole s l‖ ≠ R := by
    intro he
    have hh := hgap' l
    rw [he,sub_self,abs_zero] at hh
    exact (not_lt_of_ge hh) (by positivity)
  let B := if x ≤ 100 then (457:ℝ) else (46/100)*x*Real.sqrt x
  have hB0 : 0 ≤ B := by dsimp only [B]; split <;> positivity
  have hB₁ (h : x ≤ 100) : B ≤ 457 := by simp [B,h]
  have hB₂ (h : 100 ≤ x) : B ≤ (46/100)*x*Real.sqrt x := by
    dsimp only [B]; split
    · next h' =>
      have he : x=100 := le_antisymm h' h
      have hs100 : Real.sqrt 100 = 10 := by
        nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 100),Real.sqrt_nonneg (100:ℝ)]
      rw [he,hs100]; norm_num
    · exact le_rfl
  let M := ((k:ℝ)*Real.exp (2997/100)*B)*‖T p‖/r
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hmax (y : ℝ) : ‖originalFourierTrace k s R y‖ ≤ M := by
    have hw := (norm_circleMap_zero R y).trans (abs_of_pos hR)
    obtain ⟨hm1,hm2⟩ := hAmplitude (circleMap 0 R y) hw
    have h : r*‖originalFourierTrace k s R y‖/‖T p‖ ≤ (k:ℝ)*Real.exp (2997/100)*B := by
      by_cases h : x ≤ 100
      · simpa only [B,if_pos h] using hm1 h
      · simpa only [B,if_neg h] using hm2 (le_of_not_ge h)
    exact (le_div_iff₀ hr).mpr (by linarith only [(div_le_iff₀ hT).mp h])
  have hamp : r*M/‖T p‖ ≤ (k:ℝ)*Real.exp (2997/100)*B := by
    dsimp only [M]; apply le_of_eq; field_simp
  have hdecay : (r/R)^n ≤ Real.exp (-(19/20)*x) := by
    simpa only [he] using selected_circle_decay hk' hr hR hlo hhi hR2 n
  obtain ⟨hOld,hAdj⟩ := original_fourier_bounds_of_moments (by omega : 3 ≤ k) hs hr hR hr2 hg (n:ℤ) hM hmax
  have hsize : 1 ≤ (n:ℝ)*(π/r)^2 := by
    rw [hn,mul_assoc]; exact hu
  have hcX : 1/((n:ℝ)/k) ≤ c := by
    rw [he]; apply le_min
    · exact (div_le_div_iff₀ hx0 (by norm_num)).mpr (by linarith)
    · exact div_le_div_of_nonneg_right (by norm_num) hx0.le
  obtain ⟨_,_,_,_,_,_,_,hb₀,hb₁,hv₀,hv₁,hA⟩ := literal_fourier_kernel_budgets hk
    (he ▸ hx) hr hr2 hRlo hRhi hsize hcX (fun l => by
      rw [poleGap,abs_sub_comm]; exact hgap' l)
  rw [he] at hb₀ hb₁ hv₀ hv₁ hA
  have haN : ‖(r:ℂ)/(R:ℂ)‖ ≤ 1 := by
    rw [norm_div,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
      abs_of_pos hr,abs_of_pos hR]
    exact (div_le_one hR).mpr hRlo
  refine ⟨a,ha,R,hR,hR2,hgap',?_⟩
  let F := normalizedFourierIntegral (originalFourierTrace k s R)
  let coeff := fun l => (R:ℂ)^k/(fourierRowPole s l)^(k-1)
  dsimp only
  apply normalized_fourier_pair_of_kernel_masses (k:=(k:ℤ)) (n:=(n:ℤ))
    (s₀:=∑' l : ℤ, poleWeight (coeff l) (fourierRowPole s l) R)
    (s₁:=∑' l : ℤ, |2*(l:ℝ)+1| * poleWeight (coeff l) (fourierRowPole s l) R)
    (t₀:=∑' l : ℤ, squaredPoleWeight (coeff l) (fourierRowPole s l) R)
    (t₁:=∑' l : ℤ, |2*(l:ℝ)+1| * squaredPoleWeight (coeff l) (fourierRowPole s l) R)
    (by exact_mod_cast hk) hx (by exact_mod_cast hn) F ((r:ℂ)/(R:ℂ)) _ (s/r:ℝ)
    hS hr.le hT hR.le (by exact_mod_cast hu) hdecay (by exact_mod_cast hamp) hB₁ hB₂
    (by apply tsum_nonneg; intro l; unfold poleWeight; positivity)
    (by apply tsum_nonneg; intro l; unfold poleWeight; positivity)
    (by apply tsum_nonneg; intro l; unfold squaredPoleWeight poleGap; positivity)
    (by apply tsum_nonneg; intro l; unfold squaredPoleWeight poleGap; positivity)
    (by simpa only [Int.cast_natCast] using hb₀) (by simpa only [Int.cast_natCast] using hb₁)
    (by simpa only [Int.cast_natCast] using hv₀) (by simpa only [Int.cast_natCast] using hv₁)
    hA haN
  · simpa only [Int.cast_natCast] using hOld
  · exact hAdj

#print axioms original_normalized_fourier_errors
end OpenMathResearch.LongCycleExcedances
