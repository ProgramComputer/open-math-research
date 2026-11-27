import FourierPairedRows
import FourierSelectedRadius
import FourierOriginalErrorPair
import RepositoryFourierMinorSums
import RepositoryContourCoefficient

set_option autoImplicit false
noncomputable section
namespace RepositoryQuotientAudit
open OpenMathResearch.LongCycleExcedances Finset Real LongCycles

/-- The separated circle and both normalized errors for one original row pair. -/
def WideBoundaryBounds (n k : ℕ) (s : ℝ) : Prop :=
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
      W*‖F n‖ < 1/25 ∧ W*‖((r:ℂ)/(R:ℂ))*F ((n:ℤ)+1)-(s/r:ℝ)*F n‖ < S/25

/-- Both actual minor-pole sums on every admissible contour. -/
def WideMinorBounds (n k : ℕ) (s : ℝ) : Prop :=
  ∀ {R : ℝ}, 0≤R → ∀ I : Finset ℕ,
    let p := coherentPole s 0
    let r := ‖p‖
    let w := fun i : ℕ => coherentPole s ((i+1:ℕ):ℤ)
    let T := seriesValue (coherentTilt k (-Real.exp (-s)))
    let u := fun i => (T (w i)/(‖T p‖:ℂ))*((r:ℂ)/w i)^(n+1)
    R^2 ≤ r^2*(1+2/(k:ℝ)) → 1 ≤ (n:ℝ)*(π/r)^2 → (∀ i ∈ I, ‖w i‖ ≤ R) →
    ‖∑ i ∈ I, u i‖ ≤ 1/12 ∧ ‖∑ i ∈ I, ((r:ℂ)/w i-(s/r:ℝ))*u i‖ ≤ (π/r)/4


theorem centered_rows_from_original_fourier_bounds {n k : ℕ} (hk : 2 ≤ k) {s : ℝ} (hs : 0 ≤ s)
    (hx : 48 ≤ (n:ℝ)/k) (hb : WideBoundaryBounds n k s) (hminor : WideMinorBounds n k s) :
    let p := fourierRowPole s 0
    let r := ‖p‖
    let S := π/r
    let C := s/r
    let T := contourNumerator k s
    let U := ‖T p‖
    let a := T p/(U:ℂ)*((r:ℂ)/p)^(n+1)
    let Y := fun q : ℕ => r^(q+1)/(2*U) *
      ((enumerator q k).eval (-Real.exp (-s))/((1+Real.exp (-s))^(q+1)*q.factorial))
    1 ≤ (n:ℝ)*S^2 →
    |Y n-a.re| < 37/300 ∧ |Y (n+1)-C*Y n-S*a.im| < (29/100)*S ∧
      ((enumerator n k).eval (-Real.exp (-s))=0 →
        99/100 < |a.im| ∧ 0<(enumerator (n+1) k).eval (-Real.exp (-s))*a.im) := by
  intro p r S C T U a Y hmid
  have hp : p=(s:ℂ)+(π:ℂ)*Complex.I := by simp [p,fourierRowPole]
  have him : p.im=π := by simp [p,fourierRowPole]
  have hr : 0<r := Real.pi_pos.trans_le (him ▸ (le_abs_self p.im).trans (Complex.abs_im_le_norm p))
  have hU : 0<U := by
    dsimp only [U,T,contourNumerator]
    rw [seriesValue_original_coherentTilt (by omega : 2 ≤ k),Complex.norm_exp]
    exact Real.exp_pos _
  have hN (z : ℂ) : T ((starRingEnd ℂ) z)=(starRingEnd ℂ) (T z) := by
    dsimp only [T,contourNumerator]
    rw [seriesValue_original_coherentTilt (by omega : 2 ≤ k),seriesValue_original_coherentTilt (by omega : 2 ≤ k),←Complex.exp_conj]
    simp only [map_sum,map_mul,map_pow,Complex.conj_ofReal]
  dsimp only [WideBoundaryBounds] at hb
  rw [←hp] at hb
  obtain ⟨shift,hshift,R,hR,hR2,hgap,hF,hG⟩ := hb hmid
  obtain ⟨hpr,hcap,hregular⟩ := selected_radius_geometry (by omega) hx hr hR (fourierRowPole s) hshift hR2 hgap
  obtain ⟨P,hP⟩ := finite_poles_in_circle s R
  let I := Finset.range (enclosedPositiveCount s R-1)
  have henc (i : ℕ) (hi : i ∈ I) : ‖fourierRowPole s ((i+1:ℕ):ℤ)‖ ≤ R := by
    apply le_of_lt
    apply (positive_enclosed_pole_index hpr (i+1)).mp
    change i ∈ Finset.range (enclosedPositiveCount s R-1) at hi
    have := Finset.mem_range.mp hi
    omega
  obtain ⟨hv,hv'⟩ := hminor hR.le I hcap hmid henc
  let old := (contourCoeff n k s).re
  let next := (contourCoeff (n+1) k s).re
  let F := normalizedFourierIntegral (originalFourierTrace k s R)
  let G := ((r:ℂ)/(R:ℂ))*F ((n:ℤ)+1)-(C:ℂ)*F n
  have ho := original_contour_coefficient (by omega : 2≤k) hs hR P hregular hP n
  have ha := original_contour_adjacent (by omega : 2≤k) hs hR P hregular hP n (r:ℂ) (C:ℂ)
  have h := paired_rows_from_contour n s R P T hN old next (F n) G hpr hP hU ho
    (by simpa only [Complex.ofReal_sub,Complex.ofReal_mul,Nat.cast_succ] using ha) hF hG hv hv'
  obtain ⟨h₀,h₁,hzero⟩ := h
  refine ⟨h₀,h₁,?_⟩
  intro he
  have hz : old=0 := by simp [old,contourCoeff,he]
  obtain ⟨hi,hn⟩ := hzero (by rw [hz,mul_zero])
  refine ⟨hi,?_⟩
  let v := (enumerator (n+1) k).eval (-Real.exp (-s))
  let t := (1+Real.exp (-s))^(n+2)*((n+1).factorial:ℝ)
  have ht : 0<t := by dsimp only [t]; positivity
  have hw : 0 < (r^(n+2)/(2*U))/t := by positivity
  have he' : r^(n+2)/(2*U)*next*a.im = ((r^(n+2)/(2*U))/t)*(v*a.im) := by
    dsimp only [next,contourCoeff,Complex.ofReal_re,v,t]; ring
  rw [he'] at hn
  exact pos_of_mul_pos_right hn hw.le

theorem original_wide_centered_rows {n k : ℕ} (hk : 100 ≤ k) {s : ℝ} (hs : 0 ≤ s)
    (hx : 48 ≤ (n:ℝ)/k) :
    let p := fourierRowPole s 0
    let r := ‖p‖
    let S := π/r
    let C := s/r
    let T := contourNumerator k s
    let U := ‖T p‖
    let a := T p/(U:ℂ)*((r:ℂ)/p)^(n+1)
    let Y := fun q : ℕ => r^(q+1)/(2*U) *
      ((enumerator q k).eval (-Real.exp (-s))/((1+Real.exp (-s))^(q+1)*q.factorial))
    1 ≤ (n:ℝ)*S^2 →
    |Y n-a.re| < 37/300 ∧ |Y (n+1)-C*Y n-S*a.im| < (29/100)*S ∧
      ((enumerator n k).eval (-Real.exp (-s))=0 →
        99/100 < |a.im| ∧ 0<(enumerator (n+1) k).eval (-Real.exp (-s))*a.im) := by
  apply centered_rows_from_original_fourier_bounds (by omega) hs hx
  · have hk0 : (0:ℝ)<k := by exact_mod_cast (by omega : 0<k)
    have hn : (n:ℝ)=((n:ℝ)/k)*(k:ℝ) := (div_mul_cancel₀ _ hk0.ne').symm
    have h := original_normalized_fourier_errors hk hx hn hs
    dsimp only [WideBoundaryBounds]
    intro hm
    apply h
    rw [←mul_assoc,←hn]
    exact hm
  · exact fun hR I => original_fourier_minor_sums hk hs hR I

#print axioms centered_rows_from_original_fourier_bounds
#print axioms original_wide_centered_rows
end RepositoryQuotientAudit
