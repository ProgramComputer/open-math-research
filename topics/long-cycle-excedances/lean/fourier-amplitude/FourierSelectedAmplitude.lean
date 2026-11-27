import FourierAmplitudeComparison
import FourierAmplitudeScalars
import FourierOriginalDenominators
import FourierPrincipalPeriod

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real

private theorem annular_displacement {r K : ℝ} (hr : 0 < r) (hk : 1 < K)
    (w : ℂ) (hw : r ≤ ‖w‖) (hW : ‖w‖ ≤ (1+1/K)*r) :
    let α := (1-1/K)*r/‖w‖
    ‖(α:ℂ)*w-w‖ ≤ 2*(r/K) := by
  let α := (1-1/K)*r/‖w‖
  have hK : 0 < K := by linarith
  have hW0 := hr.trans_le hw
  have hq : 0 < 1/K := by positivity
  have hα : α ≤ 1 := (div_le_one hW0).mpr (by nlinarith [mul_pos hq hr])
  have he : (α:ℂ)*w-w = (((α-1:ℝ):ℂ))*w := by push_cast; ring
  change ‖(α:ℂ)*w-w‖ ≤ _
  rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonpos (sub_nonpos.mpr hα)]
  have hv : α*‖w‖ = (1-1/K)*r := div_mul_cancel₀ _ hW0.ne'
  calc
    _ = ‖w‖-(1-1/K)*r := by linarith only [hv]
    _ ≤ (1+1/K)*r-(1-1/K)*r := sub_le_sub_right hW _
    _ = _ := by ring

/-- On a single selected circle for all angles, the logarithmic contraction
controls the normalized Fourier amplitude of the original quotient form. -/
theorem selected_circle_amplitude {x K s M : ℝ} (hx : 44 ≤ x) (hk : 100 ≤ K)
    (hs : 0 ≤ s) (G : ℂ → ℂ) :
    let p := (s:ℂ)+(π:ℂ)*Complex.I
    let r := ‖p‖
    let c := min (1/25 : ℝ) (4/x)
    1 ≤ x*(K*(π/r)^2) →
    (∀ w : ℂ, r ≤ ‖w‖ → ‖w‖ ≤ (1+1/K)*r →
      ‖G w-diskLogisticLog s ((((1-1/K)*r/‖w‖:ℝ):ℂ)*w)‖ +
      ‖G p-diskLogisticLog s (((1-1/K:ℝ):ℂ)*p)‖ ≤ M) →
    ∃ a ∈ ({2-2*c,2} : Set ℝ), ∃ R : ℝ, 0<R ∧ R^2=r^2*(1+a/K) ∧
      ∀ w : ℂ, ‖w‖=R →
        r*‖Complex.exp (G w)/(1+Complex.exp (w-s))‖/‖Complex.exp (G p)‖ ≤
          K*Real.exp M*(1+r/K)*(1+(425/98)/c) := by
  intro p r c hu hM
  have hsq : r^2=s^2+π^2 := by
    dsimp [r,p]; rw [Complex.sq_norm,Complex.normSq_apply]; simp; ring
  have hr : 0 < r := by nlinarith [norm_nonneg p,sq_pos_of_pos Real.pi_pos]
  have hx0 : 0 < x := by linarith
  have hK : 0 < K := by linarith
  have hK1 : 1 < K := by linarith
  have hc : 0 < c := lt_min (by norm_num) (by positivity)
  have hc1 : c ≤ 1/25 := min_le_left _ _
  let q := r/K
  let δ := (49/100)*(c*r/K)
  have hq : 0 < q := div_pos hr hK
  have hd : 0 < δ := by dsimp [δ]; positivity
  have hsmall := selected_gap_is_small hx hk hr hu
  have hprincipal : q/(1+q) ≤ ‖1-Complex.exp (-p/(K:ℂ))‖ :=
    principal_point_denominator (s:=s) hK1.le
  have hpd : 0 < q/(1+q) := by positivity
  obtain ⟨a,ha,R,hR,hR2,hgap⟩ := original_circle_uniform_denominators hx hk hs hr hsq hu
  have ha' : a=2-2*c ∨ a=2 := ha
  have ha0 : 0 ≤ a := by rcases ha' with h | h <;> linarith
  have ha2 : a ≤ 2 := by rcases ha' with h | h <;> linarith
  have hA0 := div_nonneg ha0 hK.le
  have hA2 := div_le_div_of_nonneg_right ha2 hK.le
  have hRlo : r ≤ R := by nlinarith [mul_nonneg (sq_nonneg r) hA0]
  have hRhi : R ≤ (1+1/K)*r := by
    have h1 := mul_le_mul_of_nonneg_left hA2 (sq_nonneg r)
    have hpos : 0 ≤ (1+1/K)*r := by positivity
    apply (sq_le_sq₀ hR.le hpos).mp
    calc
      R^2 = r^2*(1+a/K) := hR2
      _ ≤ r^2*(1+2/K) := by linarith
      _ ≤ r^2*(1+2/K)+(r/K)^2 := le_add_of_nonneg_right (sq_nonneg _)
      _ = _ := by ring
  refine ⟨a,ha,R,hR,hR2,?_⟩
  intro w hw
  have hlo : r ≤ ‖w‖ := hw ▸ hRlo
  have hhi : ‖w‖ ≤ (1+1/K)*r := hw ▸ hRhi
  let Δ := ‖(((1-1/K)*r/‖w‖:ℝ):ℂ)*w-w‖
  have hD : Δ ≤ 2*q := annular_displacement hr hK1 w hlo hhi
  have hδq : (49/100)*(c*q) = δ := by dsimp only [δ,q]; ring
  have hratio : 1+Δ*(1+δ)/δ ≤ 1+(425/98)/c := by
    have H := selected_ratio_factor hc hq hD (by simpa only [hδq] using hsmall)
    simpa only [hδq] using H
  have H := annular_amplitude_from_contraction hs hK1 hd G w (hgap w hw).1 hlo (hM w hlo hhi)
  apply H.trans
  let D := ‖1-Complex.exp (-p/(K:ℂ))‖
  change r*Real.exp M*(1+Δ*(1+δ)/δ)/D ≤ _
  calc
    _ ≤ (r*Real.exp M*(1+(425/98)/c))/(q/(1+q)) := by
      apply div_le_div₀ (by positivity) _ hpd hprincipal
      exact mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = _ := by dsimp only [q]; field_simp

#print axioms selected_circle_amplitude
end OpenMathResearch.LongCycleExcedances
