import FourierSelectedAmplitude
import FourierOriginalContraction
import TiltAnalyticEvaluation

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real RepositoryQuotientAudit

/-- On the comparison circle chosen for the two Fourier integrals, the
actual permutation numerator satisfies a height-uniform normalized bound. -/
theorem original_selected_circle_amplitude {k : ℕ} (hk : 100 ≤ k) {x s : ℝ}
    (hx : 44 ≤ x) (hs : 0 ≤ s) :
    let p := (s:ℂ)+(π:ℂ)*Complex.I
    let r := ‖p‖
    let c := min (1/25 : ℝ) (4/x)
    let T := seriesValue (coherentTilt k (-Real.exp (-s)))
    1 ≤ x*((k:ℝ)*(π/r)^2) →
    ∃ a ∈ ({2-2*c,2} : Set ℝ), ∃ R : ℝ, 0<R ∧ R^2=r^2*(1+a/(k:ℝ)) ∧
      ∀ w : ℂ, ‖w‖=R →
        let A := r*‖T w/(1+Complex.exp (w-s))‖ / ‖T p‖
        (x ≤ 100 → A ≤ (k:ℝ)*Real.exp (2997/100)*457) ∧
        (100 ≤ x → A ≤ (k:ℝ)*Real.exp (2997/100)*((46/100)*x*Real.sqrt x)) := by
  intro p r c T hu
  let G := numeratorLog k (fun j => (cutoffLogCoefficient k (-Real.exp (-s)) j : ℂ))
  have hT (z : ℂ) : T z = Complex.exp (G z) := seriesValue_original_coherentTilt (by omega) _ _
  have hk' : (100:ℝ) ≤ k := by exact_mod_cast hk
  obtain ⟨a,ha,R,hR,hR2,hA⟩ := selected_circle_amplitude hx hk' hs G
    hu (fun w => original_numerator_contraction_all_heights hk hs w)
  have hr : 0 < r := by
    have hp : p ≠ 0 := by
      intro he
      have h := congrArg Complex.im he
      simp [p,Real.pi_ne_zero] at h
    exact norm_pos_iff.mpr hp
  obtain ⟨hb,hl⟩ := selected_amplitude_regimes hx hk' hr hu
  refine ⟨a,ha,R,hR,hR2,?_⟩
  intro w hw
  dsimp only
  rw [hT,hT]
  have H := hA w hw
  rw [mul_assoc ((k:ℝ)*Real.exp _)] at H
  constructor
  · intro h
    exact H.trans (mul_le_mul_of_nonneg_left (hb h) (by positivity))
  · intro h
    exact H.trans (mul_le_mul_of_nonneg_left (hl h) (by positivity))

#print axioms original_selected_circle_amplitude
end OpenMathResearch.LongCycleExcedances
