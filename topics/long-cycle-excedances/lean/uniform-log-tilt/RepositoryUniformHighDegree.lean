import UniformHighDegreeOddPoles
import RepositoryCoherentPoles

noncomputable section

namespace RepositoryQuotientAudit
open OpenMathResearch.LongCycleExcedances

theorem uniform_high_degree_coherent_poles (x : ℝ) {ell : ℕ} (hel : 7 ≤ ell)
    (hscale : (1:ℝ)/2 ≤ ell*(Real.pi/‖coherentPole x 0‖)^2) :
    Summable (fun l : ℤ => ‖coherentPole x 0 / coherentPole x l‖^ell) ∧
      (∑' l : ℤ, ‖coherentPole x 0 / coherentPole x l‖^ell) ≤ 13/3 := by
  simpa only [uniformTiltPole, coherentPole] using uniform_high_degree_odd_poles x hel hscale

/-- The high-degree multiplier on the inflated radius in the uniform log-tilt proof. -/
theorem uniform_high_degree_coherent_multiplier {x : ℝ} (hx : 10 ≤ x)
    {k ell : ℕ} (hell : x^2/16 < (ell:ℝ)) (hk : ell < k) :
    (1+1/(50*(k:ℝ)))^ell *
      (∑' l : ℤ, ‖coherentPole x 0 / coherentPole x l‖^ell) ≤ 650/147 := by
  have h := uniform_high_degree_scale_of_cut hx hell
  have hs : (1:ℝ)/2 ≤ ell*(Real.pi/‖coherentPole x 0‖)^2 := by
    simpa only [uniformTiltPole, coherentPole] using h.2
  exact uniform_high_degree_contour_factor hk (uniform_high_degree_coherent_poles x h.1 hs).2

theorem uniform_small_modulus_coherent_poles {x : ℝ} (hx : 0 ≤ x) (hmax : x ≤ 10)
    {ell : ℕ} (hel : 2 ≤ ell) :
    Summable (fun l : ℤ => ‖coherentPole x 0 / coherentPole x l‖^ell) ∧
      (∑' l : ℤ, ‖coherentPole x 0 / coherentPole x l‖^ell) ≤ 8 := by
  simpa only [uniformTiltPole, coherentPole] using uniform_small_modulus_odd_poles hx hmax hel

/-- The pole-sum multiplier in the bounded logarithmic interval. -/
theorem uniform_small_modulus_coherent_multiplier {x : ℝ} (hx : 0 ≤ x) (hmax : x ≤ 10)
    {k ell : ℕ} (hel : 2 ≤ ell) (hk : ell < k) :
    (1+1/(50*(k:ℝ)))^ell *
      (∑' l : ℤ, ‖coherentPole x 0 / coherentPole x l‖^ell) ≤ 9 := by
  calc
    _ ≤ (1+1/(50*(k:ℝ)))^ell * 8 :=
      mul_le_mul_of_nonneg_left (uniform_small_modulus_coherent_poles hx hmax hel).2 (by positivity)
    _ ≤ (50/49)*8 := mul_le_mul_of_nonneg_right (uniform_contour_factor hk) (by norm_num)
    _ ≤ _ := by norm_num

#print axioms uniform_high_degree_coherent_poles
#print axioms uniform_high_degree_coherent_multiplier
#print axioms uniform_small_modulus_coherent_poles
#print axioms uniform_small_modulus_coherent_multiplier
end RepositoryQuotientAudit
