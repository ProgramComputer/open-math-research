import WideVerticalTransport
import PoleChord
namespace OpenMathResearch.LongCycleExcedances
open Set Real

theorem wide_log_chord_bound {k : ℕ} (hk : 100 ≤ k) {x l u : ℝ}
    (hx : 125/2 ≤ x) (hlu : l < u)
    (hseg : ∀ v ∈ Icc l u, ‖verticalArgument x v‖^(k-1) ≤ x^(k-1)*(31/10))
    (t : ℂ) (el : Complex.exp (-verticalArgument x l)=t) (eu : Complex.exp (-verticalArgument x u)=t)
    (g : ℕ → ℂ) (coeff : ∀ j ∈ Finset.range (k-1),
      HasSum (fun i : ℕ => t^(i+1)*((i+1:ℕ):ℂ)^j) (-g (j+1)*((j+1).factorial:ℂ))) :
    π*‖logPolyAt (k-1) g (verticalArgument x u)-logPolyAt (k-1) g (verticalArgument x l)‖ <
      (14/25)*(u-l) := by
  rw [log_difference_from_modes (k-1) g x l u t eu el coeff,norm_neg]
  exact (wide_vertical_transport hk hx hlu hseg).2

#print axioms wide_log_chord_bound
end OpenMathResearch.LongCycleExcedances
