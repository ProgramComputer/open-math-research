import FourierCircleChoice
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances

/-- The squared gap ensures the strict enclosure of the principal pair
and excludes every boundary pole while preserving the residue cap. -/
theorem selected_radius_geometry {k : ℕ} (hk : 100 ≤ k) {x r R a : ℝ} (hx : 48 ≤ x)
    (hr : 0 < r) (hR : 0 < R) (P : ℤ → ℂ) :
    let c := min (1/25:ℝ) (4/x)
    a ∈ ({2-2*c,2} : Set ℝ) → R^2=r^2*(1+a/(k:ℝ)) →
    (∀ l, c*r^2/(k:ℝ) ≤ |R^2-‖P l‖^2|) →
    r<R ∧ R^2 ≤ r^2*(1+2/(k:ℝ)) ∧ ∀ l, ‖P l‖ ≠ R := by
  intro c ha he hg
  have hx0 : 0<x := by linarith
  have hk0 : (0:ℝ)<k := by exact_mod_cast (by omega : 0<k)
  have hc : 0<c := lt_min (by norm_num) (by positivity)
  have hc' : c ≤ 1/25 := min_le_left _ _
  have ha' : a=2-2*c ∨ a=2 := ha
  have ha0 : 0<a := by rcases ha' with h|h <;> linarith
  have hahi : a≤2 := by rcases ha' with h|h <;> linarith
  constructor
  · apply (sq_lt_sq₀ hr.le hR.le).mp
    nlinarith only [he,mul_pos (sq_pos_of_pos hr) (div_pos ha0 hk0)]
  constructor
  · rw [he]; gcongr
  · intro l eq
    have h := hg l
    rw [eq,sub_self,abs_zero] at h
    exact (not_lt_of_ge h) (by positivity)

#print axioms selected_radius_geometry
end OpenMathResearch.LongCycleExcedances
