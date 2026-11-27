import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real

/-- At a logarithmic modulus above ten the enlarged Cauchy circle satisfies
the two scale inequalities needed for the discrete Eulerian moments. -/
theorem uniform_outer_radius {x r : ℝ} {k : ℕ} (hx : 10 ≤ x) (hr : 0 ≤ r)
    (hgeom : r^2=x^2+π^2) (hk : 7 ≤ k) :
    let R := r*(1+1/(50*(k:ℝ)))
    R-x ≤ 5/x + x/(40*(k:ℝ)) ∧ R ≤ (53/50)*x := by
  have hx' : 0 < x := by linarith
  have hk' : (7:ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0:ℝ) < k := by linarith
  have hp : π^2 ≤ 10 := le_trans (pow_le_pow_left₀ pi_pos.le pi_lt_d2.le 2) (by norm_num)
  have hdx : r-x ≤ 5/x := by
    apply (le_div_iff₀ hx').2
    nlinarith only [sq_nonneg (r-x),hgeom,hp]
  have hr' : r ≤ (21/20)*x := by
    by_contra! h
    have ht : 0 ≤ x^2-100 := by nlinarith [mul_nonneg (sub_nonneg.mpr hx) (show 0≤x+10 by linarith)]
    nlinarith only [mul_pos (sub_pos.mpr h) (show 0<r+(21/20)*x by linarith),hgeom,hp,ht]
  have hc : r/(50*(k:ℝ)) ≤ x/(40*(k:ℝ)) := by
    calc
      _ ≤ ((5/4)*x)/(50*(k:ℝ)) := div_le_div_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by field_simp; ring
  have hkdiv : 1/(50*(k:ℝ)) ≤ 1/350 := by
    apply one_div_le_one_div_of_le (by norm_num)
    linarith
  dsimp only
  constructor
  · rw [mul_add, mul_one, mul_one_div]
    linarith
  · have hh := mul_le_mul hr' (add_le_add_left hkdiv 1) (by positivity)
      (show 0 ≤ (21/20)*x by positivity)
    nlinarith only [hh,hx'.le]

#print axioms uniform_outer_radius
end OpenMathResearch.LongCycleExcedances
