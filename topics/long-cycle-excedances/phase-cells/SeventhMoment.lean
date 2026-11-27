import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace OpenMathResearch.LongCycleExcedances
open Real Finset Set

noncomputable def seventhDensity (t : ℝ) := (1 / √(1+t^2))^7
noncomputable def seventhPrimitive (t : ℝ) :=
  let v := t / √(1+t^2)
  v - (2/3)*v^3 + (1/5)*v^5

theorem seventhPrimitive_deriv (t : ℝ) :
    HasDerivAt seventhPrimitive (seventhDensity t) t := by
  let u := √(1+t^2)
  have hu : 0 < u := Real.sqrt_pos.2 (by positivity)
  have hsq : u^2 = 1+t^2 := Real.sq_sqrt (by positivity)
  have ha := (hasDerivAt_const t (1:ℝ)).add ((hasDerivAt_id t).pow 2)
  have hs := (Real.hasDerivAt_sqrt (by positivity : (1+t^2)≠0)).comp t ha
  have hv : HasDerivAt (fun x : ℝ => x/√(1+x^2)) (1/u^3) t := by
    convert (hasDerivAt_id t).div hs hu.ne' using 1
    change 1/u^3 = (1*u - t*(1/(2*u)*(0+2*t^(2-1)*1)))/u^2
    field_simp [hu.ne']
    linear_combination -2*u^3 * hsq
  have hh := (hv.sub ((hv.pow 3).const_mul (2/3))).add ((hv.pow 5).const_mul (1/5))
  convert hh using 1
  change (1/u)^7 = 1/u^3 - 2/3 * (3*(t/u)^(3-1)*(1/u^3)) +
    1/5 * (5*(t/u)^(5-1)*(1/u^3))
  field_simp [hu.ne']
  linear_combination -3*u^15*(u^2-t^2+1) * hsq

theorem seventhPrimitive_le (t : ℝ) (ht : 0 ≤ t) : seventhPrimitive t ≤ 8/15 := by
  let v := t / √(1+t^2)
  have hu : 0 < √(1+t^2) := Real.sqrt_pos.2 (by positivity)
  have hv : 0 ≤ v := div_nonneg ht hu.le
  have h1 : v ≤ 1 := (div_le_one hu).mpr (Real.le_sqrt_of_sq_le (by linarith))
  have he : 8/15 - seventhPrimitive t =
      (1-v)^3 * (3*v^2+9*v+8) / 15 := by dsimp [v, seventhPrimitive]; ring
  have hv1 : 0 ≤ 1-v := sub_nonneg.mpr h1
  have hp : 0 ≤ (1-v)^3 * (3*v^2+9*v+8) / 15 := by positivity
  linarith

theorem seventhDensity_antitone : AntitoneOn seventhDensity (Set.Ici 0) := by
  intro x hx y hy hxy
  change (1 / √(1+y^2))^7 ≤ (1 / √(1+x^2))^7
  apply pow_le_pow_left₀ (by positivity)
  exact one_div_le_one_div_of_le (by positivity) (Real.sqrt_le_sqrt (by
    have := sq_le_sq' (by linarith [show 0 ≤ x from hx]) hxy
    linarith))

/-- Monotone Riemann sum with its exact elementary integral bound.
The mesh is arbitrary and the estimate is uniform in the number of terms. -/
theorem seventh_mesh_bound (h : ℝ) (hh : 0 < h) (N : ℕ) :
    h * (∑ j ∈ range N, seventhDensity (h * (j+1:ℕ))) ≤ 8/15 := by
  have step (j : ℕ) : h * seventhDensity (h * (j+1:ℕ)) ≤
      seventhPrimitive (h * (j+1:ℕ)) - seventhPrimitive (h*j) := by
    have hi : h*j < h*(j+1:ℕ) := by push_cast; linarith
    obtain ⟨c,hc,he⟩ := exists_hasDerivAt_eq_slope seventhPrimitive seventhDensity hi
      (fun z _ => (seventhPrimitive_deriv z).continuousAt.continuousWithinAt)
      (fun z _ => seventhPrimitive_deriv z)
    have hd := seventhDensity_antitone (show c ∈ Set.Ici 0 from
      (by positivity : 0 ≤ h*(j:ℝ)).trans hc.1.le)
      (show h*(j+1:ℕ) ∈ Set.Ici 0 from by simp only [Set.mem_Ici]; positivity) hc.2.le
    rw [he, le_div_iff₀ (sub_pos.mpr hi)] at hd
    convert hd using 1
    push_cast
    ring
  have accumulated (n : ℕ) : h*(∑ j ∈ range n, seventhDensity (h*(j+1:ℕ))) ≤
      seventhPrimitive (h*n) := by
    induction n with
    | zero => simp [seventhPrimitive]
    | succ n ih =>
      rw [sum_range_succ, mul_add]
      linarith [step n]
  exact (accumulated N).trans (seventhPrimitive_le _ (by positivity))

#print axioms seventh_mesh_bound
end OpenMathResearch.LongCycleExcedances

namespace OpenMathResearch.LongCycleExcedances
open Real Finset

/-- The exact odd pole geometry bounds each member of one far half-lattice.
Only the square-distance inequality is needed. -/
theorem far_term_le_density {r W s : ℝ} (hr : 0 < r) (hW : 0 < W) (hs : 0 < s)
    (k j : ℕ) (hk : 7 ≤ k)
    (geom : r^2 * (1+(2*s*(j+1:ℕ))^2) ≤ W^2) :
    (r/W)^k ≤ seventhDensity (2*s*(j+1:ℕ)) := by
  let t := 2*s*(j+1:ℕ)
  let u := √(1+t^2)
  have hsu : 0 < u := Real.sqrt_pos.mpr (by positivity)
  have hu : u^2 = 1+t^2 := Real.sq_sqrt (by positivity)
  have hu1 : 1 ≤ u := Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg t])
  have hru : r*u ≤ W := by
    apply le_of_sq_le_sq _ hW.le
    rw [mul_pow, hu]
    exact geom
  have he : r/W ≤ 1/u := (div_le_div_iff₀ hW hsu).mpr (by simpa using hru)
  calc
    _ ≤ (1/u)^k := pow_le_pow_left₀ (div_nonneg hr.le hW.le) he _
    _ ≤ (1/u)^7 := pow_le_pow_of_le_one (by positivity) ((div_le_iff₀ hsu).mpr (by simpa using hu1)) hk
    _ = _ := rfl

theorem seventh_far_summable_bound {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (W : ℕ → ℝ) (hw : ∀ j, 0 < W j) (k : ℕ) (hk : 7 ≤ k)
    (geom : ∀ j, r^2 * (1+(2*s*(j+1:ℕ))^2) ≤ (W j)^2) :
    Summable (fun j => (r / W j)^k) ∧
      2*(∑' j, (r / W j)^k) ≤ 8/(15*s) := by
  have nonneg (j : ℕ) : 0 ≤ (r/W j)^k := pow_nonneg (div_nonneg hr.le (hw j).le) k
  have sums (N : ℕ) : (∑ j ∈ range N, (r / W j)^k) ≤ (8/15)/(2*s) := by
    apply (le_div_iff₀ (by positivity : 0 < 2*s)).mpr
    rw [mul_comm]
    exact (mul_le_mul_of_nonneg_left (sum_le_sum (fun j _ =>
      far_term_le_density hr (hw j) hs k j hk (geom j))) (by positivity)).trans
      (seventh_mesh_bound _ (by positivity) N)
  have h := Real.tsum_le_of_sum_range_le nonneg sums
  refine ⟨summable_of_sum_range_le nonneg sums, ?_⟩
  calc
    _ ≤ 2*((8/15)/(2*s)) := by linarith
    _ = _ := by ring

theorem middle_derivative_error {n S e : ℝ} (hn : 7 ≤ n) (hs : 0 < S)
    (hmid : 1 ≤ n*S^2) (he : |e| ≤ 1/S + 8/(15*S^2)) :
    |e| < (32/35)*n := by
  have hn' : 0 < n := by linarith
  have hl : (21/8:ℝ)^2 < n := by linarith
  have hnS : (21/8:ℝ) < n*S := by
    have hsq : (21/8:ℝ)^2 < (n*S)^2 := by
      have hm := mul_le_mul_of_nonneg_left hmid hn'.le
      nlinarith only [hl, hm, show (n*S)^2 = n*(n*S^2) by ring]
    by_contra! bad
    exact (not_le_of_gt hsq) (pow_le_pow_left₀ (mul_nonneg hn'.le hs.le) bad 2)
  have h1 : 1/S < 8/21*n := (div_lt_iff₀ hs).mpr (by linarith)
  have h2 : 8/(15*S^2) ≤ (8/15)*n :=
    (div_le_iff₀ (by positivity : 0<15*S^2)).mpr (by linarith)
  linarith

#print axioms seventh_far_summable_bound
#print axioms middle_derivative_error
end OpenMathResearch.LongCycleExcedances
