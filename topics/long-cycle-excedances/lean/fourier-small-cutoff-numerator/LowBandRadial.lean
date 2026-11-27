import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open scoped BigOperators Real

private theorem sinh_secant {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Real.exp t - Real.exp (-t) ≤ (Real.exp 1 - Real.exp (-1)) * t := by
  have hD : ConvexOn ℝ (Set.Ici 0) Real.sinh := by
    apply MonotoneOn.convexOn_of_deriv (convex_Ici (0:ℝ))
      Real.differentiable_sinh.continuous.continuousOn
      Real.differentiable_sinh.differentiableOn
    rw [Real.deriv_sinh]
    apply MonotoneOn.mono _ interior_subset
    refine monotoneOn_of_deriv_nonneg (convex_Ici (0:ℝ))
      Real.differentiable_cosh.continuous.continuousOn
      Real.differentiable_cosh.differentiableOn ?_
    intro x hx
    rw [Real.deriv_cosh]
    exact Real.sinh_nonneg_iff.mpr (Set.mem_Ici.mp (interior_subset hx))
  have hs := hD.2 (show (0:ℝ) ∈ Set.Ici 0 from Set.mem_Ici.mpr le_rfl)
    (show (1:ℝ) ∈ Set.Ici 0 by norm_num) (sub_nonneg.mpr ht1) ht0
    (show 1 - t + t = 1 by ring)
  simp [smul_eq_mul, Real.sinh_eq] at hs
  linarith only [hs]

/-- Uniform difference of the two radial powers, and its sharper value
when the outer radius is the principal radius itself. -/
theorem small_band_radial_power {k j : ℕ} (hk : 10 ≤ k) (hjk : j < k) :
    (1 + 1/(k:ℝ))^j - (1 - 1/(k:ℝ))^j ≤ (5/2) * ((j:ℝ)/k) ∧
      1 - (1 - 1/(k:ℝ))^j ≤ (j:ℝ)/k := by
  let u : ℝ := 1/(k:ℝ)
  let t : ℝ := (j:ℝ)*u
  let d : ℝ := t/((k:ℝ)-1)
  have hkR : (10:ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0:ℝ) < k := by linarith
  have hk1 : 0 < (k:ℝ)-1 := by linarith
  have hu0 : 0 ≤ u := by dsimp only [u]; positivity
  have hu1 : u < 1 := by
    dsimp only [u]
    exact (div_lt_one hk0).2 (by linarith)
  have hz : 0 < 1-u := by linarith
  have hjR : (j:ℝ) < k := by exact_mod_cast hjk
  have ht0 : 0 ≤ t := by dsimp only [t]; positivity
  have ht1 : t ≤ 1 := by
    change (j:ℝ) * (1/(k:ℝ)) ≤ 1
    rw [mul_one_div]
    exact (div_le_one hk0).2 hjR.le
  have hlog : -(u/(1-u)) ≤ Real.log (1-u) := by
    have hx := Real.log_le_sub_one_of_pos (inv_pos.mpr hz)
    rw [Real.log_inv] at hx
    have h := show (1-u)⁻¹ - 1 = u/(1-u) by field_simp [ne_of_gt hz] <;> ring
    linarith only [hx,h]
  have hu : (j:ℝ) * (-(u/(1-u))) = -t-d := by
    dsimp only [u,t,d]
    field_simp [ne_of_gt hk0, ne_of_gt hk1]
    ring
  have hup : (1+u)^j ≤ Real.exp t := by
    rw [show t = (j:ℝ)*u by rfl, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by linarith) (by simpa [add_comm] using Real.add_one_le_exp u) j
  have hdown : Real.exp (-t) - d ≤ (1-u)^j := by
    have heq : Real.exp (-t-d) ≤ (1-u)^j := by
      have h := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg j)
      rw [hu] at h
      have he := Real.exp_le_exp.mpr h
      rwa [Real.exp_nat_mul, Real.exp_log hz] at he
    have hd : 0 ≤ d := by positivity
    have hx : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have happ := Real.add_one_le_exp (-d)
    have hp := mul_le_mul_of_nonneg_left happ (Real.exp_nonneg (-t))
    have hx' := mul_le_mul_of_nonneg_right hx hd
    rw [sub_eq_add_neg, Real.exp_add] at heq
    linarith only [heq,hp,hx']
  have ha : Real.exp 1 - Real.exp (-1) + 1/((k:ℝ)-1) ≤ (5/2:ℝ) := by
    have hlast : 1/((k:ℝ)-1) ≤ 1/9 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      linarith
    linarith only [hlast, Real.exp_one_lt_d9, Real.exp_neg_one_gt_d9]
  have htj : t = (j:ℝ)/k := by simp [t,u,mul_one_div]
  change (1+u)^j - (1-u)^j ≤ (5/2)*((j:ℝ)/k) ∧
    1-(1-u)^j ≤ (j:ℝ)/k
  rw [← htj]
  constructor
  · have hsec := sinh_secant ht0 ht1
    have hcost := mul_le_mul_of_nonneg_right ha ht0
    dsimp only [d] at hdown
    rw [add_mul, one_div_mul_eq_div] at hcost
    linarith only [hup,hdown,hsec,hcost]
  · by_cases hj : j = 0
    · simp [hj,t]
    have hjR' : (1:ℝ) ≤ j := by exact_mod_cast (show 1 ≤ j by omega)
    have hB := one_add_mul_self_le_rpow_one_add (s:= -u) (p:= (j:ℝ))
      (by linarith) hjR'
    rw [Real.rpow_natCast, ← sub_eq_add_neg, mul_neg] at hB
    dsimp only [t]
    nlinarith only [hB]

#print axioms small_band_radial_power
end OpenMathResearch.LongCycleExcedances
