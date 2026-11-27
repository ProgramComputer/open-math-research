import FourierLocalPoleBounds
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Metric Set Filter
open scoped Topology

def anchoredPoleSum {ι : Type*} (P : ι → ℂ) (w : ℂ) : ℂ := ∑' i, w/(P i*(P i-w))

def inverseSquarePoleSum {ι : Type*} (P : ι → ℂ) (w : ℂ) : ℂ := ∑' i, 1/(P i-w)^2

private theorem anchored_pole_deriv {p w : ℂ} (hp : p ≠ 0) (hw : p-w ≠ 0) :
    HasDerivAt (fun z : ℂ => z/(p*(p-z))) (1/(p-w)^2) w := by
  have h := (hasDerivAt_const w p).mul ((hasDerivAt_const w p).sub (hasDerivAt_id w))
  apply ((hasDerivAt_id w).div h (mul_ne_zero hp hw)).congr_deriv
  dsimp only [id]
  field_simp [hp,hw]
  ring

/-- Local normal convergence differentiates the anchored resolvent using only
summability of inverse squared pole moduli. -/
theorem anchoredPoleSum_hasDerivAt {ι : Type*} (P : ι → ℂ) (hp : ∀ i, P i ≠ 0)
    (hs : Summable (fun i => 1/‖P i‖^2)) {U : Set ℂ} (hU : IsOpen U)
    (havoid : ∀ i, P i ∉ U) {z : ℂ} (hz : z ∈ U) :
    HasDerivAt (anchoredPoleSum P) (inverseSquarePoleSum P z) z := by
  obtain ⟨δ,M,hd,hM,hin,hbound⟩ := local_pole_ratio P hU havoid hz
  have hcenter := mem_ball_self hd (x:=z)
  have hsep i w (hw : w ∈ ball z δ) : P i-w ≠ 0 := sub_ne_zero.mpr
    (fun e => havoid i (e ▸ hin hw))
  have hnorm i := norm_pos_iff.mpr (hp i)
  have hsq (i) (w) (hw : w ∈ ball z δ) : ‖(1:ℂ)/(P i-w)^2‖ ≤ M^2*(1/‖P i‖^2) := by
    rw [norm_div,norm_one,norm_pow,←mul_div_assoc,mul_one,
      div_le_div_iff₀ (pow_pos (norm_pos_iff.mpr (hsep i w hw)) _) (pow_pos (hnorm i) _),one_mul]
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (hbound i w hw) 2
  have hstart : Summable (fun i => z/(P i*(P i-z))) := by
    apply (hs.mul_left (‖z‖*M)).of_norm_bounded
    intro i
    rw [norm_div,norm_mul,←mul_div_assoc,mul_one,
      div_le_div_iff₀ (mul_pos (hnorm i) (norm_pos_iff.mpr (hsep i z hcenter))) (pow_pos (hnorm i) _)]
    calc
      _ = (‖z‖*‖P i‖)*‖P i‖ := by ring
      _ ≤ (‖z‖*‖P i‖)*(M*‖P i-z‖) := mul_le_mul_of_nonneg_left (hbound i z hcenter) (by positivity)
      _ = _ := by ring
  exact hasDerivAt_tsum_of_isPreconnected (hs.mul_left (M^2)) isOpen_ball
    (convex_ball z δ).isPreconnected (fun i w hw => anchored_pole_deriv (hp i) (hsep i w hw))
    hsq hcenter hstart hcenter

theorem inverseSquarePoleSum_analytic {ι : Type*} (P : ι → ℂ) (hp : ∀ i, P i ≠ 0)
    (hs : Summable (fun i => 1/‖P i‖^2)) {U : Set ℂ} (hU : IsOpen U)
    (havoid : ∀ i, P i ∉ U) : AnalyticOnNhd ℂ (inverseSquarePoleSum P) U := by
  have hh (w) (hw : w ∈ U) := anchoredPoleSum_hasDerivAt P hp hs hU havoid hw
  have hc : DifferentiableOn ℂ (anchoredPoleSum P) U := fun w hw => (hh w hw).differentiableAt.differentiableWithinAt
  intro w hw
  apply ((hc.analyticOnNhd hU w hw).deriv).congr
  filter_upwards [hU.mem_nhds hw] with v hv
  exact (hh v hv).deriv

#print axioms anchoredPoleSum_hasDerivAt
#print axioms inverseSquarePoleSum_analytic
end OpenMathResearch.LongCycleExcedances
