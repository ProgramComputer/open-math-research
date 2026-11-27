import AngularRootSelection
import IntegerMiddleSeam
import Mathlib.Topology.Algebra.Polynomial

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Set Real Polynomial

def angularRowScale (m : ℕ) (θ : ℝ) : ℝ :=
  (π/sin θ)^m / ((1+exp (-angleCoordinate θ))^m*(m.factorial:ℝ))

theorem angularRowScale_pos (m : ℕ) {θ : ℝ} (hs : 0<sin θ) : 0<angularRowScale m θ := by
  unfold angularRowScale
  have hR : 0<π/sin θ := div_pos pi_pos hs
  positivity

theorem angular_row_normalization (m : ℕ) (P : ℝ[X]) (θ : ℝ) :
    let R := π/sin θ
    let x := -exp (-(R*cos θ))
    R^m * (P.eval x / (1-x)^m) / (m.factorial:ℝ) =
      angularRowScale m θ * P.eval (-exp (-angleCoordinate θ)) := by
  dsimp only
  have hx : π/sin θ*cos θ = angleCoordinate θ := by unfold angleCoordinate; ring
  rw [hx]
  simp only [angularRowScale,sub_neg_eq_add,div_eq_mul_inv,mul_inv_rev]
  ring

theorem angular_point_continuousOn (n j : ℕ) (hn : 10000≤n)
    (hj : uniformJoinRank n+1≤j) (hc : j+1≤n/2) :
    ContinuousOn (fun θ : ℝ => -exp (-angleCoordinate θ))
      (Icc (integerPhaseAngle n j) (integerPhaseAngle n (j+1))) := by
  intro θ hθ
  obtain ⟨hp,hh,_⟩ := integer_middle_grid_cell_geometry hn hj hc hθ
  have hs := sin_pos_of_pos_of_lt_pi hp (by linarith only [hh,pi_pos])
  have hx : ContinuousAt angleCoordinate θ := continuousAt_const.mul
    (continuous_cos.continuousAt.div continuous_sin.continuousAt hs.ne')
  exact (continuous_exp.continuousAt.comp hx.neg).neg.continuousWithinAt

/-- The middle half-root witnesses from the determinant of two polynomial
rows.  The left boundary is exactly the strict exterior cut furnished by the
coefficient estimates.  No estimate of a perturbed phase is needed. -/
theorem bounded_determinant_middle_witnesses {n k : ℕ} (hn : 10000≤n)
    (P Q : ℝ[X])
    (hD : ∀ θ : ℝ, 0<sin θ → 0≤cos θ → 6/5≤(n:ℝ)*sin θ^2 →
      let x := -exp (-angleCoordinate θ)
      0 < (k:ℝ)/sin θ*(sin ((n:ℝ)*θ+θ)*(angularRowScale n θ*P.eval x) -
        sin ((n:ℝ)*θ)*(angularRowScale (n+1) θ*Q.eval x))) :
    ∃ u : Fin (n/2-(uniformJoinRank n+1)) → ℝ, StrictMono u ∧
      ∀ i, exp (-exteriorIntegerSeamLog n)<u i ∧ u i<1 ∧ P.eval (-u i)=0 ∧
        0<(-1:ℝ)^(uniformJoinRank n+1+i.val+1)*Q.eval (-u i) := by
  have hnp : 0<n := by omega
  let μ := fun θ : ℝ => exp (-angleCoordinate θ)
  obtain ⟨hstart,_,_,hseam⟩ := integer_middle_first_sample hn
  apply ordered_angular_cell_moduli n (uniformJoinRank n) hnp
    (P:=P.eval) (Q:=Q.eval) (μ:=μ) angular_modulus_strictMonoOn (by simp [μ,angleCoordinate]) hseam.le hstart
  intro j hj hcomp
  let a := integerPhaseAngle n j
  let b := integerPhaseAngle n (j+1)
  have hab : a<b := integerPhaseAngle_strictMono hnp (Nat.lt_succ_self j)
  have geom {θ : ℝ} (hx : θ∈Icc a b) :
      0<sin θ ∧ 0≤cos θ ∧ 6/5≤(n:ℝ)*sin θ^2 := by
    obtain ⟨hp,hh,hs⟩ := integer_middle_grid_cell_geometry hn hj hcomp hx
    exact ⟨sin_pos_of_pos_of_lt_pi hp (by linarith only [hh,pi_pos]),
      cos_nonneg_of_mem_Icc ⟨by linarith only [hp,pi_pos],hh⟩,hs.le⟩
  have hcont : ContinuousOn (fun θ : ℝ => P.eval (-μ θ)) (Icc a b) :=
    P.continuous.comp_continuousOn (angular_point_continuousOn n j hn hj hcomp)
  have h := determinant_signed_cell hab hnp j hcont
    (integerPhaseAngle_level hnp j) (integerPhaseAngle_level hnp (j+1))
    (fun _ hx => (geom hx).1)
    (V:=angularRowScale n) (W:=angularRowScale (n+1)) (Q:=fun θ => Q.eval (-μ θ))
    (fun _ hx => angularRowScale_pos n (geom hx).1)
    (fun _ hx => angularRowScale_pos (n+1) (geom hx).1)
    (fun θ hx => pos_of_mul_pos_right (hD θ (geom hx).1 (geom hx).2.1 (geom hx).2.2)
      (div_nonneg (Nat.cast_nonneg k) (geom hx).1.le))
  obtain ⟨θ,hθ,hz⟩ := h.1
  exact ⟨θ,hθ,hz,h.2 θ hθ hz⟩

#print axioms angularRowScale_pos
#print axioms angular_row_normalization
#print axioms angular_point_continuousOn
#print axioms bounded_determinant_middle_witnesses
end OpenMathResearch.LongCycleExcedances
