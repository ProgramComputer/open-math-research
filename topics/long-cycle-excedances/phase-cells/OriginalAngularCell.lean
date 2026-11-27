import ActualPhaseDerivative
import AngularGeometry
import CellReadout
import Displacement
import Mathlib.Topology.Algebra.Polynomial

noncomputable section
namespace RepositoryQuotientAudit
open scoped Real
open Finset LongCycles OpenMathResearch.LongCycleExcedances Real

def angleRow (n k : ℕ) (θ : ℝ) : ℝ :=
  (enumerator n k).eval (-Real.exp (-angleCoordinate θ))

def angleLogTilt (k : ℕ) (θ : ℝ) : ℂ :=
  principalLogTilt k (angleCoordinate θ)

def anglePhase (n k : ℕ) (θ : ℝ) : ℝ :=
  ((n+1:ℕ):ℝ)*θ - (angleLogTilt k θ).im

private theorem angle_principal_readout {n k : ℕ} (hk : 2 ≤ k) {θ : ℝ}
    (ha : π/6 ≤ θ) (hb : θ ≤ π/2) :
    let x := angleCoordinate θ
    0 ≤ x ∧ ‖coherentPole x 0‖ ≤ 2*π ∧
    (highAnglePrincipal n k x).re / highAngleAmplitude k x = cos (anglePhase n k θ) ∧
    (highAnglePrincipal n k x).im / highAngleAmplitude k x = -sin (anglePhase n k θ) := by
  dsimp only
  obtain ⟨hx,_,hrad,_,_,hz⟩ := angular_pole_geometry ha hb
  have hw : coherentPole (angleCoordinate θ) 0 =
      (angleCoordinate θ:ℂ) + (π:ℂ)*Complex.I := by simp [coherentPole]
  have hz' : highAngleUnit (angleCoordinate θ) = Complex.exp (-(θ:ℂ)*Complex.I) := by
    unfold highAngleUnit
    rw [hw]
    exact hz
  have hval : seriesValue (coherentTilt k (-Real.exp (-angleCoordinate θ)))
      (coherentPole (angleCoordinate θ) 0) = Complex.exp (angleLogTilt k θ) :=
    seriesValue_original_coherentTilt hk _ _
  have hread := phase_readout_cis (angleLogTilt k θ) θ (n+1)
  dsimp only at hread
  rw [← hz', ← hval] at hread
  refine ⟨hx,by rw [hw]; exact hrad,?_⟩
  simpa only [Complex.div_ofReal_re, Complex.div_ofReal_im] using hread

theorem signed_original_high_angle_cell_of_displacement {n k j : ℕ} (hn : 0 < n)
    (hk : 7 ≤ k) (hsize : 100*(k:ℝ)*Real.log k ≤ n)
    (ha : π/6 ≤ (j:ℝ)*π/n) (hb : ((j+1:ℕ):ℝ)*π/n ≤ π/2)
    (hdisp : ∀ θ ∈ Set.Icc (π/6) (π/2), |(angleLogTilt k θ).im-θ| ≤ 1/2) :
    (∃ θ ∈ Set.Ioo ((j:ℝ)*π/n) (((j+1:ℕ):ℝ)*π/n), angleRow n k θ = 0) ∧
    (∀ θ ∈ Set.Icc ((j:ℝ)*π/n) (((j+1:ℕ):ℝ)*π/n),
      angleRow n k θ = 0 → 0 < (-1:ℝ)^(j+1) * angleRow (n+1) k θ) := by
  let a := (j:ℝ)*π/n
  let b := ((j+1:ℕ):ℝ)*π/n
  have hn₀ : 0 < (n:ℝ) := by exact_mod_cast hn
  have hab : a ≤ b := by
    unfold a b
    apply div_le_div_of_nonneg_right _ hn₀.le
    push_cast
    nlinarith [pi_pos]
  have region (θ : ℝ) (hθ : θ ∈ Set.Icc a b) : θ ∈ Set.Icc (π/6) (π/2) :=
    ⟨ha.trans hθ.1,hθ.2.trans hb⟩
  have sinpos (θ : ℝ) (hθ : θ ∈ Set.Icc a b) : 0 < sin θ := by
    have h := region θ hθ
    exact sin_pos_of_pos_of_lt_pi (by linarith [h.1,pi_pos]) (by linarith [h.2,pi_pos])
  let normal (θ : ℝ) : ℝ :=
    let x := angleCoordinate θ
    let t := -Real.exp (-x)
    (‖coherentPole x 0‖^(n+1)/2) /
      ((1-t)^(n+1)*n.factorial * highAngleAmplitude k x)
  have hcont : ContinuousOn (angleRow n k) (Set.Icc a b) := by
    intro y hy
    have hx : ContinuousAt angleCoordinate y := continuousAt_const.mul (continuous_cos.continuousAt.div
      continuous_sin.continuousAt (sinpos y hy).ne')
    have ht := (Real.continuous_exp.continuousAt.comp hx.neg).neg
    exact ((enumerator n k).continuous.continuousAt.comp ht).continuousWithinAt
  refine signed_grid_cell_of_row_estimates hab n j (normal := normal) (phase := anglePhase n k)
    ?_ ?_ hcont ?_ ?_ ?_ ?_
  · dsimp [a]; field_simp
  · dsimp [b]; field_simp
  · intro θ hθ
    rw [anglePhase, show ((↑(n+1:ℕ):ℝ)*θ-(angleLogTilt k θ).im-(n:ℝ)*θ) =
      -((angleLogTilt k θ).im-θ) by push_cast; ring, abs_neg]
    exact hdisp θ (region θ hθ)
  · intro θ hθ
    have hd := region θ hθ
    have hp := highAngleAmplitude_pos (by omega : 2 ≤ k) (angleCoordinate θ)
    have h := coherentPole_near_pos (angleCoordinate θ)
    have ht : 0 < 1 + Real.exp (-angleCoordinate θ) := by positivity
    dsimp only [normal]
    rw [sub_neg_eq_add]
    positivity
  · intro θ hθ
    have hd := region θ hθ
    obtain ⟨hx,hrad,hre,_⟩ := angle_principal_readout (n := n) (k := k) (by omega) hd.1 hd.2
    rw [← hre]
    have herr := actual_high_angle_normalized_error hn hk hx hrad hsize n le_rfl
    have he : normal θ * angleRow n k θ =
        highAngleRow n k (angleCoordinate θ) / highAngleAmplitude k (angleCoordinate θ) := by
      unfold normal angleRow highAngleRow
      dsimp only
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    rw [he]
    exact herr
  · intro θ hθ hold
    have hd := region θ hθ
    obtain ⟨hx,hrad,_,him⟩ := angle_principal_readout (n := n) (k := k) (by omega) hd.1 hd.2
    rw [← him, ← mul_div_assoc]
    exact div_pos (original_high_angle_next_sign hn hk hx hrad hsize hold)
      (highAngleAmplitude_pos (by omega) _)

theorem signed_original_high_angle_cell {n k j : ℕ} (hn : 0 < n)
    (hk : 7 ≤ k) (hsize : 100*(k:ℝ)*Real.log k ≤ n)
    (ha : π/6 ≤ (j:ℝ)*π/n) (hb : ((j+1:ℕ):ℝ)*π/n ≤ π/2)
    (hend : (angleLogTilt k (π/2)).im = π/2)
    (hdiff : ∀ θ ∈ Set.Icc (π/6) (π/2),
      DifferentiableAt ℝ (fun v => (angleLogTilt k v).im) θ)
    (hErr : ∀ θ ∈ Set.Icc (π/6) (π/2),
      |deriv (fun v => (angleLogTilt k v).im) θ - 1 + sin (((2*k-1:ℕ):ℝ)*θ)/sin θ| ≤
        2*(3/5:ℝ)^(k-2)/sin θ) :
    (∃ θ ∈ Set.Ioo ((j:ℝ)*π/n) (((j+1:ℕ):ℝ)*π/n), angleRow n k θ = 0) ∧
    (∀ θ ∈ Set.Icc ((j:ℝ)*π/n) (((j+1:ℕ):ℝ)*π/n),
      angleRow n k θ = 0 → 0 < (-1:ℝ)^(j+1) * angleRow (n+1) k θ) :=
  signed_original_high_angle_cell_of_displacement hn hk hsize ha hb
    (fun _ hθ => (high_angle_displacement_of_deriv hk hend hdiff hErr hθ.1 hθ.2).le)

#print axioms signed_original_high_angle_cell
end RepositoryQuotientAudit
