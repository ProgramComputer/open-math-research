import RepositoryCenteredRows
import ExactPhaseCell
import PolePhaseReadout
import MiddleAssembly
import AngularGeometry

set_option autoImplicit false
noncomputable section
namespace RepositoryQuotientAudit
open LongCycles OpenMathResearch.LongCycleExcedances Real Set

theorem original_middle_phase_readout {n k : ℕ} (hk : 2 ≤ k) (x : ℝ) :
    let a := highAnglePrincipal n k x / (highAngleAmplitude k x : ℂ)
    a.re=cos (principalPhaseX n k x) ∧ a.im= -sin (principalPhaseX n k x) := by
  have hw : coherentPole x 0=(x:ℂ)+(π:ℂ)*Complex.I := by simp [coherentPole]
  have hu : highAngleUnit x = Complex.exp (-(poleAngle x:ℂ)*Complex.I) := by
    unfold highAngleUnit
    rw [hw]
    exact logarithmic_principal_unit x
  have hG : seriesValue (coherentTilt k (-exp (-x))) (coherentPole x 0) =
      Complex.exp (principalLogTilt k x) := seriesValue_original_coherentTilt hk _ _
  have h := phase_readout_cis (principalLogTilt k x) (poleAngle x) (n+1)
  dsimp only at h
  rw [←hu,←hG] at h
  simpa only [highAnglePrincipal,highAngleAmplitude,principalPhaseX,Nat.cast_succ] using h

/-- Every full pair of consecutive true phase levels in the middle region
encloses an actual old root and forces the successor sign at every root there. -/
theorem original_middle_true_phase_cell {n k j : ℕ} (hn : 100 ≤ n) (hk : 7 ≤ k)
    (hkn : k ≤ n) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hm : b^2+π^2 ≤ (n:ℝ)*π^2)
    (hsize : 30*log (n:ℝ)+20 < (n:ℝ)/(200*(k:ℝ)))
    (hφa : principalPhaseX n k a = ((j+1:ℕ):ℝ)*π)
    (hφb : principalPhaseX n k b = (j:ℝ)*π) :
    (∃ x ∈ Ioo a b, (enumerator n k).eval (-exp (-x))=0) ∧
    (∀ x ∈ Ioo a b, (enumerator n k).eval (-exp (-x))=0 →
      0 < (-1:ℝ)^(j+1)*(enumerator (n+1) k).eval (-exp (-x))) := by
  let P (q : ℕ) (x : ℝ) := (enumerator q k).eval (-exp (-x))
  let N (x : ℝ) :=
    (‖coherentPole x 0‖^(n+1)/2)/((1+exp (-x))^(n+1)*n.factorial)/highAngleAmplitude k x
  have hcont : ContinuousOn (P n) (Icc a b) :=
    ((enumerator n k).continuous.comp (continuous_exp.comp continuous_neg).neg).continuousOn
  have hpos (x : ℝ) : 0 < N x := by
    have hr := coherentPole_near_pos x
    have hU := highAngleAmplitude_pos (by omega : 2 ≤ k) x
    dsimp only [N]
    positivity
  have heq (x : ℝ) : N x*P n x=nestedScaledRow n k x := by
    dsimp [N,P,nestedScaledRow]
    rw [sub_neg_eq_add]
    ring
  have hmono := (original_middle_phase_strictAnti hk hkn b hm).mono (show Icc a b ⊆ Icc 0 b from fun x hx => ⟨ha.trans hx.1,hx.2⟩)
  have mids (x : ℝ) (hx : x ∈ Icc a b) : 1 ≤ (n:ℝ)*(π/‖coherentPole x 0‖)^2 := by
    have hr := coherentPole_near_pos x
    have he : ‖coherentPole x 0‖^2=x^2+π^2 := by
      rw [Complex.sq_norm,Complex.normSq_apply]
      simp [coherentPole,Complex.add_re,Complex.add_im,Complex.mul_I_re,Complex.mul_I_im] <;> ring
    rw [div_pow,←mul_div_assoc,le_div_iff₀ (sq_pos_of_pos hr),one_mul,he]
    linarith only [hm,pow_le_pow_left₀ (ha.trans hx.1) hx.2 2]
  refine signed_true_phase_cell_anti hab j (P n) (P (n+1)) N (principalPhaseX n k)
    hcont hmono hφa hφb (fun x _ => hpos x) ?_ ?_
  · intro x hx
    have h := (original_middle_centered_rows hn hk hkn (ha.trans hx.1) (mids x hx) hsize).1
    rw [(original_middle_phase_readout (n:=n) (by omega : 2 ≤ k) x).1] at h
    rw [heq x]
    exact h.trans (by norm_num)
  · intro x hx h0
    have hxc : x ∈ Icc a b := ⟨hx.1.le,hx.2.le⟩
    have h := (original_middle_centered_rows hn hk hkn (ha.trans hxc.1) (mids x hxc) hsize).2.2 h0
    rw [(original_middle_phase_readout (n:=n) (by omega : 2 ≤ k) x).2] at h
    exact h

#print axioms original_middle_phase_readout
#print axioms original_middle_true_phase_cell
end RepositoryQuotientAudit
