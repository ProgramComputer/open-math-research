import PairedSineCoordinates
import LongCyclePhaseWindows
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real Set Polynomial

def pairedModulus (z : ℝ) : ℝ := exp (-pairedAngleLog z)

theorem paired_integer_windows {n L : ℕ} (hL : L ≤ n/2)
    {a : ℝ} (ha : 0 < a) (hb : a ≤ π/2) (hseam : (n:ℝ)*a = (L:ℝ)*π)
    (P Q : ℝ[X])
    (hold : ∀ j : ℕ, ∀ z ∈ Icc a (π/2), (n:ℝ)*z = (j:ℝ)*π →
      0 < (-1:ℝ)^j * P.eval (-pairedModulus z))
    (hnext : ∀ j : ℕ, ∀ z ∈ Icc a (π/2), (j:ℝ)*π < (n:ℝ)*z →
      (n:ℝ)*z < ((j:ℝ)+1)*π → P.IsRoot (-pairedModulus z) →
      0 < (-1:ℝ)^(j+1)*Q.eval (-pairedModulus z)) :
    ∃ u : Fin (n/2-L) → ℝ, StrictMono u ∧ ∀ i,
      pairedModulus a < u i ∧ u i < 1 ∧ P.IsRoot (-u i) ∧
      0 < (-1:ℝ)^(L+i.val+1)*Q.eval (-u i) := by
  have hsin {z} (hz : z ∈ Icc a (π/2)) : 0 < sin z :=
    sin_pos_of_pos_of_lt_pi (ha.trans_le hz.1) (lt_of_le_of_lt hz.2 (by linarith [pi_pos]))
  have hder {z} (hz : z ∈ Icc a (π/2)) := paired_log_derivative (hsin hz).ne'
  have hcont : ContinuousOn pairedAngleLog (Icc a (π/2)) :=
    fun _ hz => (hder hz).continuousAt.continuousWithinAt
  have hanti : StrictAntiOn pairedAngleLog (Icc a (π/2)) :=
    strictAntiOn_of_deriv_neg (convex_Icc ..) hcont (by
      intro z hz
      rw [(hder (interior_subset hz)).deriv]
      exact neg_lt_zero.mpr (div_pos pi_pos (pow_pos (hsin (interior_subset hz)) 2)))
  have hm : StrictMonoOn pairedModulus (Icc a (π/2)) :=
    fun _ hx _ hy h => exp_lt_exp.mpr (neg_lt_neg (hanti hx hy h))
  have hbv : pairedModulus (π/2) ≤ 1 := by simp [pairedModulus,pairedAngleLog]
  let level (i : Fin (n/2-L+1)) : ℝ := ((L+i.val:ℕ):ℝ)*π
  have hmono : StrictMono level := by
    intro i j hij
    apply mul_lt_mul_of_pos_right _ pi_pos
    exact_mod_cast Nat.add_lt_add_left (show i.val < j.val from hij) L
  have hend : level (Fin.last (n/2-L)) ≤ (n:ℝ)*(π/2) := by
    have hs : 2*((n/2:ℕ):ℝ) ≤ (n:ℝ) := by exact_mod_cast (show 2*(n/2) ≤ n by omega)
    dsimp [level]
    rw [show L+(n/2-L)=n/2 by omega]
    linarith only [mul_le_mul_of_nonneg_right hs pi_pos.le]
  obtain ⟨x,_,hmx,hx⟩ := singleton_windows_of_phase (offset:=L) (phase:=fun z => (n:ℝ)*z)
    (radius:=pairedModulus) (P:=P) (Q:=Q) L hb (continuous_const.mul continuous_id).continuousOn
    (continuous_exp.comp_continuousOn hcont.neg) hm hbv level hmono (by simpa [level] using hseam.le) hend
    (fun i z hz he => hold (L+i.val) z hz he) (by
      intro i z hz he hr
      apply hnext (L+i.val) z hz he.1 _ hr
      simpa only [level,Fin.val_succ, Nat.cast_add,Nat.cast_one,add_assoc] using he.2)
  exact ⟨pairedModulus ∘ x,hmx,fun i => ⟨(hx i).2.1.1,(hx i).2.1.2,(hx i).2.2.2⟩⟩

#print axioms paired_integer_windows
end OpenMathResearch.LongCycleExcedances
