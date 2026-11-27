import LongCycleBounds.InsertionBoundary
import PairedDeflatedCoefficients
import AllAspectExterior
import FrontMiddleWitnesses
import OriginalLiteralHalfRoots

set_option autoImplicit false
noncomputable section
namespace RepositoryQuotientAudit
open LongCycles LongCycleFinite LongCycleBounds.Band OpenMathResearch.LongCycleExcedances Real Set

def originalPairedRow (n k : ℕ) : ℝ → ℝ := pairedAngularRow n (normalizedEnumerator n k)

/-- Positive scale relating a literal Eulerian row to its angular representation. -/
theorem original_paired_row_factor (n k : ℕ) {z : ℝ} (hz : 0 < sin z) :
    ∃ w : ℝ, 0 < w ∧ originalPairedRow n k z =
      w*(enumerator n k).eval (-exp (-pairedAngleLog z)) := by
  let t := -exp (-pairedAngleLog z)
  let w := (pairedAngleRadius z)^n/(n.factorial:ℝ)/(1-t)^n
  have hr : 0 < pairedAngleRadius z := div_pos pi_pos hz
  have ht : 0 < 1-t := by dsimp only [t]; linarith [exp_pos (-pairedAngleLog z)]
  refine ⟨w,div_pos (div_pos (pow_pos hr n) (by positivity)) (pow_pos ht n),?_⟩
  unfold originalPairedRow pairedAngularRow normalizedEnumerator
  dsimp only [w,t]
  ring

/-- A positive finite sine comparison on the indicated middle interval gives both
complete literal root lists. This criterion requires only values of two adjacent
rows and applies for every minimum admissible cycle length. -/
theorem original_interlacing_of_paired_sine {n k : ℕ} (hn : 10000 ≤ n) (hk : 2 ≤ k)
    (hkn : k ≤ n)
    (hdot : ∀ z : ℝ, 0 < z → z ≤ π/2 → 6/5 ≤ (n:ℝ)*sin z^2 →
      0 < pairedSineDifference n z (originalPairedRow n k z) (originalPairedRow (n+1) k z)) :
    StrictNegativeInterlacing (enumerator n k).divX (enumerator (n+1) k).divX (n-2) ∧
    WeakRealInterlacing (enumerator n k) (enumerator (n+1) k) := by
  let a := exteriorIntegerSeamAngle n
  let L := uniformJoinRank n + 1
  have hnR : 0 < (n:ℝ) := Nat.cast_pos.mpr (by omega)
  obtain ⟨ha,hsmall,hbudget,_⟩ := exterior_integer_seam_geometry hn
  have hb : a ≤ π/2 := by change exteriorIntegerSeamAngle n ≤ _; linarith only [hsmall,pi_gt_three]
  have hseam : (n:ℝ)*a = (L:ℝ)*π := by
    dsimp [a,L,exteriorIntegerSeamAngle]
    push_cast
    field_simp
  have hL : L ≤ n/2 := by
    have hr : (2*(L:ℝ))*π ≤ (n:ℝ)*π := by nlinarith only [mul_le_mul_of_nonneg_left hb hnR.le,hseam]
    have hs : 2*L ≤ n := by exact_mod_cast (le_of_mul_le_mul_right hr pi_pos)
    omega
  have hs {z : ℝ} (hz : z ∈ Icc a (π/2)) : 0 < sin z :=
    sin_pos_of_pos_of_lt_pi (ha.trans_le hz.1) (hz.2.trans_lt (by linarith [pi_pos]))
  have dot {z : ℝ} (hz : z ∈ Icc a (π/2)) : 0 < pairedSineDifference n z (originalPairedRow n k z) (originalPairedRow (n+1) k z) := by
    have hzsin : sin a ≤ sin z := sin_le_sin_of_le_of_le_pi_div_two (by linarith [pi_pos,ha] : -(π/2)≤a)
      hz.2 hz.1
    have hsa : 0 < sin a := hs (left_mem_Icc.mpr hb)
    exact hdot z (ha.trans_le hz.1) hz.2 (hbudget.le.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hsa.le hzsin 2) hnR.le))
  have hsample (j : ℕ) (z : ℝ) (hz : z ∈ Icc a (π/2)) (he : (n:ℝ)*z=(j:ℝ)*π) :
      0 < (-1:ℝ)^j*(enumerator n k).eval (-pairedModulus z) := by
    have h := paired_sine_sample (hs hz) he (dot hz)
    obtain ⟨w,hw,heq⟩ := original_paired_row_factor n k (hs hz)
    rw [heq,mul_left_comm] at h
    exact pos_of_mul_pos_right h hw.le
  have hnext (j : ℕ) (z : ℝ) (hz : z ∈ Icc a (π/2)) (hl : (j:ℝ)*π < (n:ℝ)*z)
      (hu : (n:ℝ)*z < ((j:ℝ)+1)*π) (h0 : (enumerator n k).IsRoot (-pairedModulus z)) :
      0 < (-1:ℝ)^(j+1)*(enumerator (n+1) k).eval (-pairedModulus z) := by
    have hd := dot hz
    obtain ⟨w,_,hw⟩ := original_paired_row_factor n k (hs hz)
    change (enumerator n k).eval (-exp (-pairedAngleLog z))=0 at h0
    rw [hw,h0,mul_zero] at hd
    have h := paired_sine_at_root hl hu hd
    obtain ⟨w',hw',heq⟩ := original_paired_row_factor (n+1) k (hs hz)
    rw [heq,mul_left_comm] at h
    exact pos_of_mul_pos_right h hw'.le
  obtain ⟨m,hm,hroot⟩ := paired_integer_windows hL ha hb hseam
    (enumerator n k) (enumerator (n+1) k) hsample hnext
  have hmod : pairedModulus a = exp (-exteriorIntegerSeamLog n) := by
    apply congrArg (fun t : ℝ => exp (-t))
    unfold pairedAngleLog exteriorIntegerSeamLog
    rw [tan_eq_sin_div_cos]
    change π*cos a/sin a = π/(sin a/cos a)
    simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
    ring
  obtain ⟨f,hf,hfront⟩ := original_all_aspect_exterior hn hk hkn
  rw [←hmod] at hfront
  obtain ⟨u,hu,hu'⟩ := join_signed_root_moduli (n:=n) (c:=pairedModulus a) (P:=(enumerator n k).eval)
    (Q:=(enumerator (n+1) k).eval) (exp_pos _) (by
      rw [hmod]
      exact exp_le_one_iff.mpr (neg_nonpos.mpr (exterior_integer_seam_log_pos hn).le))
    f hf hfront m hm hroot
  exact original_interlacing_of_literal_half_roots hk hkn u hu hu'

#print axioms original_paired_row_factor
#print axioms original_interlacing_of_paired_sine
end RepositoryQuotientAudit
