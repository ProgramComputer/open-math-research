import RepositoryWidePhaseTransfer
import RepositoryMiddleLevelSelection
import RepositoryJoinAngle
import FourierPhaseEntrance
import AllAspectExterior
import OriginalLiteralHalfRoots
import FrontMiddleWitnesses
import FrontModulusJoin

set_option autoImplicit false
noncomputable section
namespace RepositoryQuotientAudit
open OpenMathResearch.LongCycleExcedances LongCycles Real Set
open LongCycleBounds LongCycleFinite

/-- Above the bounded-aspect seam the actual consecutive original quotients
are strictly interlacing; adjoining the common simple zero gives weak
interlacing of the original permutation enumerators. -/
theorem original_wide_aspect_interlacing_of_centered {n k : ℕ} (hn : 10000 ≤ n) (hk : 8 ≤ k)
    (hratio : 48*k ≤ n) (hcentered : WideCenteredRows n k) :
    StrictNegativeInterlacing (enumerator n k).divX (enumerator (n+1) k).divX (n-2) ∧
    WeakRealInterlacing (enumerator n k) (enumerator (n+1) k) := by
  let H := uniformJoinRank n
  let b := uniformJoinLog n
  have hk₂ : 2 ≤ k := by omega
  have hk₇ : 7 ≤ k := by omega
  have hkn : k≤n := by omega
  have hb : 0≤b := (by positivity : 0 ≤ 2*sqrt (n:ℝ)).trans (uniform_join_geometry hn).2.2.2.1.le
  have hm := (uniform_join_radius_sq hn).le
  have hjoin : principalPhaseX n k b < ((H:ℝ)+1)*π := by
    have ht := wide_join_cutoff_separation hn (by omega : 25*k≤n)
    have him := principalLogTilt_im_bound hk₇ ht.le
    rw [principalPhaseX,show poleAngle b=uniformJoinAngle n from poleAngle_uniform_join hn]
    exact uniform_join_phase_from_imag hn him
  have hcenter : ((n/2:ℕ):ℝ)*π ≤ principalPhaseX n k 0 := by
    rw [original_principal_phase_at_zero hk₂]
    have hz : 2*((n/2:ℕ):ℝ)≤n := by exact_mod_cast (show 2*(n/2)≤n by omega)
    nlinarith only [mul_le_mul_of_nonneg_right hz pi_pos.le]
  have hcont : ContinuousOn (principalPhaseX n k) (Icc 0 b) := by
    intro x hx
    have h := actual_principalLogTilt_derivative hk₂ x hx.1
    have hphase : ContinuousAt (principalPhaseX n k) x :=
      ((poleAngle_hasDerivAt x).continuousAt.const_mul ((n:ℝ)+1)).sub
        (Complex.continuous_im.continuousAt.comp h.continuousAt)
    exact hphase.continuousWithinAt
  have cells (j : ℕ) {u v : ℝ} (hu : 0≤u) (huv : u<v) (hv : v≤b)
      (hφu : principalPhaseX n k u=((j+1:ℕ):ℝ)*π) (hφv : principalPhaseX n k v=(j:ℝ)*π) :
      ∃ x ∈ Ioo u v, (enumerator n k).eval (-exp (-x))=0 ∧
        0<(-1:ℝ)^(j+1)*(enumerator (n+1) k).eval (-exp (-x)) := by
    have hm' : v^2+π^2≤(n:ℝ)*π^2 := by
      linarith only [pow_le_pow_left₀ (hu.trans huv.le) hv 2,hm]
    obtain ⟨⟨x,hx,h0⟩,hsign⟩ := original_wide_phase_cell_of_centered hk₇ hkn hcentered hu huv hm' hφu hφv
    exact ⟨x,hx,h0,hsign x hx h0⟩
  obtain ⟨z,hz,hmid⟩ := ordered_middle_level_roots ((enumerator n k).eval) ((enumerator (n+1) k).eval)
    (principalPhaseX n k) hb (H+1) (n/2) hcont (original_middle_phase_strictAnti hk₇ hkn b hm)
    (by simpa only [Nat.cast_add,Nat.cast_one] using hjoin) hcenter cells
  obtain ⟨f,hf,hfront⟩ := original_exterior_root_witnesses_all hn hk₂ hkn (original_near_lag_all_aspects hn hk₂ hkn)
  obtain ⟨hH,hsize⟩ := exterior_floor_budget hn
  obtain ⟨u,hu,hroots⟩ := join_signed_root_moduli (n:=n) (H:=H) (P:=(enumerator n k).eval)
    (Q:=(enumerator (n+1) k).eval) (exp_pos (-b)) (exp_le_one_iff.mpr (neg_nonpos.mpr hb)) f hf
    (fun i => ⟨(hfront i).2.1,exterior_modulus_lt_phase_boundary hH hsize
      (uniform_join_geometry hn).2.2.2.2.le (hfront i).2.2.1,(hfront i).2.2.2⟩)
    (fun i => -z i) (fun _ _ h => neg_lt_neg (hz h)) (by
      intro i
      obtain ⟨hi,h0,hs⟩ := hmid i
      exact ⟨by linarith only [hi.2],by linarith only [hi.1],by simpa only [neg_neg] using h0,
        by simpa only [neg_neg] using hs⟩)
  exact original_interlacing_of_literal_half_roots hk₂ hkn u hu hroots

#print axioms original_wide_aspect_interlacing_of_centered
end RepositoryQuotientAudit
