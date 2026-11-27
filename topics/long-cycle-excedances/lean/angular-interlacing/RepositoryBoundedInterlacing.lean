import RepositoryCoarseDeterminant
import BoundedAngularWitnesses
import BoundedAspectSlabs
import AllAspectExterior
import FrontMiddleWitnesses
import OriginalLiteralHalfRoots

set_option autoImplicit false
noncomputable section
namespace RepositoryQuotientAudit
open LongCycles LongCycleBounds LongCycleFinite Real OpenMathResearch.LongCycleExcedances

/-- Undo the two positive factors in the determinant normalization at the same
negative evaluation point in each consecutive permutation polynomial. -/
theorem angularOriginalRow_eq_eval (m k : ℕ) (θ : ℝ) :
    angularOriginalRow k m θ = angularRowScale m θ*
      (enumerator m k).eval (-exp (-angleCoordinate θ)) := by
  exact angular_row_normalization m (enumerator m k) θ

theorem original_bounded_aspect_signed_middle {n k : ℕ}
    (hn : 10000 ≤ n) (hk : 2 ≤ k) (hl : 4*k ≤ n) (hu : n ≤ 48*k) :
    ∃ u : Fin (n/2-(uniformJoinRank n+1)) → ℝ, StrictMono u ∧
      ∀ i, exp (-exteriorIntegerSeamLog n)<u i ∧ u i<1 ∧
        (enumerator n k).eval (-u i)=0 ∧
        0<(-1:ℝ)^(uniformJoinRank n+1+i.val+1)*(enumerator (n+1) k).eval (-u i) := by
  obtain ⟨s,hs₁,hs₂⟩ := bounded_aspect_has_slab hl hu
  obtain ⟨j,rfl⟩ : ∃ j, k=j+2 := ⟨k-2,by omega⟩
  apply bounded_determinant_middle_witnesses (k:=j+2) hn
  intro θ hS hC hmid
  have h := original_bounded_aspect_determinant s hn hs₁ hs₂ hS hC hmid
  have positive := (by norm_num : (0:ℝ)<93581/10^6).trans h
  simpa only [scaledOriginalDeterminant,angularOriginalRow_eq_eval] using positive

/-- Complete strict negative interlacing after division by the shared zero,
and weak interlacing for the original unweighted strict-excedance enumerators. -/
theorem original_bounded_aspect_interlacing {n k : ℕ}
    (hn : 10000 ≤ n) (hk : 2 ≤ k) (hl : 4*k ≤ n) (hu : n ≤ 48*k) :
    StrictNegativeInterlacing (enumerator n k).divX (enumerator (n+1) k).divX (n-2) ∧
    WeakRealInterlacing (enumerator n k) (enumerator (n+1) k) := by
  have hkn : k ≤ n := by omega
  obtain ⟨f,hf,hfront⟩ := original_all_aspect_exterior hn hk hkn
  obtain ⟨m,hm,hmiddle⟩ := original_bounded_aspect_signed_middle hn hk hl hu
  obtain ⟨hstart,hhalf,_,he⟩ := integer_middle_first_sample hn
  have hc : exp (-exteriorIntegerSeamLog n) ≤ 1 :=
    he.le.trans (angular_modulus_lt_one ⟨hstart,hhalf⟩).le
  obtain ⟨u,hmono,hw⟩ := join_signed_root_moduli (P:=(enumerator n k).eval)
    (Q:=(enumerator (n+1) k).eval) (exp_pos _) hc f hf hfront m hm hmiddle
  exact original_interlacing_of_literal_half_roots hk hkn u hmono hw

#print axioms angularOriginalRow_eq_eval
#print axioms original_bounded_aspect_signed_middle
#print axioms original_bounded_aspect_interlacing
end RepositoryQuotientAudit
