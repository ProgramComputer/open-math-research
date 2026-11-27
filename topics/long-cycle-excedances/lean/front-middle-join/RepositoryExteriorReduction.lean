import FrontModulusJoin
import FrontMiddleWitnesses
import OriginalLiteralHalfRoots
import RepositoryJoinAngle
import RepositoryMiddleLevelSelection

set_option autoImplicit false
noncomputable section
namespace RepositoryQuotientAudit
open LongCycles LongCycleFinite Real OpenMathResearch.LongCycleExcedances

/-- In the uniform large-size sector, signed ordered old roots up to
the explicit exterior envelope suffice for both full root factorizations. -/
theorem original_interlacing_of_exterior_roots {n k : ℕ} (hn : 10^4 ≤ n) (hk : 7 ≤ k)
    (hkn : k ≤ n) (hsize : 30*log (n:ℝ)+20 < (n:ℝ)/(200*(k:ℝ)))
    (f : Fin (uniformJoinRank n) → ℝ) (hf : StrictMono f)
    (hfront : ∀ i, 0 < f i ∧ f i ≤
      (459/40:ℝ)*((uniformJoinRank n:ℝ)/((uniformJoinRank n:ℝ)+1))^n ∧
      (enumerator n k).eval (-f i) = 0 ∧
      0 < (-1:ℝ)^(i.val+2)*(enumerator (n+1) k).eval (-f i)) :
    StrictNegativeInterlacing (enumerator n k).divX (enumerator (n+1) k).divX (n-2) ∧
    WeakRealInterlacing (enumerator n k) (enumerator (n+1) k) := by
  let H := uniformJoinRank n
  let b := uniformJoinLog n
  have hgeom := uniform_join_geometry hn
  have hphase := original_uniform_join_phase hn hk hsize
  have hb : 0 ≤ b := (by positivity : (0:ℝ) ≤ 10*√(k:ℝ)).trans hphase.1.le
  have hφ : principalPhaseX n k b < ((H+1:ℕ):ℝ)*π := by
    simpa only [Nat.cast_add,Nat.cast_one,H,b] using hphase.2.2.2
  obtain ⟨m,hmono,hm⟩ := original_ordered_middle_roots (by omega : 100 ≤ n) hk hkn hb
    (uniform_join_radius_sq hn).le hsize hφ
  obtain ⟨hH,hbudget⟩ := exterior_floor_budget hn
  have hfront' (i : Fin H) : 0 < f i ∧ f i < exp (-b) ∧ (enumerator n k).eval (-f i)=0 ∧
      0 < (-1:ℝ)^(i.val+2)*(enumerator (n+1) k).eval (-f i) :=
    ⟨(hfront i).1,exterior_modulus_lt_phase_boundary hH hbudget hgeom.2.2.2.2.le (hfront i).2.1,
      (hfront i).2.2⟩
  obtain ⟨u,hu,hs⟩ := join_signed_root_moduli (n:=n)
    (P:=(enumerator n k).eval) (Q:=(enumerator (n+1) k).eval)
    (exp_pos (-b)) (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hb))
    f hf hfront' m hmono hm
  exact original_interlacing_of_literal_half_roots (by omega) hkn u hu hs

#print axioms original_interlacing_of_exterior_roots
end RepositoryQuotientAudit
