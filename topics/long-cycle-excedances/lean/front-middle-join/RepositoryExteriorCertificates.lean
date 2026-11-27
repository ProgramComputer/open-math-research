import CoefficientFrontWindow
import RepositoryExteriorReduction
import RepositoryPolynomialFront

set_option autoImplicit false
noncomputable section
namespace RepositoryQuotientAudit
open LongCycles LongCycleFinite Real Polynomial OpenMathResearch.LongCycleExcedances

/-- Two finite coefficient bounds on each exterior box suffice for the
full consecutive-row conclusion. There are no assumed roots or exact signs. -/
theorem original_interlacing_of_exterior_coefficient_bounds {n k : ℕ} (hn : 10^4 ≤ n)
    (hk : 7 ≤ k) (hkn : k ≤ n) (hsize : 30*log (n:ℝ)+20 < (n:ℝ)/(200*(k:ℝ)))
    (a u : Fin (uniformJoinRank n) → ℝ) (G : Fin (uniformJoinRank n) → ℝ[X])
    (ha : ∀ i, 0 < a i) (hu : ∀ i, 0 < u i)
    (horder : ∀ i j, i < j → (9/8:ℝ)*u i ≤ (7/8:ℝ)*u j)
    (hcap : ∀ i, (9/8:ℝ)*u i ≤
      (459/40:ℝ)*((uniformJoinRank n:ℝ)/((uniformJoinRank n:ℝ)+1))^n)
    (hOld : ∀ i, frontCoefficientNorm
      (frontOldResidual (enumerator n k) (i.val+1) (a i) (u i))
      (i.val+1) (7/8*u i) (9/8*u i) < a i/8)
    (hNext : ∀ i, frontCoefficientNorm
      (frontNextResidual (enumerator n k) (enumerator (n+1) k) (G i) (i.val+1) (a i))
      (i.val+1) (7/8*u i) (9/8*u i) < a i) :
    StrictNegativeInterlacing (enumerator n k).divX (enumerator (n+1) k).divX (n-2) ∧
    WeakRealInterlacing (enumerator n k) (enumerator (n+1) k) := by
  classical
  have each (i) := signed_root_of_front_coefficients (enumerator n k)
    (enumerator (n+1) k) (G i) (ha i) (hu i) (hOld i) (hNext i)
  choose f hf using each
  apply original_interlacing_of_exterior_roots hn hk hkn hsize f
  · intro i j hij
    exact (hf i).1.2.trans ((horder i j hij).trans_lt (hf j).1.1)
  · intro i
    exact ⟨(mul_pos (by norm_num : (0:ℝ)<7/8) (hu i)).trans (hf i).1.1,
      (hf i).1.2.le.trans (hcap i),(hf i).2⟩

/-- The three analytic estimates on the old two-term approximation, its
centered derivative and the actual lag polynomial are a second sufficient
condition; the permutation insertion identity is supplied by its pinned proof. -/
theorem original_interlacing_of_exterior_box_bounds {n k : ℕ} (hn : 10^4 ≤ n)
    (hk : 7 ≤ k) (hkn : k ≤ n) (hsize : 30*log (n:ℝ)+20 < (n:ℝ)/(200*(k:ℝ)))
    (a u : ℕ → ℝ)
    (ha : ∀ i < uniformJoinRank n, 0 < a i) (hu : ∀ i < uniformJoinRank n, 0 < u i)
    (hcap : ∀ i < uniformJoinRank n, u i ≤
      (51/5:ℝ)*((uniformJoinRank n:ℝ)/((uniformJoinRank n:ℝ)+1))^n)
    (hgap : ∀ i, i+1 < uniformJoinRank n → 20*u i < u (i+1))
    (hbox : ∀ i < uniformJoinRank n, FrontBounds (enumerator n k)
      (originalFrontLag n k) (i+1) (a i) (u i)) :
    StrictNegativeInterlacing (enumerator n k).divX (enumerator (n+1) k).divX (n-2) ∧
    WeakRealInterlacing (enumerator n k) (enumerator (n+1) k) := by
  obtain ⟨f,hf,hw⟩ := original_front_of_polynomial_bounds (by omega : 2 ≤ k)
    a u ha hu hcap hgap hbox
  apply original_interlacing_of_exterior_roots hn hk hkn hsize f hf
  intro i
  refine ⟨(hw i).1,?_,(hw i).2.2⟩
  have e : (9/8:ℝ)*(51/5)=459/40 := by norm_num
  simpa only [←mul_assoc,e] using (hw i).2.1

#print axioms original_interlacing_of_exterior_coefficient_bounds
#print axioms original_interlacing_of_exterior_box_bounds
end RepositoryQuotientAudit
