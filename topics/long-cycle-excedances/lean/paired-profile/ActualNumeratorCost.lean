import ActualWindowParts
import RepositoryCutoffJump

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset Real CycleProbability

private def atomTermAt (k n : ℕ) (d : ℕ→ℝ) (θ : ℝ) (A : Finset ℤ) (a : ℤ) :=
  ((k:ℝ)/sin θ*|numeratorDiff k d k| *‖(pairedPoleDenom (cos θ) (sin θ) a)⁻¹‖^k*|sin ((n:ℝ)*θ)|) *
    ‖occupiedCoeffAt k (n+1-k) θ A a‖

private theorem split_numerator_term {k n t : ℕ} (hkn : k ≤ n) (ht : t ≤ n+1)
    (d : ℕ→ℝ) (θ : ℝ) (A : Finset ℤ) (a : ℤ) :
    (k:ℝ)/sin θ * ‖poleNumeratorTerm k n t d θ A a‖ =
      scaledRegularTerm k n t d θ a*‖occupiedCoeffAt k t θ A a‖ +
        (if t=n+1-k then atomTermAt k n d θ A a else 0) := by
  simp only [poleNumeratorTerm,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
  by_cases he : t=n+1-k
  · have hs : n+1-t=k := by omega
    rw [scaledRegularTerm,if_neg (by omega),if_pos he,zero_mul,zero_add,hs,he]
    unfold atomTermAt
    change _ = ((k:ℝ)/sin θ*|numeratorDiff k d k| *
      ‖(pairedPoleDenom (cos θ) (sin θ) a)⁻¹‖^k*|sin ((n:ℝ)*θ)|) *_
    ring
  · rw [if_neg he,add_zero,scaledRegularTerm]
    by_cases hr : k < n+1-t
    · rw [if_pos hr]
      ring
    · have hs : n+1-t < k := by omega
      rw [if_neg hr,numeratorDiff_below d hs]
      simp

/-- Absolute numerator terms partition exactly into longer successor degrees
and the unique cutoff jump, even when the old row reaches its final degree. -/
theorem actual_numerator_mass {k n : ℕ} (hkn : k ≤ n) (d : ℕ→ℝ)
    (θ : ℝ) (A : Finset ℤ) :
    (∑ a ∈ A, ∑ t ∈ range (n+2), (k:ℝ)/sin θ * ‖poleNumeratorTerm k n t d θ A a‖)=
      finiteRegularCost k n d θ A + finiteCutoffJump k n d θ A := by
  unfold finiteRegularCost finiteCutoffJump
  rw [←sum_add_distrib]
  apply sum_congr rfl
  intro a _
  have ht : n+1-k ∈ range (n+2) := mem_range.mpr (by omega)
  have hh (t:ℕ) (h : t ∈ range (n+2)) := split_numerator_term hkn
    (show t ≤ n+1 by have := mem_range.mp h; omega) d θ A a
  rw [sum_congr rfl hh,sum_add_distrib]
  congr 1
  rw [sum_ite_eq',if_pos ht]
  rfl

#print axioms actual_numerator_mass
end OpenMathResearch.LongCycleExcedances
