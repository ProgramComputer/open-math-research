import PrincipalScaledBudget
import SymmetricPoleComparison

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real Filter Finset
open scoped Topology PowerSeries

def offPrincipalWindow (M : ℕ) : Finset {q : ℤ // q ≠ 0} :=
  (symmetricPoleWindow M).subtype (· ≠ 0)

theorem off_principal_window_cofinal : Tendsto offPrincipalWindow atTop atTop := by
  apply Filter.tendsto_atTop_finset_of_monotone
  · intro m n h q hq
    have hh : (m:ℤ) ≤ n := by exact_mod_cast h
    simp only [offPrincipalWindow,mem_subtype,symmetricPoleWindow,mem_Icc] at hq ⊢
    omega
  · intro q
    have hq := tendsto_atTop.mp symmetric_pole_window_cofinal ({q.val} : Finset ℤ)
    obtain ⟨m,hm⟩ := eventually_atTop.mp hq
    exact ⟨m,mem_subtype.mpr (hm m le_rfl (mem_singleton_self _))⟩

def finiteScaledPrincipal (M j : ℕ) (θ : ℝ) : ℝ :=
  2*(j+2:ℕ)*exp (-cycleHarmonic ((j+2)-1)) *
    (∏ q ∈ offPrincipalWindow M, ∑' m,
       PowerSeries.coeff (R := ℂ) m (1+occupiedPrimitive (j+2) (cos θ) (sin θ) 0 q) *
         (pairedPoleDenom (cos θ) (sin θ) 0)^m).re

theorem finite_scaled_principal_tends (j : ℕ) {θ : ℝ} (hS : 0 < sin θ) :
    Tendsto (fun M => finiteScaledPrincipal M j θ) atTop (𝓝 (originalScaledPrincipal j θ)) := by
  have hp := principal_lattice_factors_hasProd j (cos θ) hS.ne'
  dsimp only at hp
  have h := hp.multipliable.hasProd.comp off_principal_window_cofinal
  exact (Complex.continuous_re.continuousAt.tendsto.comp h).const_mul _

/-- A uniform error estimate suffices on finite symmetric products even when
their principal values vary with the window. -/
theorem determinant_of_window_errors {D : ℕ→ℝ} {d E θ : ℝ} {j : ℕ}
    (hS : 0 < sin θ) (hD : Tendsto D atTop (𝓝 d))
    (herr : ∀ᶠ M in atTop, finiteScaledPrincipal M j θ - D M ≤ E) :
    originalScaledPrincipal j θ - E ≤ d := by
  have he := le_of_tendsto ((finite_scaled_principal_tends j hS).sub hD) herr
  linarith

#print axioms off_principal_window_cofinal
#print axioms finite_scaled_principal_tends
#print axioms determinant_of_window_errors
end OpenMathResearch.LongCycleExcedances
