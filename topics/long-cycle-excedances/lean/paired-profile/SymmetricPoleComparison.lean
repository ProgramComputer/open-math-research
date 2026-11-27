import FiniteAdjacentResidues
import Mathlib.Order.Filter.AtTopBot.Finset

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Filter Finset
open scoped PowerSeries Topology

/-- Both principal poles are present already at M=0. -/
def symmetricPoleWindow (M : ℕ) : Finset ℤ := Icc (-(M:ℤ)-1) (M:ℤ)

theorem symmetric_pole_window_cofinal :
    Tendsto symmetricPoleWindow atTop atTop := by
  apply Filter.tendsto_atTop_finset_of_monotone
  · intro m n h q hq
    have h' : (m:ℤ) ≤ n := by exact_mod_cast h
    rw [symmetricPoleWindow,mem_Icc] at hq ⊢
    omega
  · intro q
    cases q with
    | ofNat n => exact ⟨n,by simp [symmetricPoleWindow]; omega⟩
    | negSucc n => exact ⟨n,by simp [symmetricPoleWindow]; omega⟩

theorem symmetric_pole_window_conjugate (M : ℕ) (q : ℤ) :
    -q-1 ∈ symmetricPoleWindow M ↔ q ∈ symmetricPoleWindow M := by
  simp only [symmetricPoleWindow,mem_Icc]
  omega

theorem symmetric_pole_window_principals (M : ℕ) :
    (0:ℤ) ∈ symmetricPoleWindow M ∧ (-1:ℤ) ∈ symmetricPoleWindow M := by
  simp only [symmetricPoleWindow,mem_Icc]
  omega

def finiteCoefficient (A : Finset ℤ) (k : ℕ) (C S : ℝ) (n : ℕ) : ℂ :=
  PowerSeries.coeff (R := ℂ) n (∏ q ∈ A,
    PowerSeries.rescale (pairedPoleDenom C S q)⁻¹ (cutoffCycleSeries k))

/-- A uniform finite lower bound gives the bound on the two original real rows
once their coefficient limits are supplied. Strictness uses a positive margin. -/
theorem determinant_lower_of_symmetric_windows {n k : ℕ} {C S old next x y δ : ℝ}
    (hold : Tendsto (fun A => finiteCoefficient A k C S n) atTop (𝓝 (old:ℂ)))
    (hnext : Tendsto (fun A => finiteCoefficient A k C S (n+1)) atTop (𝓝 (next:ℂ)))
    (hwin : ∀ᶠ M in atTop, δ ≤ ((x:ℂ)*finiteCoefficient (symmetricPoleWindow M) k C S n -
      (y:ℂ)*finiteCoefficient (symmetricPoleWindow M) k C S (n+1)).re) :
    δ ≤ x*old-y*next := by
  have ht := ((hold.comp symmetric_pole_window_cofinal).const_mul (x:ℂ)).sub
    ((hnext.comp symmetric_pole_window_cofinal).const_mul (y:ℂ))
  have hr := Complex.continuous_re.continuousAt.tendsto.comp ht
  have h := ge_of_tendsto hr hwin
  simpa using h

#print axioms symmetric_pole_window_cofinal
#print axioms symmetric_pole_window_conjugate
#print axioms determinant_lower_of_symmetric_windows
end OpenMathResearch.LongCycleExcedances
