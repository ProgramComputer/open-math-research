import SymmetricPoleComparison
import PrimitiveNumeratorInputs

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real Finset CycleProbability
open scoped PowerSeries

def occupiedCoeffAt (k t : ℕ) (θ : ℝ) (A : Finset ℤ) (a : ℤ) : ℂ :=
  PowerSeries.coeff (R := ℂ) t (∏ v ∈ A.erase a, (1+occupiedPrimitive k (cos θ) (sin θ) a v))

def poleValueTerm (k n t : ℕ) (d : ℕ→ℝ) (θ : ℝ) (A : Finset ℤ) (a : ℤ) : ℂ :=
  let w := pairedPoleDenom (cos θ) (sin θ) a
  occupiedCoeffAt k t θ A a*w⁻¹^(n+1-t)*(cutoffWeight k d (n-t):ℂ)*
    (w*(sin ((n:ℝ)*θ+θ):ℂ)-(sin ((n:ℝ)*θ):ℂ))

def poleNumeratorTerm (k n t : ℕ) (d : ℕ→ℝ) (θ : ℝ) (A : Finset ℤ) (a : ℤ) : ℂ :=
  let w := pairedPoleDenom (cos θ) (sin θ) a
  occupiedCoeffAt k t θ A a*w⁻¹^(n+1-t)*(numeratorDiff k d (n+1-t):ℂ)*(sin ((n:ℝ)*θ):ℂ)

def windowDeterminant (k n : ℕ) (θ : ℝ) (A : Finset ℤ) : ℂ :=
  (sin ((n:ℝ)*θ+θ):ℂ)*finiteCoefficient A k (cos θ) (sin θ) n -
    (sin ((n:ℝ)*θ):ℂ)*finiteCoefficient A k (cos θ) (sin θ) (n+1)

theorem finite_determinant_parts {k n : ℕ} {d : ℕ→ℝ} (hd : Spec k d) (hk : 0 < k) (hn : 0 < n)
    {θ : ℝ} (hS : 0 < sin θ) (A : Finset ℤ) :
    windowDeterminant k n θ A =
      (∑ a ∈ A, ∑ t ∈ range (n+2), poleValueTerm k n t d θ A a) -
      (∑ a ∈ A, ∑ t ∈ range (n+2), poleNumeratorTerm k n t d θ A a) := by
  rw [windowDeterminant,finiteCoefficient,finiteCoefficient,finite_adjacent_occupied_rows A hk hn _ hS.ne']
  rw [←sum_sub_distrib]
  apply sum_congr rfl
  intro a _
  rw [←sum_sub_distrib]
  apply sum_congr rfl
  intro t _
  simp only [coeff_original_cutoff_weight hd hk,poleNumeratorTerm,poleValueTerm,numeratorDiff,Complex.ofReal_sub,occupiedCoeffAt]
  rw [show n+1-t-1=n-t by omega]
  ring

#print axioms finite_determinant_parts
end OpenMathResearch.LongCycleExcedances
