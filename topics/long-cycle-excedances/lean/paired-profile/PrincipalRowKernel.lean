import PrincipalBudgetJoin

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset Real

def principalRowKernel (k : ℕ) (θ : ℝ) (q : ℤ) : ℝ :=
  ‖(pairedPoleDenom (cos θ) (sin θ) q)⁻¹‖^(k-1)/(2*|(q:ℝ)| *((k:ℝ)*sin θ))

theorem finite_principal_row_kernel {n j : ℕ} {θ : ℝ}
    (hn : 10000 ≤ n) (hkn : n ≤ 48*(j+2)) (hS : 0 < sin θ)
    (hangle : 6/5 ≤ (n:ℝ)*sin θ^2) (T : Finset ℤ) (h0 : 0 ∉ T) :
    (∑ q ∈ T, principalRowKernel (j+2) θ q) ≤ 4/5 := by
  classical
  let B := T.subtype (· ≠ 0)
  let f (q : {q:ℤ // q ≠ 0}) := if q ∈ B then principalRowKernel (j+2) θ q else 0
  have hsum : HasSum f (∑ q ∈ B, f q) :=
    hasSum_sum_of_ne_finset_zero (fun q h => by simp [f,h])
  have heq : (∑ q ∈ B, f q) = ∑ q ∈ T, principalRowKernel (j+2) θ q := by
    rw [show (∑ q ∈ B, f q)=∑ q ∈ B, principalRowKernel (j+2) θ q by
      exact sum_congr rfl (fun q hq => if_pos hq)]
    exact sum_subtype_of_mem _ (fun q hq h => h0 (h ▸ hq))
  rw [←heq,←hsum.tsum_eq]
  obtain ⟨hy,hA⟩ := principal_size_budgets (X:=48) (h:=1/1940) (A:=227/100) hn (by norm_num)
    (by exact_mod_cast hkn) hS hangle (by norm_num) (by norm_num)
  apply reflected_row_majorant hsum.summable (by norm_num : 0 < (1/1940:ℝ))
    (by norm_num : 0 < (227/100:ℝ)) _ reflected_log_all_budget
  intro q
  have hw := primitive_angular_bernoulli_kernel (r:=j+1) (show 0 < n by omega)
    (show 192 ≤ j+1 by omega) q hS (y:=40*(1/1940)) (by norm_num)
    (by simpa using hy) (U:=6/5) (by norm_num) hangle
  change ‖(pairedPoleDenom (cos θ) (sin θ) q)⁻¹‖^(j+1) ≤ _ at hw
  have hid : 1+40*(1/1940:ℝ)*(6/5)/192*(primitiveOddNumber q^2-1) =
      1+1/1940*(q:ℤ)*((q:ℤ)+1:ℝ) := by unfold primitiveOddNumber; ring
  rw [hid] at hw
  have ha : 227/100 ≤ ((j+2:ℕ):ℝ)*sin θ := by push_cast; nlinarith only [hA,hS]
  have hq : 0 < |((q:ℤ):ℝ)| := abs_pos.mpr (by exact_mod_cast q.property)
  have hker : principalRowKernel (j+2) θ q ≤ _ :=
    div_le_div₀ (by positivity) hw (by positivity : 0 < 2*|((q:ℤ):ℝ)| *(227/100))
      (mul_le_mul_of_nonneg_left ha (by positivity))
  by_cases hb : q ∈ B
  · simpa only [f,if_pos hb] using hker
  · rw [show f q=0 by simp [f,hb]]
    apply le_trans _ hker
    unfold principalRowKernel
    positivity

#print axioms finite_principal_row_kernel
end OpenMathResearch.LongCycleExcedances
