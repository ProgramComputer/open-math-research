import PrimitiveBinMass

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset

private theorem sum_reciprocal_difference (l u : ℕ) (hlu : l ≤ u) :
    (∑ s ∈ Ioc l u, (1/((s:ℝ)-1)-1/(s:ℝ))) =
      1/(l:ℝ)-1/(u:ℝ) := by
  induction u, hlu using Nat.le_induction with
  | base => simp
  | succ u hu ih =>
    have hI : Ioc l (u+1) = insert (u+1) (Ioc l u) := by
      ext s
      simp only [mem_Ioc,mem_insert]
      omega
    rw [hI,sum_insert (by simp),ih]
    push_cast
    ring

/-- Telescoping on a bin's ordinary first-block degrees. Integer lower and
upper endpoints are chosen before applying the outward rational estimates. -/
theorem primitive_first_block_subset_mass {k l u : ℕ} (hk : 0 < k)
    (hl : k ≤ l) (hlu : l ≤ u) (hu : u < 2*k) (T : Finset ℕ)
    (hT : T ⊆ Ioc l u) (b : ℕ → ℝ)
    (hb : ∀ s : ℕ, k < s → s < 2*k → b s = -1/((s:ℝ)*((s:ℝ)-1))) :
    (k:ℝ)*(∑ s ∈ T, |b s|) ≤ (k:ℝ)/(l:ℝ)-(k:ℝ)/(u:ℝ) := by
  have h0 : (0:ℝ) ≤ k := by positivity
  calc
    _ ≤ (k:ℝ)*(∑ s ∈ Ioc l u, |b s|) := mul_le_mul_of_nonneg_left
      (sum_le_sum_of_subset_of_nonneg hT (fun s _ _ => abs_nonneg (b s))) h0
    _ = (k:ℝ)*(∑ s ∈ Ioc l u, (1/((s:ℝ)-1)-1/(s:ℝ))) := by
      congr 1
      apply sum_congr rfl
      intro s hs
      have hks : k < s := hl.trans_lt (mem_Ioc.mp hs).1
      have hs1 : (1:ℝ)<s := by exact_mod_cast (show 1<s by omega)
      have hs0 : (0:ℝ)<s := by linarith
      rw [hb s hks ((mem_Ioc.mp hs).2.trans_lt hu), abs_of_nonpos]
      · field_simp [hs0.ne',(sub_pos.mpr hs1).ne'] <;> ring
      · exact div_nonpos_of_nonpos_of_nonneg (by norm_num)
          (mul_nonneg hs0.le (sub_nonneg.mpr hs1.le))
    _ = _ := by rw [sum_reciprocal_difference l u hlu]; ring

#print axioms primitive_first_block_subset_mass
end OpenMathResearch.LongCycleExcedances
