import PrimitiveBinAssembly

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset

def oddGap (q a : ℤ) : ℕ := (2*(q-a)).natAbs

theorem oddGap_cast (q a : ℤ) : (oddGap q a:ℝ)=|primitiveOddNumber q-primitiveOddNumber a| := by
  have h : primitiveOddNumber q-primitiveOddNumber a=((2*(q-a):ℤ):ℝ) := by
    push_cast
    simp only [primitiveOddNumber]
    ring
  rw [h,oddGap,Int.cast_natAbs, Int.cast_abs]

/-- Each checked ceiling may be supplied as its integer product inequality. -/
theorem finite_star_dyadic_bound (A : Finset ℤ) (a : ℤ) {c : ℝ} {G : ℕ}
    (hG : 0 < G) (w v : ℤ → ℕ) {budget : ℕ}
    (hw : ∀ q ∈ A.erase a, oddBinKernel c q ≤ (w q:ℝ)/G)
    (hv : ∀ q ∈ A.erase a, w q ≤ oddGap q a*v q)
    (hb : ∑ q ∈ A.erase a,v q ≤ budget) :
    (∑ q ∈ A.erase a, oddStarTerm c a q) ≤ (budget:ℝ)/G := by
  have hGR : (0:ℝ)<G := by exact_mod_cast hG
  calc
    _ ≤ ∑ q ∈ A.erase a, (v q:ℝ)/G := by
      apply sum_le_sum
      intro q hq
      have hqa := (mem_erase.mp hq).1
      have hgapN : 0 < oddGap q a := by
        unfold oddGap
        have hz : 2*(q-a:ℤ)≠0 := mul_ne_zero (by decide) (sub_ne_zero.mpr hqa)
        exact Int.natAbs_pos.mpr hz
      have hgap : (0:ℝ) < oddGap q a := by exact_mod_cast hgapN
      unfold oddStarTerm
      rw [← oddGap_cast]
      apply (div_le_iff₀ hgap).mpr
      apply (hw q hq).trans
      apply (div_le_iff₀ hGR).2
      have hvR : (w q:ℝ) ≤ (oddGap q a:ℝ)*(v q:ℝ) := by exact_mod_cast hv q hq
      calc
        _ ≤ _ := hvR
        _ = _ := by field_simp [hGR.ne'] <;> ring
    _ = (↑(∑ q ∈ A.erase a,v q):ℝ)/G := by
      push_cast
      simp only [div_eq_mul_inv,sum_mul]
    _ ≤ _ := div_le_div_of_nonneg_right (by exact_mod_cast hb) hGR.le

#print axioms finite_star_dyadic_bound
end OpenMathResearch.LongCycleExcedances
