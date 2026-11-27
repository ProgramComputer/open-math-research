import HighAngleScalar
import LowMomentInput

noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset Real

private theorem harmonic_tail_log {k : ℕ} (hk : 2 ≤ k) :
    (∑ d ∈ Icc 2 (k-1), (1:ℝ)/(d:ℝ)) ≤ log k := by
  rw [← Nat.Ico_succ_right, Finset.sum_Ico_eq_sum_range]
  have he : (k-1).succ-2 = k-2 := by omega
  rw [he]
  simp only [Nat.cast_add, Nat.cast_ofNat, add_comm (2:ℝ)]
  apply (shifted_harmonic_sum (k-2)).trans
  apply Real.log_le_log (by positivity)
  have hc : k-2+1 ≤ k := by omega
  exact_mod_cast hc

theorem harmonic_full_log {k : ℕ} (hk : 1 ≤ k) :
    (∑ i ∈ range k, (1:ℝ)/((i+1:ℕ):ℝ)) ≤ 1+log k := by
  have he : k = (k-1)+1 := by omega
  conv_lhs => rw [he, sum_range_succ']
  have h := shifted_harmonic_sum (k-1)
  have hc : ((k-1:ℕ):ℝ)+1 = k := by exact_mod_cast he.symm
  rw [hc] at h
  simp only [Nat.cast_succ, zero_add, Nat.cast_one, one_div_one]
  convert add_le_add_right h 1 using 1 <;> first | ring | (apply sum_congr rfl; intros; congr 1; ring)

private theorem positive_band_sum {k : ℕ} (hk : 2 ≤ k) (F : ℕ → ℝ) :
    (∑ i ∈ range (k-1), F (i+1)) = F 1 + ∑ d ∈ Icc 2 (k-1), F d := by
  have he : Icc 1 (k-1) = insert 1 (Icc 2 (k-1)) := by
    ext j
    simp only [mem_Icc,mem_insert]
    omega
  have h1 : 1 ∉ Icc 2 (k-1) := by simp
  rw [←sum_insert h1,←he,←Nat.Ico_succ_right,sum_Ico_eq_sum_range]
  have hh : (k-1).succ-1 = k-1 := by omega
  simp only [hh,Nat.add_comm 1]

/-- Collect a bounded low-degree mass and a harmonic high-degree estimate on the
enlarged circle. All terms are absolute values of the individual monomials. -/
theorem uniform_mass_from_split {k L : ℕ} (hk : 2 ≤ k) (F : ℕ → ℝ)
    (hF : ∀ d, 0 ≤ F d) {A B C : ℝ} (hB : 0 ≤ B) (h1 : F 1 ≤ A)
    (lo : (∑ d ∈ Icc 2 L, F d) ≤ C)
    (hi : ∀ d ∈ Icc 2 (k-1), L < d → F d ≤ B/(d:ℝ)) :
    (∑ i ∈ range (k-1), F (i+1)) ≤ A+C+B*log k := by
  rw [positive_band_sum hk F]
  let I := Icc 2 (k-1)
  have low : (∑ d ∈ I.filter (· ≤ L), F d) ≤ C := by
    apply le_trans _ lo
    apply sum_le_sum_of_subset_of_nonneg
    · intro d hd
      exact mem_Icc.mpr ⟨(mem_Icc.mp (mem_filter.mp hd).1).1,(mem_filter.mp hd).2⟩
    · exact fun i _ _ => hF i
  have high : (∑ d ∈ I.filter (fun j => ¬ j ≤ L), F d) ≤ B*log k := by
    apply le_trans _ (mul_le_mul_of_nonneg_left (harmonic_tail_log hk) hB)
    rw [mul_sum]
    apply le_trans (b := ∑ d ∈ I.filter (fun j => ¬ j ≤ L), B*(1/(d:ℝ)))
    · apply sum_le_sum
      intro d hd
      rw [mul_one_div]
      exact hi d (mem_filter.mp hd).1 (lt_of_not_ge (mem_filter.mp hd).2)
    · apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      intros; positivity
  have split := sum_filter_add_sum_filter_not I (· ≤ L) F
  change (F 1 + ∑ d ∈ I, F d) ≤ _
  linarith only [h1,low,high,split]

#print axioms uniform_mass_from_split
end OpenMathResearch.LongCycleExcedances
