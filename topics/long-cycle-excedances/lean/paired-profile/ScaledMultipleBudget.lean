import BinIntegerCertificate

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Polynomial Finset

/-- Differentiate one actual primitive before applying the rounded estimate
for the other factors. This retains a small scalar from the linear mass
even after subtracting the rounded, rather than the actual, linear term. -/
theorem scaled_multiple_budget {ι : Type*} (A : Finset ι) (p : ι → ℝ[X])
    (hp : ∀ i ∈ A, ∀ j, 0 ≤ (p i).coeff j) (hz : ∀ i ∈ A, (p i).coeff 0=0)
    {G N : ℕ} (hG : 0 < G) (l q : ℕ→ℕ) (hl : l 0=0) (hq : q 0=G)
    {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (hL : ∀ i ≤ N, (binLinear A p).coeff i ≤ u*((l i:ℝ)/G))
    (hrec : ∀ m < N, ∑ ij ∈ antidiagonal m,(ij.1+1)*l (ij.1+1)*q ij.2 ≤ (m+1)*q (m+1)*G)
    {j : ℕ} (hj : 0 < j) (hN : j ≤ N) :
    (binMultiple A p).coeff j ≤ u*(((q j:ℝ)-(l j:ℝ))/G) := by
  let L := binScaledTable G N l
  let Q := binScaledTable G N q
  have hL' (i:ℕ) (hi : i ≤ N) : (binLinear A p).coeff i ≤ L.coeff i := by
    rw [bin_scaled_table_coeff hi]
    exact (hL i hi).trans (mul_le_of_le_one_left (by positivity) hu1)
  have h0 : L.coeff 0=0 := by simp [L,bin_scaled_table_coeff,hl]
  have h1 : Q.coeff 0=1 := by rw [bin_scaled_table_coeff (Nat.zero_le N),hq]; exact div_self (by exact_mod_cast hG.ne')
  have hdiff := bin_integer_derivative_certificate hG l q hrec
  have hb := bin_rounded_product_bounds A p hp hz L Q N h0 h1 hL' hdiff
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
  have hm := Nat.lt_of_succ_le hN
  have deriv := bin_multiple_derivative_le A p hp m
  have term : (derivative (binLinear A p)*(binFull A p-1)).coeff m ≤
      u*(derivative L*(Q-1)).coeff m := by
    rw [coeff_mul,coeff_mul,mul_sum]
    apply sum_le_sum
    intro ij hij
    have hij' := mem_antidiagonal.mp hij
    have hright : (binFull A p-1).coeff ij.2 ≤ (Q-1).coeff ij.2 := by
      simpa only [coeff_sub,sub_le_sub_iff_right] using (hb ij.2 (by omega)).1
    have hnn := bin_full_nonconstant_nonnegative A p hp ij.2
    have hleft : (derivative (binLinear A p)).coeff ij.1 ≤ u*(derivative L).coeff ij.1 := by
      simp only [coeff_derivative]
      rw [bin_scaled_table_coeff (by omega : ij.1+1 ≤ N),←mul_assoc]
      exact mul_le_mul_of_nonneg_right (hL _ (by omega)) (by positivity)
    have hpos : 0 ≤ u*(derivative L).coeff ij.1 := by
      rw [coeff_derivative,bin_scaled_table_coeff (by omega : ij.1+1 ≤ N)]; positivity
    simpa only [mul_assoc] using mul_le_mul hleft hright hnn hpos
  have hh := deriv.trans term
  rw [mul_sub,mul_one,coeff_sub] at hh
  have hfin := hh.trans (mul_le_mul_of_nonneg_left (sub_le_sub_right (hdiff m hm) _) hu)
  change (derivative (binMultiple A p)).coeff m ≤ u*((derivative Q).coeff m-(derivative L).coeff m) at hfin
  simp only [coeff_derivative,bin_scaled_table_coeff hN,←sub_mul,←sub_div,←mul_assoc] at hfin
  have h := le_of_mul_le_mul_right hfin (by positivity : 0 < (m:ℝ)+1)
  simpa only [Q,L,bin_scaled_table_coeff hN,←sub_div] using h

#print axioms scaled_multiple_budget
end OpenMathResearch.LongCycleExcedances
