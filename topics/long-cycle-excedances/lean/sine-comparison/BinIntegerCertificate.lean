import BinProductMajorant
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Polynomial Finset

def binScaledTable (G N : ℕ) (v : ℕ → ℕ) : ℝ[X] :=
  ∑ i ∈ range (N+1), monomial i ((v i:ℝ)/G)

theorem bin_scaled_table_coeff {N j : ℕ} (hj : j ≤ N) (G : ℕ) (v : ℕ → ℕ) :
    (binScaledTable G N v).coeff j = (v j:ℝ)/G := by
  classical
  simp [binScaledTable,finset_sum_coeff,coeff_monomial,show j<N+1 by omega,hj]

/-- Natural-number certificate used by ceiling-rounded bin coefficients. -/
theorem bin_integer_derivative_certificate {G N : ℕ} (hG : 0 < G)
    (l q : ℕ → ℕ)
    (hrec : ∀ m < N, ∑ ij ∈ antidiagonal m, (ij.1+1)*l (ij.1+1)*q ij.2 ≤
        (m+1)*q (m+1)*G) :
    ∀ m < N, (derivative (binScaledTable G N l)*binScaledTable G N q).coeff m ≤
      (derivative (binScaledTable G N q)).coeff m := by
  intro m hm
  have hpos : 0 < (G:ℝ) := by exact_mod_cast hG
  let term (ij : ℕ × ℕ) : ℕ := (ij.1+1)*l (ij.1+1)*q ij.2
  have hsum : (derivative (binScaledTable G N l)*binScaledTable G N q).coeff m =
      (∑ ij ∈ antidiagonal m,(term ij:ℝ))/((G:ℝ)^2) := by
    rw [coeff_mul,div_eq_mul_inv,Finset.sum_mul]
    apply sum_congr rfl
    intro ij hij
    have he := Finset.mem_antidiagonal.mp hij
    rw [coeff_derivative,bin_scaled_table_coeff (by omega : ij.1+1≤N),
      bin_scaled_table_coeff (by omega : ij.2≤N)]
    dsimp only [term]
    push_cast
    field_simp
    <;> ring
  rw [hsum,coeff_derivative,bin_scaled_table_coeff (by omega : m+1 ≤ N)]
  apply (div_le_iff₀ (pow_pos hpos 2)).mpr
  have hh : ∑ ij ∈ antidiagonal m,(term ij:ℝ) ≤ ((m:ℝ)+1)*(q (m+1):ℝ)*(G:ℝ) := by
    exact_mod_cast hrec m hm
  refine hh.trans_eq ?_
  field_simp
  <;> ring

/-- For a positive target bin, the multiple-primitive budget is the
difference of the two rounded coefficients divided by G. -/
theorem bin_integer_multiple_bound {ι : Type*} (s : Finset ι) (p : ι → ℝ[X])
    (hp : ∀ i ∈ s, ∀ j, 0 ≤ (p i).coeff j) (hz : ∀ i ∈ s, (p i).coeff 0=0)
    {G N : ℕ} (hG : 0 < G) (l q : ℕ → ℕ) (hl : l 0=0) (hq : q 0=G)
    (hL : ∀ j ≤ N, (binLinear s p).coeff j ≤ (l j:ℝ)/G)
    (hrec : ∀ m < N, ∑ ij ∈ antidiagonal m, (ij.1+1)*l (ij.1+1)*q ij.2 ≤
        (m+1)*q (m+1)*G) {j : ℕ} (hj : 0 < j) (hN : j ≤ N) :
    (binFull s p).coeff j ≤ (q j:ℝ)/G ∧
      (binMultiple s p).coeff j ≤ ((q j:ℝ)-(l j:ℝ))/G := by
  let L := binScaledTable G N l
  let Q := binScaledTable G N q
  have h₀ : L.coeff 0=0 := by simp [L,bin_scaled_table_coeff,hl]
  have h₁ : Q.coeff 0=1 := by
    rw [bin_scaled_table_coeff (Nat.zero_le N), hq]
    exact div_self (by exact_mod_cast hG.ne')
  have hres := bin_rounded_product_bounds s p hp hz L Q N h₀ h₁
    (fun i hi => (hL i hi).trans_eq (bin_scaled_table_coeff hi G l).symm)
    (bin_integer_derivative_certificate hG l q hrec) j hN
  simpa only [coeff_sub,L,Q,bin_scaled_table_coeff hN,coeff_one,if_neg hj.ne',sub_zero,
    sub_div] using hres

/-- Integer ceiling update in the binned rational checker. -/
theorem bin_ceiling_recurrence {G N : ℕ} (hG : 0 < G) (l q : ℕ → ℕ)
    (h : ∀ m < N, q (m+1) =
      ((∑ ij ∈ antidiagonal m, (ij.1+1)*l (ij.1+1)*q ij.2) + (m+1)*G-1)/((m+1)*G)) :
    ∀ m < N, ∑ ij ∈ antidiagonal m, (ij.1+1)*l (ij.1+1)*q ij.2 ≤
      (m+1)*q (m+1)*G := by
  intro m hm
  let num := ∑ ij ∈ antidiagonal m, (ij.1+1)*l (ij.1+1)*q ij.2
  let den := (m+1)*G
  have hd : 0 < den := Nat.mul_pos (Nat.succ_pos m) hG
  have qstep : q (m+1) = (num+den-1)/den := h m hm
  have key := Nat.mod_add_div (num+den-1) den
  have rem := Nat.mod_lt (num+den-1) hd
  calc
    num ≤ den * ((num+den-1)/den) := by omega
    _ = (m+1)*q (m+1)*G := by rw [qstep]; dsimp only [den]; ring

#print axioms bin_ceiling_recurrence
#print axioms bin_integer_derivative_certificate
#print axioms bin_integer_multiple_bound
end OpenMathResearch.LongCycleExcedances
