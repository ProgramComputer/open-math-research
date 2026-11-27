import AtomMultipleBudget

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset Real Polynomial CycleProbability

theorem literal_multiple_at_nonnegative (k n b t : ℕ) (θ : ℝ) (A : Finset ℤ) (a : ℤ) :
    0 ≤ literalMultipleAt k n b t θ A a := by
  exact marked_multiple_nonnegative (A.erase a) k (n+1)
    (fun v s => ‖PowerSeries.coeff (R := ℂ) s (occupiedPrimitive k (cos θ) (sin θ) a v)‖)
    (fun _ _ _ => norm_nonneg _) b t

def atomMultipleWeight (k b n t : ℕ) (θ : ℝ) (A : Finset ℤ) (a : ℤ) : ℝ :=
  literalMultipleAt k n b t θ A a*
    ‖(pairedPoleDenom (cos θ) (sin θ) a)⁻¹‖^k /sin θ

def atomMultiplePoleBudget (lower upper b : ℕ) (A₀ : ℝ) (q l : ℕ→ℕ) (a : ℤ) : ℝ :=
  if 4*(lower-1) < b ∧ b+5 ≤ 5*upper then
    A₀*upper/(6/5)*(((q b:ℝ)-(l b:ℝ))/linearScale)*valueKernel lower upper b a else 0

theorem atom_multiple_bin (slab : Fin 9) {k n lower b t : ℕ} {d : ℕ→ℝ} (hd : Spec k d)
    (hn : 10000 ≤ n) (hnX : n ≤ linearSlabX slab*k) (hl : 0 < lower) (hlo : lower*k ≤ n)
    (he : t+k=n+1) {θ : ℝ} (hS : 0 < sin θ) (hU : 6/5 ≤ (n:ℝ)*sin θ^2)
    (A : Finset ℤ) (a : ℤ) (q : ℕ→ℕ) (hq : q 0=linearScale)
    (hrec : ∀ m < 240, ∑ ij ∈ antidiagonal m,
      (ij.1+1)*linearSlabTable slab (ij.1+1)*q ij.2 ≤ (m+1)*q (m+1)*linearScale) :
    atomMultipleWeight k b n t θ A a ≤
      atomMultiplePoleBudget lower (linearSlabX slab) b (linearSlabLower slab) q (linearSlabTable slab) a := by
  let upper := linearSlabX slab
  let A₀ : ℝ := linearSlabLower slab
  let gap := ((q b:ℝ)-(linearSlabTable slab b:ℝ))/linearScale
  have hx : upper ≤ 48 := by dsimp [upper]; fin_cases slab <;> norm_num [linearSlabX]
  have hk : 192 ≤ k := by have := hnX.trans (Nat.mul_le_mul_right k hx); omega
  have hA : 0 < A₀ := by dsimp [A₀]; fin_cases slab <;> norm_num [linearSlabLower,linearSlabQuarter]
  have hKS : 0 < (k:ℝ)*sin θ := by positivity
  have hu : 0 < A₀/((k:ℝ)*sin θ) := div_pos hA hKS
  have hnn := literal_multiple_at_nonnegative k n b t θ A a
  by_cases hm : 4*(lower-1) < b ∧ b+5 ≤ 5*upper
  · rw [atomMultiplePoleBudget,if_pos hm]
    have hbin := literal_multiple_scaled_bound slab hd hn hnX hS hU A a t q hq hrec
      (show 0 < b by omega) (by omega)
    have hgap : 0 ≤ gap := nonneg_of_mul_nonneg_right (hnn.trans hbin) hu
    by_cases hsupp : 4*t ≤ k*b ∧ k*b ≤ 5*t
    · have hker := atom_kernel_on_bin hk hl hlo hnX he hsupp.1 hS hU a
      have hscale := atom_angle_scale (by omega : 0 < k) hnX hS hA.le (by norm_num : (0:ℝ) < 6/5) hU
      have hρ : 0 ≤ valueKernel lower upper b a := inv_nonneg.mpr (Even.pow_nonneg (by decide : Even 96) _)
      unfold atomMultipleWeight
      calc
        _ ≤ ((A₀/((k:ℝ)*sin θ))*gap)*valueKernel lower upper b a/sin θ :=
          div_le_div_of_nonneg_right (mul_le_mul hbin hker (by positivity) (mul_nonneg hu.le hgap)) hS.le
        _ = ((A₀/((k:ℝ)*sin θ))/sin θ)*gap*valueKernel lower upper b a := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hscale hgap) hρ
    · have hzero := literal_multiple_support A (by omega : 0 < k) (n+1) (cos θ) (sin θ) a hsupp
      change literalMultipleAt k n b t θ A a=0 at hzero
      rw [atomMultipleWeight,hzero,zero_mul,zero_div]
      exact mul_nonneg (mul_nonneg (by positivity) hgap) (inv_nonneg.mpr (Even.pow_nonneg (by decide : Even 96) _))
  · have hsupp : ¬(4*t ≤ k*b ∧ k*b ≤ 5*t) :=
      fun h => hm (atom_bin_interval (by omega : 5 < k) hl hlo hnX he h.1 h.2)
    have hzero := literal_multiple_support A (by omega : 0 < k) (n+1) (cos θ) (sin θ) a hsupp
    change literalMultipleAt k n b t θ A a=0 at hzero
    rw [atomMultipleWeight,hzero,zero_mul,zero_div,atomMultiplePoleBudget,if_neg hm]

#print axioms atom_multiple_bin
end OpenMathResearch.LongCycleExcedances
