import PrincipalCostTable
set_option autoImplicit false
namespace OpenMathResearch.LongCycleExcedances
open Finset

def principalDyadicScale : ℕ := 2^32

def dyadicErrorNumerator (i : ℕ) : ℕ :=
  ⌈(principalDyadicScale : ℚ) * rationalCenteredError i⌉₊

def scaledIntegerCost (lower : ℕ) (Q : Array ℕ) : ℕ :=
  ∑ b ∈ range 241, dyadicErrorNumerator (min 40 (lower - (b+3)/4)) * Q[b]!

theorem rationalCenteredError_le_dyadic (i : ℕ) :
    rationalCenteredError i ≤ (dyadicErrorNumerator i : ℚ) / principalDyadicScale := by
  apply (le_div_iff₀ (by norm_num [principalDyadicScale] : (0 : ℚ) < principalDyadicScale)).mpr
  rw [mul_comm]
  exact Nat.le_ceil _

theorem rationalPrincipalCost_le_integer_certificate (slab : Fin 9) (cap : ℕ)
    (hcert : 2 * scaledIntegerCost (principalLower slab) (qSlabPrefix slab 240) * 1000000 +
      100 * principalDyadicScale * linearScale ≤ cap * principalDyadicScale * linearScale) :
    rationalPrincipalCost slab ≤ (cap : ℚ) / 1000000 := by
  have hS : (0 : ℚ) < principalDyadicScale := by norm_num [principalDyadicScale]
  have hG : (0 : ℚ) < linearScale := by norm_num [linearScale]
  have hSG := mul_pos hS hG
  let D : ℚ := (principalDyadicScale : ℚ) * linearScale
  let Q := qSlabPrefix slab 240
  let f (b : ℕ) := min 40 (principalLower slab - (b+3)/4)
  have hs : (∑ b ∈ range 241, rationalCenteredError (f b) * ((Q[b]! : ℚ)/linearScale)) ≤
      (scaledIntegerCost (principalLower slab) Q : ℚ) / D := by
    simp only [scaledIntegerCost, Nat.cast_sum, Nat.cast_mul]
    simp only [div_eq_mul_inv, sum_mul]
    apply sum_le_sum
    intro b _
    have h := mul_le_mul_of_nonneg_right (rationalCenteredError_le_dyadic (f b))
      (show 0 ≤ (Q[b]! : ℚ) / linearScale from div_nonneg (Nat.cast_nonneg _) hG.le)
    calc
      _ ≤ ((dyadicErrorNumerator (f b) : ℚ) / principalDyadicScale) *
          ((Q[b]! : ℚ) / linearScale) := by simpa only [div_eq_mul_inv] using h
      _ = _ := by
        change ((dyadicErrorNumerator (f b) : ℚ) / principalDyadicScale) *
            ((Q[b]! : ℚ) / linearScale) =
          (dyadicErrorNumerator (f b) : ℚ) * (Q[b]! : ℚ) *
            ((principalDyadicScale : ℚ) * linearScale)⁻¹
        rw [div_mul_div_comm, div_eq_mul_inv]
  have hc : 2 * (scaledIntegerCost (principalLower slab) Q : ℚ) * 1000000 +
      100 * D ≤ (cap : ℚ) * D := by
    have clean : (2 * scaledIntegerCost (principalLower slab) Q * 1000000 +
        100 * principalDyadicScale * linearScale : ℕ) ≤ cap * principalDyadicScale * linearScale := hcert
    have lifted := (Nat.cast_le (α := ℚ)).mpr clean
    push_cast at lifted
    dsimp [D]
    simpa only [mul_assoc] using lifted
  unfold rationalPrincipalCost
  change 1/10000 + 2 * (∑ b ∈ range 241,
    rationalCenteredError (f b) * ((Q[b]! : ℚ) / linearScale)) ≤ (cap : ℚ) / 1000000
  apply le_trans (add_le_add_left (mul_le_mul_of_nonneg_left hs (by norm_num)) (1/10000))
  have hD : 0 < D := hSG
  apply (le_div_iff₀ (by norm_num : (0:ℚ) < 1000000)).mpr
  apply (le_of_mul_le_mul_right ?_ hD)
  calc
    (1/10000 + 2*((scaledIntegerCost (principalLower slab) Q : ℚ)/D))*1000000*D
        = 2 * (scaledIntegerCost (principalLower slab) Q : ℚ) * 1000000 + 100*D := by
            field_simp
            ring
    _ ≤ (cap : ℚ) * D := hc

#print axioms rationalPrincipalCost_le_integer_certificate
end OpenMathResearch.LongCycleExcedances
