import RoundedProductTable

set_option autoImplicit false
namespace OpenMathResearch.LongCycleExcedances
open Finset

def principalLower (j : Fin 9) : ℕ :=
  (![4, 6, 10, 16, 22, 28, 34, 40, 44] : Fin 9 → ℕ) j

def rationalCenteredError (j : ℕ) : ℚ :=
  if j = 0 then 4/7 else if j = 1 then 453/1000 else
    min (4/7 - if j = 2 then 1/2 else 547/1000)
      (((j : ℚ)+1)/(2*(j : ℚ)*j.factorial))

def rationalPrincipalCost (j : Fin 9) : ℚ :=
  let Q := qSlabPrefix j 240
  1/10000 + 2 * (∑ b ∈ range 241,
    rationalCenteredError (min 40 (principalLower j - (b+3)/4)) *
      ((Q[b]! : ℚ)/linearScale))

def principalMillionths (j : Fin 9) : ℕ :=
  ⌈(1000000 : ℚ) * rationalPrincipalCost j⌉₊

theorem rationalPrincipalCost_le_millionths (j : Fin 9) :
    rationalPrincipalCost j ≤ (principalMillionths j : ℚ) / 1000000 := by
  apply (le_div_iff₀ (by norm_num : (0 : ℚ) < 1000000)).mpr
  rw [mul_comm]
  exact Nat.le_ceil _

#print axioms rationalPrincipalCost_le_millionths
end OpenMathResearch.LongCycleExcedances
