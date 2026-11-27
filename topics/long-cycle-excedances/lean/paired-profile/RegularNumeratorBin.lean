import TiltedNumeratorMass
import NonprincipalPoleValue

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open CycleProbability Finset Real

def regularBlockIndex (lower b : ℕ) := lower-(b+3)/4

def regularBinWeight (lower b : ℕ) : ℝ :=
  let j := regularBlockIndex lower b
  if 2 ≤ j then 1/(2*(j.factorial:ℝ)) else 1

private theorem blockIndex_valid {lower b k n t : ℕ} (hlo : lower*k ≤ n) (ht : 4*t ≤ k*b) :
    regularBlockIndex lower b*k ≤ n-t := by
  let z := (b+3)/4
  have hb : b ≤ 4*z := by dsimp [z]; omega
  have hr : t ≤ z*k := by have := Nat.mul_le_mul_left k hb; nlinarith
  by_cases h : z ≤ lower
  · have hh := Nat.sub_add_cancel h
    have he : (lower-z)*k+z*k = lower*k := by rw [←Nat.add_mul,hh]
    change (lower-z)*k ≤ n-t
    omega
  · have he : lower-z=0 := by omega
    change (lower-z)*k ≤ _
    simp [he]

/-- The successor shift gives a strict left endpoint at an integral
aspect-to-bin difference, so that the factorial of its floor is admissible. -/
theorem regular_numerator_strict_bin {k n t lower b : ℕ} {d : ℕ→ℝ} (hd : Spec k d)
    (hk : 2 ≤ k) (hlo : lower*k ≤ n) (ht : 4*t ≤ k*b) (hreg : k < n+1-t) :
    (k:ℝ)^2*|numeratorDiff k d (n+1-t)| ≤ regularBinWeight lower b := by
  let j := regularBlockIndex lower b
  let z := n-t
  let h := z/k
  have hk0 : 0 < k := by omega
  have hdiv : h*k ≤ z := Nat.div_mul_le_self _ _
  have hm := Nat.mod_lt z hk0
  have hs : z%k+h*k=z := by simpa [h,Nat.mul_comm] using Nat.mod_add_div z k
  have he : n+1-t = h*k+z%k+1 := by dsimp [z] at hs ⊢; omega
  have hr : j ≤ h := (Nat.le_div_iff_mul_le hk0).mpr (blockIndex_valid hlo ht)
  have hp : 0 < (k:ℝ) := by exact_mod_cast hk0
  have hpos : 0 < (k:ℝ)^2 := by positivity
  have hf : 0 < (h.factorial:ℝ) := by positivity
  change _ ≤ if 2 ≤ j then _ else _
  split
  next h₂ =>
    have hbound := hd.numeratorDiff_factorial_block hk0 (h₂.trans hr)
      (show h*k < n+1-t by omega) (show n+1-t ≤ (h+1)*k by rw [Nat.succ_mul]; omega)
    have hge : (j.factorial:ℝ) ≤ h.factorial := by exact_mod_cast Nat.factorial_le hr
    have h1 : (k:ℝ)^2*|numeratorDiff k d (n+1-t)| ≤ 1/(2*(h.factorial:ℝ)) := by
      apply (mul_le_mul_of_nonneg_left hbound hpos.le).trans_eq
      field_simp [hp.ne',hf.ne'] <;> ring
    exact h1.trans (one_div_le_one_div_of_le (by positivity) (by linarith))
  next =>
    have hh : 1 ≤ h := (Nat.le_div_iff_mul_le hk0).mpr (by dsimp [z]; simp; omega)
    have hv := numerator_block_atom_size hd hk hh hm
    rw [←he] at hv
    have hh' : (1:ℝ) ≤ h.factorial := by exact_mod_cast Nat.factorial_pos h
    have hu := mul_le_mul_of_nonneg_left hv hpos.le
    apply hu.trans
    rw [mul_one_div,div_le_one (by positivity)]
    exact le_mul_of_one_le_left hpos.le hh'

#print axioms regular_numerator_strict_bin
end OpenMathResearch.LongCycleExcedances
