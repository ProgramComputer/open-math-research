import HighHeightLogSource
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset

def expWithoutConstantPrefix (k : ℕ) (z : ℂ) : ℂ :=
  ∑ i ∈ range (k-1), z^(i+1)/((i+1).factorial : ℂ)

def prefixFrequency (k : ℕ) (s : ℝ) (z : ℂ) (a : ℕ) : ℂ :=
  frequencyWeight s a * expWithoutConstantPrefix k (((a+1:ℕ):ℂ)*z)

/-- A finite log polynomial has the positive-frequency expansion whenever its
coefficient moments agree. The hypothesis is the published cutoff coefficient
moment, including degree one. -/
theorem prefix_frequency_hasSum (k : ℕ) (s : ℝ) (g : ℕ → ℂ) (z : ℂ)
    (hG : ∀ i ∈ range (k-1),
      HasSum (fun a : ℕ => ((-Real.exp (-s):ℝ):ℂ)^(a+1)*((a+1:ℕ):ℂ)^i)
        (-(g (i+1))*((i+1).factorial:ℂ))) :
    HasSum (prefixFrequency k s z)
      (∑ i ∈ range (k-1), g (i+1)*z^(i+1)) := by
  have hterm (i : ℕ) (hi : i ∈ range (k-1)) :
      HasSum (fun a : ℕ => frequencyWeight s a *
        ((((a+1:ℕ):ℂ)*z)^(i+1)/((i+1).factorial:ℂ))) (g (i+1)*z^(i+1)) := by
    have h := (hG i hi).mul_right (-z^(i+1)/((i+1).factorial:ℂ))
    have hn : ((i+1).factorial:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (i+1)
    convert h using 1
    · funext a
      have hA : ((a+1:ℕ):ℂ) ≠ 0 := by exact_mod_cast (by omega : a+1≠0)
      rw [frequencyWeight, mul_pow, pow_succ (((a+1:ℕ):ℂ)) i]
      have hA' : (a:ℂ)+1 ≠ 0 := by simpa only [Nat.cast_add,Nat.cast_one] using hA
      field_simp [hA, hA', hn]      ring
    · field_simp [hn]      ring
  have h := hasSum_sum hterm
  convert h using 1
  funext a
  unfold prefixFrequency expWithoutConstantPrefix
  rw [mul_sum]

#print axioms prefix_frequency_hasSum
end OpenMathResearch.LongCycleExcedances
