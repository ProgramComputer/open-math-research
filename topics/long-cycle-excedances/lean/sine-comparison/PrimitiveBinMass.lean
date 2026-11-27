import LiteralBin
import Mathlib.Algebra.BigOperators.Intervals

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset

def primitiveDegrees (k N i : ℕ) := (Icc k N).filter (fun s => degreeBin k s=i)

theorem degreeBin_iff {k s i : ℕ} (hk : 0 < k) (hi : 0 < i) :
    degreeBin k s=i ↔ (i-1)*k < 4*s ∧ 4*s ≤ i*k := by
  unfold degreeBin
  rw [Nat.div_eq_iff hk]
  have h1 : (i-1)*k+k=i*k := by
    calc
      _ = (i-1+1)*k := by rw [Nat.add_mul,one_mul]
      _ = _ := by rw [Nat.sub_add_cancel hi]
  have h2 : (i+1)*k=i*k+k := by rw [Nat.add_mul,one_mul]
  omega

theorem primitiveDegrees_four {k N : ℕ} (hk : 0 < k) (hN : k ≤ N) :
    primitiveDegrees k N 4 = {k} := by
  ext s
  simp only [primitiveDegrees,mem_filter,mem_Icc,mem_singleton,degreeBin_iff hk (by decide : 0 < 4)]
  norm_num
  omega

/-- The factor k times the linear-bin mass at the isolated cutoff atom. -/
theorem primitive_atom_mass {k N : ℕ} (hk : 0 < k) (hN : k ≤ N)
    (b : ℕ → ℝ) (hb : b k=1/(k:ℝ)) :
    (k:ℝ)*(∑ s ∈ primitiveDegrees k N 4, |b s|) = 1 := by
  have hkR : (0:ℝ)<k := by exact_mod_cast hk
  rw [primitiveDegrees_four hk hN,sum_singleton,hb,abs_of_nonneg (by positivity),
    mul_one_div,div_self hkR.ne']

theorem primitive_bin_card {k N i : ℕ} (hk : 0 < k) (hi : 0 < i) :
    ((primitiveDegrees k N i).card:ℝ) ≤ (k:ℝ)/4+1 := by
  let l := ((i-1)*k)/4
  let u := (i*k)/4
  have hsub : primitiveDegrees k N i ⊆ Ioc l u := by
    intro s hs
    have h := (degreeBin_iff hk hi).mp (mem_filter.mp hs).2
    exact mem_Ioc.mpr ⟨(Nat.div_lt_iff_lt_mul (by decide : 0 < 4)).2 (by simpa [mul_comm] using h.1),
      (Nat.le_div_iff_mul_le (by decide : 0 < 4)).2 (by simpa [mul_comm] using h.2)⟩
  have hcard := card_le_card hsub
  rw [Nat.card_Ioc] at hcard
  have hu := Nat.div_add_mod (i*k) 4
  have hl := Nat.div_add_mod ((i-1)*k) 4
  have hrem := Nat.mod_lt ((i-1)*k) (by decide : 0 < 4)
  have h1 : (i-1)*k+k=i*k := by
    calc
      _ = (i-1+1)*k := by rw [Nat.add_mul,one_mul]
      _ = _ := by rw [Nat.sub_add_cancel hi]
  have htot : 4*(primitiveDegrees k N i).card ≤ k+4 := by
    dsimp [l,u] at hcard
    omega
  have hreal : 4*((primitiveDegrees k N i).card:ℝ) ≤ (k:ℝ)+4 := by exact_mod_cast htot
  linarith

/-- All bins beyond the first two blocks use the integer pointwise factorial bound.
The index j is floor((i-1)/4), including bins with integral upper endpoint. -/
theorem primitive_factorial_bin_mass {k N i : ℕ} (hk : 0 < k) (hi : 9 ≤ i)
    (b : ℕ → ℝ) (hblock : ∀ j s : ℕ, 2 ≤ j → j*k < s → s ≤ (j+1)*k →
      |b s| ≤ 1/(2*(j.factorial:ℝ)*(k:ℝ)^2)) :
    (k:ℝ)*(∑ s ∈ primitiveDegrees k N i, |b s|) ≤
      (1/4+1/(k:ℝ))/(2*(((i-1)/4).factorial:ℝ)) := by
  let j := (i-1)/4
  have hj : 2 ≤ j := by dsimp [j]; omega
  have hkR : (0:ℝ)<k := by exact_mod_cast hk
  have hjR : (0:ℝ)<j.factorial := by exact_mod_cast Nat.factorial_pos j
  have hrel (s : ℕ) (hs : s ∈ primitiveDegrees k N i) :
      |b s| ≤ 1/(2*(j.factorial:ℝ)*(k:ℝ)^2) := by
    have hb := (degreeBin_iff hk (by omega : 0 < i)).mp (mem_filter.mp hs).2
    have ha : 4*j ≤ i-1 := by dsimp [j]; omega
    have hc : i ≤ 4*(j+1) := by dsimp [j]; omega
    have hd := Nat.mul_le_mul_right k ha
    have he := Nat.mul_le_mul_right k hc
    rw [show 4*j*k=4*(j*k) by ring] at hd
    rw [show 4*(j+1)*k=4*((j+1)*k) by ring] at he
    exact hblock j s hj (by omega) (by omega)
  have nn : 0 ≤ 1/(2*(j.factorial:ℝ)*(k:ℝ)^2) := by positivity
  calc
    _ ≤ (k:ℝ)*(∑ _s ∈ primitiveDegrees k N i, 1/(2*(j.factorial:ℝ)*(k:ℝ)^2)) :=
      mul_le_mul_of_nonneg_left (sum_le_sum hrel) hkR.le
    _ = (k:ℝ)*((primitiveDegrees k N i).card:ℝ)*(1/(2*(j.factorial:ℝ)*(k:ℝ)^2)) := by
      rw [sum_const,nsmul_eq_mul,←mul_assoc]
    _ ≤ (k:ℝ)*((k:ℝ)/4+1)*(1/(2*(j.factorial:ℝ)*(k:ℝ)^2)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (primitive_bin_card hk (by omega : 0 < i)) hkR.le) nn
    _ = _ := by change _ = (1/4+1/(k:ℝ))/(2*(j.factorial:ℝ)); field_simp <;> ring

#print axioms degreeBin_iff
#print axioms primitive_atom_mass
#print axioms primitive_factorial_bin_mass
end OpenMathResearch.LongCycleExcedances
