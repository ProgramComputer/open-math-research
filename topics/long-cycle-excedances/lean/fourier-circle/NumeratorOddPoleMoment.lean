import NumeratorPoleVolume
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open scoped BigOperators Real

def numeratorPole (s : ℝ) (l : ℤ) : ℂ :=
  (s : ℂ) + (2 * (l : ℂ) + 1) * π * Complex.I

def numeratorRadius (s : ℝ) : ℝ := Real.sqrt (s^2+π^2)

theorem numeratorRadius_pos (s : ℝ) : 0 < numeratorRadius s :=
  Real.sqrt_pos.2 (by positivity)

private theorem pole_norm_sq (s : ℝ) (l : ℤ) :
    ‖numeratorPole s l‖^2 = s^2 + ((2*(l:ℝ)+1)*π)^2 := by
  rw [Complex.sq_norm]
  dsimp only [numeratorPole]
  simp [Complex.normSq_apply,Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,pow_two]

private theorem pole_norm_on_half (s : ℝ) (i : ℕ) :
    ‖numeratorPole s (-(i:ℤ)-1)‖ = ‖numeratorPole s i‖ := by
  apply (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) (by norm_num : 2 ≠ 0)).mp
  rw [pole_norm_sq,pole_norm_sq]
  push_cast
  ring

private theorem pole_norm_succ (s : ℝ) (i : ℕ) :
    ‖numeratorPole s ((i+1:ℕ):ℤ)‖ / numeratorRadius s =
      Real.sqrt (1+4*((i+1:ℕ):ℝ)*(i+2:ℕ)*(π/numeratorRadius s)^2) := by
  have hr := numeratorRadius_pos s
  have hrs : (numeratorRadius s)^2=s^2+π^2 := Real.sq_sqrt (by positivity)
  apply (pow_left_inj₀ (by positivity) (Real.sqrt_nonneg _) (by norm_num : 2 ≠ 0)).mp
  rw [Real.sq_sqrt (by positivity),div_pow,pole_norm_sq]
  have hh : (numeratorRadius s)^2 ≠ 0 := pow_ne_zero _ hr.ne'
  field_simp [hh,hr.ne']
  linear_combination -hrs

private theorem pole_moment_succ (s : ℝ) (j i : ℕ) :
    (numeratorRadius s/‖numeratorPole s ((i+1:ℕ):ℤ)‖)^j =
      (1+4*((i+1:ℕ):ℝ)*(i+2:ℕ)*(π/numeratorRadius s)^2)^(-(j:ℝ)/2) := by
  let x : ℝ := 1+4*((i+1:ℕ):ℝ)*(i+2:ℕ)*(π/numeratorRadius s)^2
  have hx : 0 ≤ x := by dsimp [x]; positivity
  change _ = x^(-(j:ℝ)/2)
  rw [← inv_div, pole_norm_succ]
  change ((Real.sqrt x)⁻¹)^j = x^(-(j:ℝ)/2)
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hx, ← Real.rpow_mul_natCast hx]
  congr 1
  ring

private theorem pole_norm_zero (s : ℝ) :
    ‖numeratorPole s 0‖ = numeratorRadius s := by
  apply (pow_left_inj₀ (norm_nonneg _) (numeratorRadius_pos s).le (by norm_num : 2 ≠ 0)).mp
  rw [pole_norm_sq,show (numeratorRadius s)^2 = s^2+π^2 from Real.sq_sqrt (by positivity)]
  norm_num

/-- The moment estimate for all signed odd poles of the actual logistic log,
including both nearest poles with the exact normalization. -/
theorem numerator_actual_pole_moment (s : ℝ) {j : ℕ} (hj : 2 ≤ j) :
    let f : ℤ → ℝ := fun l => (numeratorRadius s/‖numeratorPole s l‖)^j
    Summable f ∧ (∑' l, f l) ≤
      2 + 9/(4*(π/numeratorRadius s)*Real.sqrt j) := by
  dsimp only
  let f : ℤ → ℝ := fun l => (numeratorRadius s/‖numeratorPole s l‖)^j
  have hf0 : f 0 = 1 := by
    dsimp [f]
    rw [pole_norm_zero, div_self (numeratorRadius_pos s).ne', one_pow]
  have hfhalf (i : ℕ) : f (-(i:ℤ)-1) = f i := by
    dsimp only [f]
    rw [pole_norm_on_half]
  have hS : 0 < π/numeratorRadius s := div_pos Real.pi_pos (numeratorRadius_pos s)
  have hm := normalized_pole_moment hS hj
  change Summable f ∧ _
  have hshift (i : ℕ) : f ((i+1:ℕ):ℤ) =
      (1+4*((i+1:ℕ):ℝ)*(i+2:ℕ)*(π/numeratorRadius s)^2)^(-(j:ℝ)/2) :=
    pole_moment_succ s j i
  have hs : Summable (fun i : ℕ => f ((i+1:ℕ):ℤ)) := by
    simp_rw [hshift]
    exact hm.1
  have hpos : Summable (fun i : ℕ => f i) := (summable_nat_add_iff 1).1 hs
  have hneg : Summable (fun i : ℕ => f (-(i:ℤ)-1)) := by simp_rw [hfhalf]; exact hpos
  have hneg' : Summable (fun i : ℕ => f (-((i:ℤ)+1))) := by
    simpa only [neg_add_rev,sub_eq_add_neg,add_comm] using hneg
  refine ⟨hpos.of_nat_of_neg_add_one hneg', ?_⟩
  change (∑' l, f l) ≤ _
  rw [tsum_of_nat_of_neg_add_one hpos hneg']
  simp_rw [show ∀ i : ℕ, -((i:ℤ)+1) = -(i:ℤ)-1 from fun _ => by ring, hfhalf]
  rw [hpos.tsum_eq_zero_add]
  simp only [Nat.cast_zero,hf0]
  have heq :
      (∑' i : ℕ, f ((i+1:ℕ):ℤ)) =
        ∑' i : ℕ, (1+4*((i+1:ℕ):ℝ)*(i+2:ℕ)*(π/numeratorRadius s)^2)^(-(j:ℝ)/2) :=
    tsum_congr hshift
  rw [heq]
  linarith only [hm.2]

#print axioms numerator_actual_pole_moment
end OpenMathResearch.LongCycleExcedances
