import RepositoryMinorPoles
import SmallRadius
import UniformHighDegreeLattice

set_option autoImplicit false
noncomputable section
namespace RepositoryQuotientAudit
open OpenMathResearch.LongCycleExcedances Finset Real

private theorem full_pole_square (x : ℝ) (j : ℤ) :
    ‖coherentPole x j‖^2 = x^2 + ((2*(j:ℝ)+1)*π)^2 := by
  rw [Complex.sq_norm,Complex.normSq_apply]
  simp [coherentPole,Complex.add_re,Complex.add_im,Complex.mul_I_re,Complex.mul_I_im,Complex.mul_re,Complex.mul_im]
  ring

theorem enclosed_poles_empty_of_small {k : ℕ} (hk : 7 ≤ k) {x : ℝ} (hx : 0 ≤ x)
    (hscale : x ≤ 10*√(k:ℝ)) (i : ℕ) :
    ‖coherentPole x 0‖*(1+1/(50*(k:ℝ))) < ‖coherentPole x ((i+1:ℕ):ℤ)‖ := by
  let j := ((i+1:ℕ):ℤ)
  have hp : (3:ℝ) ≤ 2*(j:ℝ)+1 := by dsimp [j]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) i]
  exact small_log_radius_excludes hk hx hscale (norm_nonneg _) hp
    (by simpa using full_pole_square x 0) (full_pole_square x j)

theorem all_angle_enclosed_minor_poles_le_fifth {n k : ℕ} (hk : 7 ≤ k) {x : ℝ}
    (hx : 0 ≤ x) (hm : 1 ≤ (n:ℝ)*(π/‖coherentPole x 0‖)^2)
    (s : Finset ℕ) (henc : ∀ i ∈ s, ‖coherentPole x ((i+1:ℕ):ℤ)‖ ≤
      ‖coherentPole x 0‖*(1+1/(50*(k:ℝ)))) :
    let T := coherentTilt k (-exp (-x))
    ∑ i ∈ s, (2*(i+1:ℕ)+1:ℝ) *
      (‖coherentPole x 0‖/‖coherentPole x ((i+1:ℕ):ℤ)‖)^n *
      ‖seriesValue T (coherentPole x ((i+1:ℕ):ℤ))/seriesValue T (coherentPole x 0)‖ ≤ 1/5 := by
  by_cases hl : 10*√(k:ℝ) ≤ x
  · exact actual_enclosed_minor_poles_le_fifth hk hl hm s henc
  · have he : s = ∅ := by
      ext i
      constructor
      · exact fun hi => False.elim (not_le_of_gt (enclosed_poles_empty_of_small hk hx (le_of_not_ge hl) i) (henc i hi))
      · simp
    subst s
    simp

/-- Absolute square mass of the whole pole lattice in the middle range. -/
theorem middle_coherent_square_sum (x : ℝ) {n : ℕ}
    (hm : 1 ≤ (n:ℝ)*(π/‖coherentPole x 0‖)^2) :
    let ρ (j : ℤ) := ‖coherentPole x 0‖ / ‖coherentPole x j‖
    Summable (fun j : ℤ => (ρ j)^2) ∧ (∑' j : ℤ, (ρ j)^2) ≤ 2+(n:ℝ)/2 := by
  let r := ‖coherentPole x 0‖
  let S := π/r
  let ρ (j : ℤ) := r/‖coherentPole x j‖
  have hr : 0 < r := coherentPole_near_pos x
  have hs : 0 < S := div_pos pi_pos hr
  have hzero : ρ 0 = 1 := div_self hr.ne'
  have hsym (i : ℕ) : ρ (-((i:ℤ)+1)) = ρ (i:ℤ) := by
    dsimp [ρ]; rw [coherentPole_conj,Complex.norm_conj]
  have hgeom (i : ℕ) :
      (ρ ((i+1:ℕ):ℤ))^2*(1+4*((i:ℝ)+1)*((i:ℝ)+2)*S^2) ≤ 1 := by
    let j := ((i+1:ℕ):ℤ)
    let W := ‖coherentPole x j‖
    have hW : 0 < W := hr.trans_le (coherentPole_near_le x j)
    have hr2 : r^2=x^2+π^2 := by simpa [r] using full_pole_square x 0
    have hW2 : W^2=x^2+((2*((i:ℝ)+1)+1)*π)^2 := by
      simpa [j,W] using full_pole_square x j
    change (r/W)^2*(1+4*((i:ℝ)+1)*((i:ℝ)+2)*(π/r)^2) ≤ 1
    have heq : r^2*(1+4*((i:ℝ)+1)*((i:ℝ)+2)*(π/r)^2) = W^2 := by
      rw [div_pow,mul_add,mul_one,←mul_assoc,←mul_div_assoc]
      field_simp [hr.ne']
      nlinarith only [hr2,hW2]
    rw [div_pow,div_mul_eq_mul_div,heq,div_self (pow_ne_zero _ hW.ne')]
  obtain ⟨hsm,hb⟩ := square_majorized_lattice (ell:=2) hs le_rfl ρ
    (fun j => div_nonneg hr.le (norm_nonneg _)) hzero hsym hgeom
  refine ⟨hsm,hb.trans (add_le_add (le_refl 2) ?_)⟩
  rw [div_le_div_iff₀ (by positivity : 0 < 2*S^2) (by norm_num : (0:ℝ)<2)]
  change 1 ≤ (n:ℝ)*S^2 at hm
  linarith

#print axioms enclosed_poles_empty_of_small
#print axioms all_angle_enclosed_minor_poles_le_fifth
#print axioms middle_coherent_square_sum
end RepositoryQuotientAudit
