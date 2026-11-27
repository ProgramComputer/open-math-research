import ExteriorIntegerSeam
import AngularGeometry

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real Set

theorem exterior_integer_seam_log_eq_angleCoordinate (n : ℕ) :
    exteriorIntegerSeamLog n = angleCoordinate (exteriorIntegerSeamAngle n) := by
  unfold exteriorIntegerSeamLog angleCoordinate
  rw [tan_eq_sin_div_cos, div_div_eq_mul_div, mul_div_assoc]

/-- The literal first grid sample has the exterior seam modulus and meets the middle threshold. -/
theorem integer_middle_first_sample {n : ℕ} (hn : 10000 ≤ n) :
    let θ := ((uniformJoinRank n+1:ℕ):ℝ)*π/(n:ℝ)
    0 < θ ∧ θ < π/2 ∧ 6/5 < (n:ℝ)*sin θ^2 ∧
      exp (-exteriorIntegerSeamLog n) = exp (-angleCoordinate θ) := by
  dsimp only
  have he : ((uniformJoinRank n+1:ℕ):ℝ)*π/(n:ℝ) = exteriorIntegerSeamAngle n := by
    simp only [exteriorIntegerSeamAngle, Nat.cast_add, Nat.cast_one]
  rw [he]
  obtain ⟨hp, hs, hsin, _⟩ := exterior_integer_seam_geometry hn
  exact ⟨hp, by linarith only [hs, pi_gt_three], hsin,
    congrArg (fun x => exp (-x)) (exterior_integer_seam_log_eq_angleCoordinate n)⟩

/-- The modulus increases with the angle, including the center endpoint. -/
theorem angular_modulus_strictMonoOn :
    StrictMonoOn (fun θ : ℝ => exp (-angleCoordinate θ)) (Ioc 0 (π/2)) := by
  intro a ha b hb hab
  have haπ : a < π := by linarith only [ha.2, pi_pos]
  have hbπ : b < π := by linarith only [hb.2, pi_pos]
  have hsa := sin_pos_of_pos_of_lt_pi ha.1 haπ
  have hsb := sin_pos_of_pos_of_lt_pi hb.1 hbπ
  have hcos := strictAntiOn_cos ⟨ha.1.le, haπ.le⟩ ⟨hb.1.le, hbπ.le⟩ hab
  have hsin := sin_le_sin_of_le_of_le_pi_div_two (by linarith only [ha.1, pi_pos]) hb.2 hab.le
  have hcb := cos_nonneg_of_mem_Icc ⟨by linarith only [hb.1, pi_pos], hb.2⟩
  have hquot : cos b/sin b < cos a/sin a := by
    apply (div_lt_div_iff₀ hsb hsa).2
    exact (mul_le_mul_of_nonneg_left hsin hcb).trans_lt (mul_lt_mul_of_pos_right hcos hsb)
  exact exp_lt_exp.mpr (neg_lt_neg (mul_lt_mul_of_pos_left hquot pi_pos))

theorem angular_modulus_lt_one {θ : ℝ} (hθ : θ ∈ Ioo 0 (π/2)) :
    exp (-angleCoordinate θ) < 1 := by
  have hπ : (0:ℝ) < π/2 := by positivity
  have hm := angular_modulus_strictMonoOn
    (show θ ∈ Ioc 0 (π/2) from ⟨hθ.1, hθ.2.le⟩)
    (show π/2 ∈ Ioc 0 (π/2) from ⟨hπ, le_rfl⟩) hθ.2
  simpa only [angleCoordinate, cos_pi_div_two, zero_div, mul_zero, neg_zero, exp_zero] using hm

/-- The strict threshold at the seam holds throughout the closed upper angular band. -/
theorem integer_middle_sine_sq {n : ℕ} (hn : 10000 ≤ n) {θ : ℝ}
    (hθ : exteriorIntegerSeamAngle n ≤ θ) (hhalf : θ ≤ π/2) :
    0 < θ ∧ 6/5 < (n:ℝ)*sin θ^2 := by
  obtain ⟨ha, hsmall, hs, _⟩ := exterior_integer_seam_geometry hn
  have hθpos := ha.trans_le hθ
  have hsa := sin_pos_of_pos_of_lt_pi ha (by linarith only [hsmall, pi_gt_three])
  have hsin := sin_le_sin_of_le_of_le_pi_div_two
    (by linarith only [ha, pi_pos]) hhalf hθ
  exact ⟨hθpos, hs.trans_le (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ hsa.le hsin 2) (Nat.cast_nonneg n))⟩

/-- A closed complete grid cell above the exterior ranks is contained in the angular band. -/
theorem integer_middle_grid_cell_bounds {n j : ℕ} (hn : 10000 ≤ n)
    (hj : uniformJoinRank n+1 ≤ j) (hcomplete : j+1 ≤ n/2) {θ : ℝ}
    (hθ : θ ∈ Icc ((j:ℝ)*π/n) (((j+1:ℕ):ℝ)*π/n)) :
    exteriorIntegerSeamAngle n ≤ θ ∧ θ ≤ π/2 := by
  have hnR : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hjR : (uniformJoinRank n:ℝ)+1 ≤ (j:ℝ) := by exact_mod_cast hj
  have h2 : (2:ℝ)*((j+1:ℕ):ℝ) ≤ (n:ℝ) := by
    exact_mod_cast (show 2*(j+1) ≤ n by omega)
  have hl : exteriorIntegerSeamAngle n ≤ (j:ℝ)*π/n :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hjR pi_pos.le) hnR.le
  have hr : ((j+1:ℕ):ℝ)*π/n ≤ π/2 := by
    apply (div_le_iff₀ hnR).2
    nlinarith only [mul_le_mul_of_nonneg_right h2 pi_pos.le]
  exact ⟨hl.trans hθ.1, hθ.2.trans hr⟩

theorem integer_middle_grid_cell_geometry {n j : ℕ} (hn : 10000 ≤ n)
    (hj : uniformJoinRank n+1 ≤ j) (hcomplete : j+1 ≤ n/2) {θ : ℝ}
    (hθ : θ ∈ Icc ((j:ℝ)*π/n) (((j+1:ℕ):ℝ)*π/n)) :
    0 < θ ∧ θ ≤ π/2 ∧ 6/5 < (n:ℝ)*sin θ^2 := by
  obtain ⟨hl, hr⟩ := integer_middle_grid_cell_bounds hn hj hcomplete hθ
  obtain ⟨hp, hs⟩ := integer_middle_sine_sq hn hl hr
  exact ⟨hp, hr, hs⟩

theorem exterior_integer_seam_modulus_le {n : ℕ} (hn : 10000 ≤ n) {θ : ℝ}
    (hl : exteriorIntegerSeamAngle n ≤ θ) (hu : θ ≤ π/2) :
    exp (-exteriorIntegerSeamLog n) ≤ exp (-angleCoordinate θ) := by
  obtain ⟨ha, hsmall, _, _⟩ := exterior_integer_seam_geometry hn
  rw [exterior_integer_seam_log_eq_angleCoordinate]
  exact angular_modulus_strictMonoOn.monotoneOn
    ⟨ha, by linarith only [hsmall, pi_gt_three]⟩ ⟨ha.trans_le hl, hu⟩ hl

/-- Even the left endpoint of the first complete grid cell is past the exterior cap. -/
theorem integer_middle_grid_cell_above_exterior {n j : ℕ} (hn : 10000 ≤ n)
    (hj : uniformJoinRank n+1 ≤ j) (hcomplete : j+1 ≤ n/2) {θ : ℝ}
    (hθ : θ ∈ Icc ((j:ℝ)*π/n) (((j+1:ℕ):ℝ)*π/n)) :
    (459/40:ℝ)*((uniformJoinRank n:ℝ)/((uniformJoinRank n:ℝ)+1))^n <
      exp (-angleCoordinate θ) := by
  obtain ⟨hl, hu⟩ := integer_middle_grid_cell_bounds hn hj hcomplete hθ
  exact (exterior_cap_before_integer_seam hn).trans_le (exterior_integer_seam_modulus_le hn hl hu)

theorem integer_middle_first_cell_complete {n : ℕ} (hn : 10000 ≤ n) :
    uniformJoinRank n+2 ≤ n/2 := by
  have hnR : (10000:ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0:ℝ) < n := by linarith only [hnR]
  have hθ : ((uniformJoinRank n:ℝ)+1)*π/n < 1/50 :=
    (exterior_integer_seam_geometry hn).2.1
  have hm := (div_lt_iff₀ hnpos).mp hθ
  have hthree := mul_le_mul_of_nonneg_left pi_gt_three.le
    (by positivity : 0 ≤ (uniformJoinRank n:ℝ)+1)
  have h2 : (2:ℝ)*((uniformJoinRank n:ℝ)+2) ≤ (n:ℝ) := by
    linarith only [hm, hthree, hnR]
  have hNat : 2*(uniformJoinRank n+2) ≤ n := by exact_mod_cast h2
  omega

#print axioms exterior_integer_seam_log_eq_angleCoordinate
#print axioms integer_middle_first_sample
#print axioms angular_modulus_strictMonoOn
#print axioms angular_modulus_lt_one
#print axioms integer_middle_sine_sq
#print axioms integer_middle_grid_cell_bounds
#print axioms integer_middle_grid_cell_geometry
#print axioms exterior_integer_seam_modulus_le
#print axioms integer_middle_grid_cell_above_exterior
#print axioms integer_middle_first_cell_complete
end OpenMathResearch.LongCycleExcedances
