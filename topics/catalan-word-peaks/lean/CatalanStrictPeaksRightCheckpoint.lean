import CatalanStrictPeaksPhaseOrder

/-!
# The first checkpoint separates the right edge

At the transition value −11/16, every root after the first is at least
the inverse squared row length away. This uses the actual outer
checkpoint geometry and leaves the first root to be compared.
-/

namespace CatalanStrictPeaks.CutGeometry

open Real Set OpenMathResearch.OrientedNegativeInterlace

private theorem scale_le_transition {d : ℝ} (hd : 0 < d) (hD : d ≤ 1) :
    scale d ≤ scale 1 * ((1 + d) / 2) := by
  have hp : 0 < 1 + 2 * d := by positivity
  have hf : d / (1 + 2 * d) ≤ 1 / 3 :=
    (div_le_iff₀ hp).2 (by linarith)
  have hr : sqrt (1 + 2 * d) ≤ sqrt 3 := sqrt_le_sqrt (by linarith)
  rw [scale_eq_product hd]
  calc
    _ ≤ 2 * (1 / 3 : ℝ) ^ 2 * (1 + d) * sqrt 3 := by gcongr
    _ = _ := by rw [scale_eq_product (by norm_num : (0 : ℝ) < 1)]; norm_num; ring

/-- The modulus increases by at least the decrease of the cosine from
its value at the transition. -/
theorem modulus_sub_transition_ge_one_sub_cos {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) (π / 2)) :
    1 - cos θ ≤ modulus θ - 11 / 16 := by
  let d := cos θ
  have ⟨hd, hD⟩ : 0 < d ∧ d < 1 := cosine_in_unit hθ
  have hc : 0 < scale d := scale_pos (d := d) hd
  have ht := scale_pos (d := 1) (by norm_num)
  have hcsq : scale d ^ 2 ≤ (4 / 27 : ℝ) * (1 + d) ^ 2 := calc
    _ ≤ (scale 1 * ((1 + d) / 2)) ^ 2 :=
      (sq_le_sq₀ hc.le (by positivity)).2 (scale_le_transition hd hD.le)
    _ = _ := by rw [mul_pow, scale_one_sq]; ring
  have hrec : 1 / ((4 / 27 : ℝ) * (1 + d) ^ 2) ≤ 1 / (scale d ^ 2) :=
    one_div_le_one_div_of_le (pow_pos hc 2) hcsq
  have hpos : 0 < (1 + d) ^ 2 := by positivity
  have hdd : d ^ 2 ≤ d := by nlinarith [mul_nonneg hd.le (sub_nonneg.mpr hD.le)]
  have hcoeff : (1 + d) ^ 2 ≤ (27 / 16 : ℝ) * (3 + d) := by nlinarith
  have hdsub : 0 ≤ 1 - d := sub_nonneg.mpr hD.le
  have hnum := mul_le_mul_of_nonneg_right hcoeff hdsub
  change 1 - d ≤ (scale d ^ 2)⁻¹ - 1 - 11 / 16
  calc
    _ ≤ (27 / 16 : ℝ) * (1 - d) * (3 + d) / (1 + d) ^ 2 :=
      (le_div_iff₀ hpos).2 (by
        calc
          _ = (1 + d) ^ 2 * (1 - d) := by ring
          _ ≤ (27 / 16 : ℝ) * (3 + d) * (1 - d) := hnum
          _ = _ := by ring)
    _ = 1 / ((4 / 27 : ℝ) * (1 + d) ^ 2) - 1 - 11 / 16 := by
      field_simp [(show 0 < 1 + d by positivity).ne']
      ring
    _ ≤ _ := by
      rw [inv_eq_one_div]
      exact sub_le_sub_right (sub_le_sub_right hrec 1) (11 / 16)

private theorem one_sub_cos_ge_inv_sq {θ : ℝ} {n : ℕ} (hθ : θ ∈ Ioo (0 : ℝ) (π / 2))
    (hn : 150 ≤ n) (hangle : (2 : ℝ) / (n : ℝ) ≤ θ) :
    (1 : ℝ) / (n : ℝ) ^ 2 < 1 - cos θ := by
  let u := (1 : ℝ) / (n : ℝ)
  have hnR : (150 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnP : 0 < (n : ℝ) := by linarith
  have hu : 0 < u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := (div_le_one hnP).2 (by linarith)
  have huθ : u ≤ θ / 2 := by
    have heq : (2 : ℝ) / (n : ℝ) = 2 * u := by dsimp [u]; ring
    rw [heq] at hangle
    linarith
  have hsin₁ : (3 / 4 : ℝ) * u ≤ sin (θ / 2) := calc
    _ ≤ u - u ^ 3 / 4 := by
      nlinarith [mul_le_of_le_one_left (sq_nonneg u) hu1,
        mul_le_of_le_one_right hu.le hu1]
    _ ≤ sin u := (sin_gt_sub_cube hu hu1).le
    _ ≤ _ := sin_le_sin_of_le_of_le_pi_div_two (by linarith [pi_pos]) (by linarith [hθ.2, pi_pos]) huθ
  have hsin₂ : ((3 / 4 : ℝ) * u) ^ 2 ≤ sin (θ / 2) ^ 2 :=
    (sq_le_sq₀ (by positivity) ((by positivity : (0 : ℝ) ≤ (3 / 4 : ℝ) * u).trans hsin₁)).2 hsin₁
  have hC := cos_two_mul (θ / 2)
  rw [show 2 * (θ / 2) = θ by ring] at hC
  have h : (1 : ℝ) / (n : ℝ) ^ 2 = u ^ 2 := by dsimp [u]; rw [div_pow, one_pow]
  rw [h]
  nlinarith [sin_sq_add_cos_sq (θ / 2), pow_pos hu 2]

private theorem checkpoint_modulus_gap {θ : ℝ} {n : ℕ} (hn : 150 ≤ n)
    (hθ : θ ∈ Ioo (0 : ℝ) (π / 2)) (hfirst : π ≤ checkpointPhase n θ) :
    (11 / 16 : ℝ) + 1 / (n : ℝ) ^ 2 < modulus θ := by
  have hγ := (phaseCorrection_bounds ⟨hθ.1.le, hθ.2.le⟩).1
  unfold checkpointPhase at hfirst
  have hnR : (150 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnP : 0 < (n : ℝ) := by linarith
  have hangle : (2 : ℝ) / (n : ℝ) ≤ θ :=
    (div_le_iff₀ hnP).2 (by linarith [pi_gt_three])
  linarith [one_sub_cos_ge_inv_sq hθ hn hangle, modulus_sub_transition_ge_one_sub_cos hθ]

/-- The first positive phase level has modulus at least \(11/16+1/n^2\). -/
theorem first_checkpoint_modulus_gap {θ : ℝ} {n : ℕ} (hn : 150 ≤ n)
    (hθ : θ ∈ Ioo (0 : ℝ) (π / 2)) (hfirst : checkpointPhase n θ = π) :
    (11 / 16 : ℝ) + 1 / (n : ℝ) ^ 2 ≤ modulus θ :=
  (checkpoint_modulus_gap hn hθ hfirst.ge).le

/-- All roots after the rightmost one are separated from the transition
value by at least the inverse square of the row length. -/
theorem roots_after_first_modulus_gap {n : ℕ} (hn : 150 ≤ n) :
    ∃ roots : Fin (rowDegree n) → ℝ, CompleteNegativeRoots (C n) roots ∧
      ∀ i, 0 < i.val → (11 / 16 : ℝ) + 1 / (n : ℝ) ^ 2 < roots i := by
  obtain ⟨roots, hroots, hmiddle⟩ := middle_roots_between_checkpoints hn
  let secondRoot : Fin (rowDegree n) := ⟨1, by unfold rowDegree; omega⟩
  have h₂ : 0 < secondRoot.val := by change (0 : ℕ) < 1; decide
  have h₃ : secondRoot.val + 1 < rowDegree n := by dsimp [secondRoot, rowDegree]; omega
  obtain ⟨θ, hθ, heq, hphase, _⟩ := hmiddle secondRoot h₂ h₃
  have hphase' : π ≤ checkpointPhase n θ := by
    rw [show secondRoot.val = 1 from rfl, Nat.cast_one, one_mul] at hphase
    exact hphase.le
  have hgap : (11 / 16 : ℝ) + 1 / (n : ℝ) ^ 2 < roots secondRoot := by
    rw [heq]
    exact checkpoint_modulus_gap hn hθ hphase'
  refine ⟨roots, hroots, ?_⟩
  intro i hi
  have hi' : secondRoot ≤ i := by change 1 ≤ i.val; omega
  exact hgap.trans_le (hroots.2.1.monotone hi')

end CatalanStrictPeaks.CutGeometry
