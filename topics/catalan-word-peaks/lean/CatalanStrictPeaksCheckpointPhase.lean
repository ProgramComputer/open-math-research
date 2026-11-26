import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.Real.Pi.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The Catalan phase and the interior estimates

The arguments in the correction are taken on the real principal arctangent.
The bounds apply to the whole band between the first and last phase levels.
-/

namespace CatalanStrictPeaks.CutGeometry

open Real

/-- The phase correction coming from the three near amplitude factors. -/
noncomputable def phaseCorrection (θ : ℝ) : ℝ :=
  θ / 2 - π / 4 + (1 / 2) * arctan (sin θ / (1 + 2 * cos θ)) +
    2 * arctan (cos θ * sin θ / (1 + cos θ - cos θ ^ 2))

/-- The phase of the leading near-ray contribution, with its sign reversed. -/
noncomputable def checkpointPhase (n : ℕ) (θ : ℝ) : ℝ :=
  (n : ℝ) * θ - phaseCorrection θ

private theorem phaseCorrection_den_pos {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) (π / 2)) :
    0 < 1 + 2 * cos θ ∧ 1 ≤ 1 + cos θ - cos θ ^ 2 := by
  have hcos : 0 ≤ cos θ := cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, pi_pos], hθ.2⟩
  exact ⟨by positivity, by nlinarith [mul_nonneg hcos (sub_nonneg.mpr (cos_le_one θ))]⟩

private theorem phaseCorrection_arguments {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) (π / 2)) :
    sin θ / (1 + 2 * cos θ) ∈ Set.Icc (0 : ℝ) 1 ∧
      cos θ * sin θ / (1 + cos θ - cos θ ^ 2) ∈ Set.Icc (0 : ℝ) (1 / 2) := by
  have hsin : 0 ≤ sin θ := sin_nonneg_of_mem_Icc ⟨hθ.1, hθ.2.trans (by linarith [pi_pos])⟩
  have hcos : 0 ≤ cos θ := cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, pi_pos], hθ.2⟩
  obtain ⟨hA, hB⟩ := phaseCorrection_den_pos hθ
  have hB0 : 0 < 1 + cos θ - cos θ ^ 2 := zero_lt_one.trans_le hB
  refine ⟨⟨div_nonneg hsin hA.le, (div_le_one hA).2 ?_⟩,
    ⟨div_nonneg (mul_nonneg hcos hsin) hB0.le, (div_le_iff₀ hB0).2 ?_⟩⟩
  · linarith [sin_le_one θ]
  · have hprod : cos θ * sin θ ≤ 1 / 2 := by
      nlinarith [sin_sq_add_cos_sq θ, sq_nonneg (sin θ - cos θ)]
    linarith

/-- The phase correction satisfies the lower and upper bounds of the paper. -/
theorem phaseCorrection_bounds {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) (π / 2)) :
    -(π / 4) ≤ phaseCorrection θ ∧ phaseCorrection θ ≤ π / 8 + 1 := by
  obtain ⟨hA, hB⟩ := phaseCorrection_arguments hθ
  have hA0 := arctan_le_arctan hA.1
  have hA1 := arctan_le_arctan hA.2
  have hB0 := arctan_le_arctan hB.1
  have hB1 := arctan_le_arctan hB.2
  have hhalf0 : 0 < arctan (1 / 2) := by
    rw [← arctan_zero]
    exact arctan_lt_arctan (by norm_num)
  have hhalf : arctan (1 / 2) ≤ 1 / 2 := by
    have h := lt_tan hhalf0 (arctan_lt_pi_div_two _)
    rw [tan_arctan] at h
    exact h.le
  rw [arctan_zero] at hA0 hB0
  rw [arctan_one] at hA1
  unfold phaseCorrection
  exact ⟨by linarith [hθ.1], by linarith [hθ.2]⟩

theorem phaseCorrection_zero : phaseCorrection 0 = -(π / 4) := by
  simp [phaseCorrection, arctan_zero]

theorem phaseCorrection_pi_div_two : phaseCorrection (π / 2) = π / 8 := by
  simp [phaseCorrection, arctan_zero, arctan_one]
  ring

private theorem radial_sine_bound {n : ℕ} {x a : ℝ} (hn : 150 ≤ n)
    (ha : a ∈ Set.Ioc (0 : ℝ) 4) (hx : x ≤ π / 2) (hangle : a ≤ (n : ℝ) * x) :
    (399 / 400 : ℝ) * a < (n : ℝ) * sin x := by
  have hnR : (150 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnP : 0 < (n : ℝ) := by linarith
  let t := a / (n : ℝ)
  have ht : 0 < t := div_pos ha.1 hnP
  have ht' : t ≤ 1 / 10 := by
    exact (div_le_iff₀ hnP).2 (by linarith [ha.2])
  have htx : t ≤ x := by
    exact (div_le_iff₀ hnP).2 (by simpa only [mul_comm] using hangle)
  have hsin := sin_le_sin_of_le_of_le_pi_div_two (by linarith [pi_pos]) hx htx
  have hTaylor := sin_gt_sub_cube ht (by linarith : t ≤ 1)
  have hpow : t ^ 2 ≤ (1 / 10 : ℝ) ^ 2 := (sq_le_sq₀ ht.le (by norm_num)).2 ht'
  have hlin : (399 / 400 : ℝ) * t ≤ t - t ^ 3 / 4 := by
    nlinarith [mul_le_mul_of_nonneg_left hpow ht.le]
  have hm := mul_lt_mul_of_pos_left (hlin.trans_lt (hTaylor.trans_le hsin)) hnP
  have hta : (n : ℝ) * t = a := by dsimp [t]; field_simp
  nlinarith

/-- At every point between the first and last interior phase levels, the
cosine and sine satisfy the quantitative radial premises. -/
theorem checkpointPhase_interior {n : ℕ} {θ : ℝ} (hn : 150 ≤ n)
    (hθ : θ ∈ Set.Icc (0 : ℝ) (π / 2))
    (hfirst : π ≤ checkpointPhase n θ)
    (hlast : checkpointPhase n θ ≤ ((((n - 1) / 2 : ℕ) : ℝ) - 1) * π) :
    (29 / 10 : ℝ) ≤ (n : ℝ) * cos θ ∧ (2 : ℝ) ≤ (n : ℝ) * sin θ := by
  obtain ⟨hγlo, hγhi⟩ := phaseCorrection_bounds hθ
  unfold checkpointPhase at hfirst hlast
  have hθn : (9 / 4 : ℝ) ≤ (n : ℝ) * θ := by linarith [pi_gt_three]
  have hm : 2 * ((n - 1) / 2) + 1 ≤ n := by omega
  have hmR : 2 * ((((n - 1) / 2 : ℕ) : ℝ)) + 1 ≤ (n : ℝ) := by exact_mod_cast hm
  have hlast' : (n : ℝ) * θ - phaseCorrection θ ≤ ((n : ℝ) / 2 - 3 / 2) * π :=
    hlast.trans (mul_le_mul_of_nonneg_right (by linarith) pi_pos.le)
  have hΔn : (25 / 8 : ℝ) ≤ (n : ℝ) * (π / 2 - θ) := by
    nlinarith [pi_gt_three]
  have hc := radial_sine_bound hn (a := 25 / 8) (by constructor <;> norm_num)
    (by linarith [hθ.1]) hΔn
  have hs := radial_sine_bound hn (a := 9 / 4) (by constructor <;> norm_num) hθ.2 hθn
  rw [sin_pi_div_two_sub] at hc
  constructor <;> linarith

/-- The explicit correction is continuous up to both phase endpoints. -/
theorem continuousOn_phaseCorrection : ContinuousOn phaseCorrection (Set.Icc (0 : ℝ) (π / 2)) := by
  have hcos : ContinuousOn cos (Set.Icc (0 : ℝ) (π / 2)) := continuous_cos.continuousOn
  have hsin : ContinuousOn sin (Set.Icc (0 : ℝ) (π / 2)) := continuous_sin.continuousOn
  have hA : ContinuousOn (fun θ : ℝ => 1 + 2 * cos θ) (Set.Icc (0 : ℝ) (π / 2)) :=
    continuousOn_const.add (continuousOn_const.mul hcos)
  have hB : ContinuousOn (fun θ : ℝ => 1 + cos θ - cos θ ^ 2) (Set.Icc (0 : ℝ) (π / 2)) :=
    (continuousOn_const.add hcos).sub (hcos.pow 2)
  have hA' := continuous_arctan.comp_continuousOn
    (hsin.div hA (fun _ hθ => (phaseCorrection_den_pos hθ).1.ne'))
  have hB' := continuous_arctan.comp_continuousOn
    ((hcos.mul hsin).div hB (fun _ hθ => (zero_lt_one.trans_le (phaseCorrection_den_pos hθ).2).ne'))
  unfold phaseCorrection
  exact (((continuousOn_id.div_const 2).sub continuousOn_const).add
    (continuousOn_const.mul hA')).add (continuousOn_const.mul hB')

theorem continuousOn_checkpointPhase (n : ℕ) :
    ContinuousOn (checkpointPhase n) (Set.Icc (0 : ℝ) (π / 2)) :=
  (continuousOn_const.mul continuousOn_id).sub continuousOn_phaseCorrection

end CatalanStrictPeaks.CutGeometry
