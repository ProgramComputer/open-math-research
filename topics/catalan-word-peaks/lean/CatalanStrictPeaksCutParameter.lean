import CatalanStrictPeaksCutGeometry
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The Catalan cut parameter gives increasing negative-root moduli

The factorization and pointwise bounds use d, while the checkpoint signs
use the angle θ. The parameter conversion below supplies the exact
positivity and ordering hypotheses of the root count.
-/

namespace CatalanStrictPeaks.CutGeometry

open Set

/-- The product form used to compare the scale with its transition value. -/
theorem scale_eq_product {d : ℝ} (hd : 0 < d) :
    scale d = 2 * (d / (1 + 2 * d)) ^ 2 * (1 + d) * Real.sqrt (1 + 2 * d) := by
  let r := Real.sqrt (1 + 2 * d)
  have hr : 0 < r := Real.sqrt_pos.2 (by linarith)
  have hsq : r ^ 2 = 1 + 2 * d := Real.sq_sqrt (by linarith)
  change 2 * d ^ 2 * (1 + d) * (r⁻¹) ^ 3 = 2 * (d / (1 + 2 * d)) ^ 2 * (1 + d) * r
  rw [← hsq]
  field_simp
  ring

/-- The length parameter increases with the cosine. -/
theorem strictMonoOn_scale : StrictMonoOn scale (Ioi (0 : ℝ)) := by
  intro d hd e he hde
  have hd₀ : 0 < d := hd
  have he₀ : 0 < e := he
  have hpD : 0 < 1 + 2 * d := by linarith
  have hpE : 0 < 1 + 2 * e := by linarith
  have hf : d / (1 + 2 * d) < e / (1 + 2 * e) := by
    apply (div_lt_div_iff₀ hpD hpE).mpr
    nlinarith
  have hs : (d / (1 + 2 * d)) ^ 2 < (e / (1 + 2 * e)) ^ 2 :=
    (sq_lt_sq₀ (by positivity) (by positivity)).mpr hf
  rw [scale_eq_product hd₀, scale_eq_product he₀]
  have hpre : 2 * (d / (1 + 2 * d)) ^ 2 * (1 + d) * Real.sqrt (1 + 2 * d) <
      2 * (e / (1 + 2 * e)) ^ 2 * (1 + d) * Real.sqrt (1 + 2 * d) := by
    exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right
      (mul_lt_mul_of_pos_left hs (by norm_num)) (by positivity)) (Real.sqrt_pos.2 hpD)
  have hsqrt : Real.sqrt (1 + 2 * d) ≤ Real.sqrt (1 + 2 * e) :=
    Real.sqrt_le_sqrt (by linarith)
  exact hpre.trans_le (mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
    hsqrt (Real.sqrt_nonneg _) (by positivity))

/-- The square of the scale at the coalescing near pair. -/
theorem scale_one_sq : scale 1 ^ 2 = 16 / 27 := by
  have hr := radius_relation (d := 1) (by norm_num)
  norm_num at hr
  calc
    _ = 16 * (radius 1 ^ 2) ^ 3 := by unfold scale; ring
    _ = _ := by rw [show radius 1 ^ 2 = 1 / 3 by linarith]; norm_num

theorem scale_sq_lt_one {d : ℝ} (h₀ : 0 < d) (h₁ : d < 1) : (scale d) ^ 2 < 1 := by
  have hscale := scale_one_sq
  have hx : scale d < scale 1 := strictMonoOn_scale h₀ (by norm_num : (1 : ℝ) ∈ Ioi 0) h₁
  have hy := (sq_lt_sq₀ (scale_pos h₀).le (scale_pos (by norm_num : (0 : ℝ) < 1)).le).mpr hx
  linarith

theorem cosine_in_unit {θ : ℝ} (h : θ ∈ Ioo 0 (Real.pi / 2)) :
    0 < Real.cos θ ∧ Real.cos θ < 1 := by
  have hp := Real.pi_pos
  constructor
  · exact Real.cos_pos_of_mem_Ioo ⟨by linarith [h.1], h.2⟩
  · have hmem : θ ∈ Icc 0 Real.pi := ⟨h.1.le, by linarith [h.2]⟩
    have hzero : (0 : ℝ) ∈ Icc 0 Real.pi := ⟨le_rfl, hp.le⟩
    simpa using Real.strictAntiOn_cos hzero hmem h.1

/-- The positive modulus −t at the scaled value t = 1-c⁻². -/
noncomputable def modulus (θ : ℝ) : ℝ := ((scale (Real.cos θ)) ^ 2)⁻¹ - 1

theorem modulus_pos {θ : ℝ} (h : θ ∈ Ioo 0 (Real.pi / 2)) : 0 < modulus θ := by
  obtain ⟨hd, hu⟩ := cosine_in_unit h
  have hScale := scale_pos hd
  have hg := scale_sq_lt_one hd hu
  unfold modulus
  rw [sub_pos, inv_eq_one_div, lt_div_iff₀ (pow_pos hScale 2), one_mul]
  exact hg

/-- The angular order matches increasing positive moduli of negative t. -/
theorem strictMonoOn_modulus : StrictMonoOn modulus (Ioo 0 (Real.pi / 2)) := by
  intro θ hθ φ hφ hθφ
  have hp := Real.pi_pos
  have hθ' : θ ∈ Icc 0 Real.pi := ⟨hθ.1.le, by linarith [hθ.2]⟩
  have hφ' : φ ∈ Icc 0 Real.pi := ⟨hφ.1.le, by linarith [hφ.2]⟩
  have hc := Real.strictAntiOn_cos hθ' hφ' hθφ
  have hθc := (cosine_in_unit hθ).1
  have hφc := (cosine_in_unit hφ).1
  have hs := strictMonoOn_scale hφc hθc hc
  have hθp := scale_pos hθc
  have hφp := scale_pos hφc
  have hpows := (sq_lt_sq₀ hφp.le hθp.le).mpr hs
  unfold modulus
  apply sub_lt_sub_right
  rw [inv_eq_one_div, inv_eq_one_div,
    div_lt_div_iff₀ (pow_pos hθp 2) (pow_pos hφp 2), one_mul, one_mul]
  exact hpows

end CatalanStrictPeaks.CutGeometry
