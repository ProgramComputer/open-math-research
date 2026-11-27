import SmallCutoffHighPoints
import EightNineConstants

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset Real

theorem high_band_eight_original_shape (k : ℕ) (hk : 8 ≤ k) (hku : k < 10)
    (s : ℝ) (hhigh : 8*Real.sqrt (k:ℝ) < s) (w : ℂ)
    (g : ℕ → ℂ)
    (hG : ∀ i ∈ range (k-1),
      HasSum (fun a : ℕ => ((-exp (-s):ℝ):ℂ)^(a+1)*((a+1:ℕ):ℂ)^i)
        (-(g (i+1))*((i+1).factorial:ℂ))) :
    let w₁ : ℂ := (s:ℂ)+(π:ℂ)*Complex.I
    let r := ‖w₁‖
    r ≤ ‖w‖ → ‖w‖ ≤ (1+1/(k:ℝ))*r →
    let w' := (((1-1/(k:ℝ))*r/‖w‖ : ℝ):ℂ)*w
    let w₁' := ((1-1/(k:ℝ):ℝ):ℂ)*w₁
    ‖numeratorLog k g w-localLogRatio s w'‖ +
      ‖numeratorLog k g w₁-localLogRatio s w₁'‖ < 65 := by
  have hK : (8:ℝ) ≤ k := by exact_mod_cast hk
  have hKu : (k:ℝ) ≤ 9 := by exact_mod_cast (show k ≤ 9 by omega)
  have hs0 : 0 ≤ 8*Real.sqrt (k:ℝ) := by positivity
  have hs := hs0.trans_lt hhigh
  have hbase : (10:ℝ) ≤ 8*Real.sqrt (k:ℝ) := by
    have hss : (10/8:ℝ) ≤ Real.sqrt (k:ℝ) := (Real.le_sqrt (by norm_num)
      (by positivity)).mpr (by linarith)
    linarith only [hss]
  have hh := (sq_lt_sq₀ hs0 hs.le).mpr hhigh
  rw [mul_pow, Real.sq_sqrt (by positivity : (0:ℝ) ≤ k)] at hh
  have hgeom (r : ℝ) (hr : 0 ≤ r) (hcircle : r^2 = s^2+π^2) :
      s ≤ r ∧ r-s ≤ (78/1000)*s/k ∧ r ≤ (101/100)*s :=
    high_band_geometry_at (K:=8) (b:=8) (by norm_num) hK hs hr hh hcircle
      (by norm_num) (by norm_num) (by norm_num)
  apply high_band_at_points k (by omega) s (hbase.trans hhigh.le)
    (78/1000) (101/100) (2) (3/20) 65 hgeom
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) _ _ _ g hG w
  · apply sub_pos.mpr
    exact (div_lt_iff₀ (by linarith : (0:ℝ) < k)).mpr (by linarith)
  · intro x hx hsplit
    simpa only [show (1:ℝ)-(3/20) = 17/20 by norm_num] using
      poisson_prefix_eight hx k hsplit
  · intro t ht
    exact high_band_eight_budget hK hKu ht

#print axioms high_band_eight_original_shape
end OpenMathResearch.LongCycleExcedances
