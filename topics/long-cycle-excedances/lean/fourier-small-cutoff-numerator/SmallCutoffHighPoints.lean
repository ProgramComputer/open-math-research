import HighBandConstants
import HighHeightPointAdapter

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset Real

theorem high_band_at_points (k : ℕ) (hk : 10 ≤ k)
    (s : ℝ) (hs10 : 10 ≤ s)
    (d q split decay M : ℝ)
    (hgeom : ∀ r : ℝ, 0 ≤ r → r^2 = s^2+π^2 →
      s ≤ r ∧ r-s ≤ d*s/k ∧ r ≤ q*s)
    (hd0 : 0 ≤ d) (hd1 : d < 1) (hu0 : 0 ≤ split) (hv0 : 0 ≤ decay)
    (hpos : 0 < decay-(d+q)/(k:ℝ))
    (hprefix : ∀ x : ℝ, 0 ≤ x → split*k ≤ x →
      (∑ i ∈ range (k-1), x^i/(i.factorial:ℝ)) ≤ exp ((1-decay)*x))
    (hbudget : ∀ t : ℝ, 5 ≤ t →
      2*q*split*exp ((d+q)*split) + q*split*exp (d*split) +
      2*q/(k*decay-(d+q)) + q/(k*decay-d) +
      2*((k/(2*t))*exp (-(k:ℝ)/6) + 2/(1-d)) < M)
    (g : ℕ → ℂ)
    (hG : ∀ i ∈ range (k-1),
      HasSum (fun a : ℕ => ((-exp (-s):ℝ):ℂ)^(a+1)*((a+1:ℕ):ℂ)^i)
        (-(g (i+1))*((i+1).factorial:ℂ)))
    (w : ℂ) :
    let w₁ : ℂ := (s:ℂ)+(π:ℂ)*Complex.I
    let r := ‖w₁‖
    r ≤ ‖w‖ → ‖w‖ ≤ (1+1/(k:ℝ))*r →
    let w' := (((1-1/(k:ℝ))*r/‖w‖ : ℝ):ℂ)*w
    let w₁' := ((1-1/(k:ℝ):ℝ):ℂ)*w₁
    ‖numeratorLog k g w-localLogRatio s w'‖ +
      ‖numeratorLog k g w₁-localLogRatio s w₁'‖ < M := by
  let w₁ : ℂ := (s:ℂ)+(π:ℂ)*Complex.I
  let r := ‖w₁‖
  let R := ‖w‖
  change r ≤ R → R ≤ (1+1/(k:ℝ))*r → _
  intro hrR hR
  have hsq : r^2 = s^2+π^2 := by
    dsimp [r,w₁]
    rw [Complex.sq_norm,Complex.normSq_apply]
    simp <;> ring
  have hr : 0 ≤ r := norm_nonneg _
  obtain ⟨hsr,hd,hq⟩ := hgeom r hr hsq
  have hr0 : 0 < r := by linarith
  have hR0 : 0 < R := hr0.trans_le hrR
  have hrc : (r:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr0.ne'
  have hRc : (R:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR0.ne'
  let u := w/(R:ℂ)
  let v := w₁/(r:ℂ)
  have hu : ‖u‖=1 := by simp [u,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hR0,R,hR0.ne']
  have hv : ‖v‖=1 := by simp [v,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr0,r,hr0.ne']
  have h1 : (R:ℂ)*u=w := by dsimp [u]; field_simp
  have h2 : (r:ℂ)*v=w₁ := by dsimp [v]; field_simp
  let t := (1-1/(k:ℝ))*r
  have h3 : (t:ℂ)*u=((t/R:ℝ):ℂ)*w := by
    dsimp [u]
    rw [Complex.ofReal_div]
    ring
  have h4 : (t:ℂ)*v=((1-1/(k:ℝ):ℝ):ℂ)*w₁ := by
    dsimp [v,t]
    rw [Complex.ofReal_mul]
    generalize hcoef : (1-1/(k:ℝ))=c
    field_simp [hrc] <;> ring
  have H := high_band_numerator_cost k (by omega) s r R d q split decay
    (by linarith) hsr hd hd0 hd1 hq hrR hR hu0 hv0 hpos hprefix g hG hu hv
  have ht : 5 ≤ t := by
    have hK : (10:ℝ) ≤ k := by exact_mod_cast hk
    have hd : 1/(k:ℝ) ≤ 1/10 :=
      one_div_le_one_div_of_le (by norm_num) hK
    dsimp only [t]
    have h := mul_le_mul_of_nonneg_right
      (show (9/10:ℝ) ≤ 1-1/(k:ℝ) by linarith) hr
    have h' := mul_le_mul_of_nonneg_left (hs10.trans hsr) (show (0:ℝ) ≤ 9/10 by norm_num)
    linarith only [h,h']
  have HH := H.trans_lt (hbudget t ht)
  change ‖numeratorLog k g ((R:ℂ)*u)-localLogRatio s ((t:ℂ)*u)‖ +
    ‖numeratorLog k g ((r:ℂ)*v)-localLogRatio s ((t:ℂ)*v)‖ < M at HH
  simpa only [h1,h2,h3,h4] using HH

#print axioms high_band_at_points
end OpenMathResearch.LongCycleExcedances
