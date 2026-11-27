import FrequencyMajorants

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset Real

def numeratorLog (k : ℕ) (g : ℕ → ℂ) (w : ℂ) : ℂ :=
  ∑ i ∈ range (k-1), g (i+1)*w^(i+1)

private theorem norm_hasSum_le {f : ℕ → ℂ} {y : ℂ} {M : ℕ → ℝ}
    (hs : HasSum f y) (hM : Summable M) (h : ∀ a, ‖f a‖ ≤ M a) :
    ‖y‖ ≤ ∑' a, M a := by
  have hn := hM.of_nonneg_of_le (fun a => norm_nonneg (f a)) h
  rw [←hs.tsum_eq]
  exact (norm_tsum_le_tsum_norm hn).trans (hn.tsum_le_tsum h hM)

private theorem scale_radial_sum {k s B D : ℝ} (hk : 0 < k) (hs : 0 < s)
    (hc : 0 < 1/50-D/k) :
    (B*s/k)*(((5/4:ℝ)*k/s)*exp (D*(5/4)) + 1/((1/50-D/k)*s)) =
    B*(5/4)*exp (D*(5/4)) + B/(k/50-D) := by
  have hh : (1/50-D/k)*k = k/50-D := by field_simp; ring
  rw [←hh]
  generalize hz : (1/50-D/k) = C at hc ⊢
  field_simp [hk.ne',hs.ne',hc.ne']
  ring

theorem high_height_numerator_contraction (k : ℕ) (hk : 100 ≤ k)
    (s r R : ℝ) (hs : 0 < s) (hr : 0 ≤ r) (hhigh : 16*(k:ℝ) < s^2)
    (hcircle : r^2 = s^2+π^2) (hrR : r ≤ R) (hR : R ≤ (1+1/(k:ℝ))*r)
    (g : ℕ → ℂ)
    (hG : ∀ i ∈ range (k-1),
      HasSum (fun a : ℕ => ((-exp (-s):ℝ):ℂ)^(a+1)*((a+1:ℕ):ℂ)^i)
        (-(g (i+1))*((i+1).factorial:ℂ)))
    {u v : ℂ} (hu : ‖u‖=1) (hv : ‖v‖=1) :
    let t := (1-1/(k:ℝ))*r
    ‖numeratorLog k g ((R:ℂ)*u)-localLogRatio s ((t:ℂ)*u)‖ +
      ‖numeratorLog k g ((r:ℂ)*v)-localLogRatio s ((t:ℂ)*v)‖ < 25 := by
  have hK : (100:ℝ) ≤ k := by exact_mod_cast hk
  have hkR : (0:ℝ)<k := by linarith
  obtain ⟨hsr, hd, hq, houter, hgap, ht⟩ := high_height_geometry hK hs hr hhigh hcircle
  let t := (1-1/(k:ℝ))*r
  change 1<t at ht
  change (69/100:ℝ)*s/k<s-t at hgap
  have ht0 : 0 ≤ t := by linarith only [ht]
  have htr : t ≤ r := by
    rw [show t=r-r/k by dsimp [t]; ring]
    exact sub_le_self _ (div_nonneg hr hkR.le)
  have hts : t < s := by linarith only [hgap, show 0<(69/100:ℝ)*s/k by positivity]
  have hGG (z : ℂ) : HasSum (prefixFrequency k s z) (numeratorLog k g z) :=
    prefix_frequency_hasSum k s g z hG
  obtain ⟨hTail, hTailCost⟩ := high_height_tail_tsum k s t hk ht.le hgap.le hts
  have htail (e : ℂ) (he : ‖e‖=1) :
      ‖numeratorLog k g ((t:ℂ)*e)-localLogRatio s ((t:ℂ)*e)‖ ≤ 1/1000+2/(69/100) := by
    let z := (t:ℂ)*e
    have hn : ‖z‖=t := by simp [z, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0, he]
    have hsum := (log_frequency_hasSum hs (hn ▸ hts)).sub (hGG z)
    rw [norm_sub_rev]
    apply (norm_hasSum_le hsum hTail ?_).trans hTailCost
    intro a
    rw [←hn]
    apply prefix_tail_frequency_majorant
    omega
  have radial (X D B : ℝ) {e : ℂ} (he : ‖e‖=1) (hsX : s ≤ X) (htX : t ≤ X)
      (hD : 0 ≤ D) (hXD : X-s ≤ D*(s/k)) (hc : 0 < 1/50-D/k)
      (hw : X-t ≤ B*s/k) :
      ‖numeratorLog k g ((X:ℂ)*e)-numeratorLog k g ((t:ℂ)*e)‖ ≤
        B*(5/4)*exp (D*(5/4)) + B/(k/50-D) := by
    obtain ⟨hS,hB⟩ := radial_tsum_bound k s X D hs hsX (by omega) hD hXD hc
    have hsum := (hGG ((X:ℂ)*e)).sub (hGG ((t:ℂ)*e))
    have hbound := norm_hasSum_le hsum (hS.mul_left (X-t))
      (radial_prefix_frequency_majorant k s X t he ht0 htX)
    rw [tsum_mul_left] at hbound
    apply hbound.trans
    rw [← scale_radial_sum hkR hs hc (B:=B)]
    exact (mul_le_mul_of_nonneg_left hB (sub_nonneg.mpr htX)).trans
      (mul_le_mul_of_nonneg_right hw (by positivity))
  have wO : R-t ≤ (2*(251/250))*s/k := by
    calc
      _ ≤ 2*r/k := by dsimp [t]; linarith only [hR, show (1+1/(k:ℝ))*r = (1-1/(k:ℝ))*r+2*r/k by ring]
      _ ≤ _ := (div_le_div_iff_of_pos_right hkR).mpr (by linarith only [hq])
  have wI : r-t ≤ (251/250)*s/k := by
    have he : r-t = r/k := by dsimp [t]; ring
    rw [he]
    exact (div_le_div_iff_of_pos_right hkR).mpr hq.le
  have posOuter : (0:ℝ) < 1/50-(657/500)/(k:ℝ) := by
    apply sub_pos.mpr
    apply (div_lt_iff₀ hkR).mpr
    linarith
  have posInner : (0:ℝ) < 1/50-(31/100)/(k:ℝ) := by
    apply sub_pos.mpr
    apply (div_lt_iff₀ hkR).mpr
    linarith
  have hradO := radial R (657/500) (2*(251/250)) hu (hsr.trans hrR) (htr.trans hrR)
    (by norm_num) (by
      simpa only [mul_div_assoc] using (sub_le_sub_right hR s).trans houter.le) posOuter wO
  have hradI := radial r (31/100) (251/250) hv hsr htr (by norm_num)
    (by simpa only [mul_div_assoc] using hd.le) posInner wI
  change ‖numeratorLog k g ((R:ℂ)*u)-localLogRatio s ((t:ℂ)*u)‖ +
    ‖numeratorLog k g ((r:ℂ)*v)-localLogRatio s ((t:ℂ)*v)‖ < 25
  have htO := dist_triangle (numeratorLog k g ((R:ℂ)*u)) (numeratorLog k g ((t:ℂ)*u))
    (localLogRatio s ((t:ℂ)*u))
  have htI := dist_triangle (numeratorLog k g ((r:ℂ)*v)) (numeratorLog k g ((t:ℂ)*v))
    (localLogRatio s ((t:ℂ)*v))
  simp only [dist_eq_norm] at htO htI
  have final := high_height_cost_budget hK
  norm_num at hradO hradI final
  linarith only [htO, htI, hradO, hradI, htail u hu, htail v hv, final]

#print axioms high_height_numerator_contraction
end OpenMathResearch.LongCycleExcedances
