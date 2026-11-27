import HighHeightNumerator
import SmallCutoffFrequency

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset Real Filter Topology

private theorem norm_hasSum_le {f : ℕ → ℂ} {y : ℂ} {M : ℕ → ℝ}
    (hs : HasSum f y) (hM : Summable M) (h : ∀ a, ‖f a‖ ≤ M a) :
    ‖y‖ ≤ ∑' a, M a := by
  have hn := hM.of_nonneg_of_le (fun a => norm_nonneg (f a)) h
  rw [←hs.tsum_eq]
  exact (norm_tsum_le_tsum_norm hn).trans (hn.tsum_le_tsum h hM)

private theorem scale_band_radial_sum {k s B D u v : ℝ} (hk : 0 < k) (hs : 0 < s)
    (hc : 0 < v-D/k) :
    (B*s/k)*((u*k/s)*exp (D*u) + 1/((v-D/k)*s)) =
    B*u*exp (D*u) + B/(k*v-D) := by
  have hh : (v-D/k)*k = k*v-D := by field_simp; ring
  rw [←hh]
  generalize hz : (v-D/k) = C at hc ⊢
  field_simp [hk.ne',hs.ne',hc.ne']
  ring

theorem high_band_numerator_cost (k : ℕ) (hk : 2 ≤ k)
    (s r R d q split decay : ℝ) (hs : 0 < s) (hsr : s ≤ r)
    (hd : r-s ≤ d*s/k) (hd0 : 0 ≤ d) (hgap : d < 1)
    (hq : r ≤ q*s) (hrR : r ≤ R) (hR : R ≤ (1+1/(k:ℝ))*r)
    (hS : 0 ≤ split) (hDroot : 0 ≤ decay) (hdecay : 0 < decay-(d+q)/k)
    (hprefix : ∀ x : ℝ, 0 ≤ x → split*k ≤ x →
      (∑ i ∈ range (k-1), x^i/(i.factorial:ℝ)) ≤ exp ((1-decay)*x))
    (g : ℕ → ℂ)
    (hG : ∀ i ∈ range (k-1),
      HasSum (fun a : ℕ => ((-exp (-s):ℝ):ℂ)^(a+1)*((a+1:ℕ):ℂ)^i)
        (-(g (i+1))*((i+1).factorial:ℂ)))
    {u v : ℂ} (hu : ‖u‖=1) (hv : ‖v‖=1) :
    let t := (1-1/(k:ℝ))*r
    ‖numeratorLog k g ((R:ℂ)*u)-localLogRatio s ((t:ℂ)*u)‖ +
      ‖numeratorLog k g ((r:ℂ)*v)-localLogRatio s ((t:ℂ)*v)‖ ≤
      2*q*split*exp ((d+q)*split) + q*split*exp (d*split) +
      2*q/(k*decay-(d+q)) + q/(k*decay-d) +
      2*((k/(2*t))*exp (-(k:ℝ)/6) + 2/(1-d)) := by
  have hkR : (0:ℝ)<k := by exact_mod_cast (show 0 < k by omega)
  have hk1 : (1:ℝ) < k := by exact_mod_cast (show 1 < k by omega)
  have hr : 0 ≤ r := hs.le.trans hsr
  have hq0 : 0 ≤ q := by
    apply nonneg_of_mul_nonneg_left (hr.trans hq) hs
  let t := (1-1/(k:ℝ))*r
  have ht0 : 0 < t := mul_pos (sub_pos.mpr ((div_lt_one hkR).mpr hk1)) (hs.trans_le hsr)
  have htr : t ≤ r := by
    rw [show t=r-r/k by dsimp [t]; ring]
    exact sub_le_self _ (div_nonneg hr hkR.le)
  have rdiff : r-t = r/k := by dsimp [t]; ring
  have hinner : (1-d)*s/k ≤ s-t := by
    rw [show s-t=s-r+(r-t) by ring, rdiff]
    have hdiv := div_le_div_of_nonneg_right hsr hkR.le
    linarith only [hd,hdiv,show (1-d)*s/k=s/k-d*s/k by ring]
  have hpos : 0 < (1-d)*s/(k:ℝ) := div_pos (mul_pos (sub_pos.mpr hgap) hs) hkR
  have hts : t < s := by linarith only [hinner,hpos]
  have hout : R-s ≤ (d+q)*(s/k) := by
    have he : (1+1/(k:ℝ))*r-s = (r-s)+r/k := by ring
    have h := (sub_le_sub_right hR s)
    rw [he] at h
    linarith only [h,hd,div_le_div_of_nonneg_right hq hkR.le,
      show (d+q)*(s/k)=d*s/k+q*s/k by ring]
  have hGG (z : ℂ) : HasSum (prefixFrequency k s z) (numeratorLog k g z) :=
    prefix_frequency_hasSum k s g z hG
  obtain ⟨hTail, hTailCost⟩ := high_height_tail_tsum_at k s t (1-d) (by omega) ht0 (sub_pos.mpr hgap) hinner hts
  have htail (e : ℂ) (he : ‖e‖=1) :
      ‖numeratorLog k g ((t:ℂ)*e)-localLogRatio s ((t:ℂ)*e)‖ ≤ ((k:ℝ)/(2*t))*exp (-(k:ℝ)/6) + 2/(1-d) := by
    let z := (t:ℂ)*e
    have hn : ‖z‖=t := by simp [z, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0.le, he]
    have hsum := (log_frequency_hasSum hs (hn ▸ hts)).sub (hGG z)
    rw [norm_sub_rev]
    apply (norm_hasSum_le hsum hTail ?_).trans hTailCost
    intro a
    rw [←hn]
    apply prefix_tail_frequency_majorant
    omega
  have radial (X D B : ℝ) {e : ℂ} (he : ‖e‖=1) (hsX : s ≤ X) (htX : t ≤ X)
      (hD : 0 ≤ D) (hXD : X-s ≤ D*(s/k)) (hc : 0 < decay-D/k)
      (hw : X-t ≤ B*s/k) :
      ‖numeratorLog k g ((X:ℂ)*e)-numeratorLog k g ((t:ℂ)*e)‖ ≤
        B*split*exp (D*split) + B/(k*decay-D) := by
    obtain ⟨hS,hB⟩ := radial_tsum_bound_at k s X D split decay hs hsX (by omega) hD hXD hS hDroot hc hprefix
    have hsum := (hGG ((X:ℂ)*e)).sub (hGG ((t:ℂ)*e))
    have hbound := norm_hasSum_le hsum (hS.mul_left (X-t))
      (radial_prefix_frequency_majorant k s X t he ht0.le htX)
    rw [tsum_mul_left] at hbound
    apply hbound.trans
    rw [← scale_band_radial_sum hkR hs hc (B:=B) (u:=split)]
    exact (mul_le_mul_of_nonneg_left hB (sub_nonneg.mpr htX)).trans
      (mul_le_mul_of_nonneg_right hw (by positivity))
  have wO : R-t ≤ (2*q)*s/k := by
    calc
      _ ≤ 2*r/k := by dsimp [t]; linarith only [hR, show (1+1/(k:ℝ))*r = (1-1/(k:ℝ))*r+2*r/k by ring]
      _ ≤ _ := (div_le_div_iff_of_pos_right hkR).mpr (by linarith only [hq])
  have wI : r-t ≤ q*s/k := by
    rw [rdiff]
    exact (div_le_div_iff_of_pos_right hkR).mpr hq
  have posInner : (0:ℝ) < decay-d/(k:ℝ) := by
    have hdiff := div_le_div_of_nonneg_right (show d ≤ d+q by linarith) hkR.le
    linarith only [hdecay,hdiff]
  have hradO := radial R (d+q) (2*q) hu (hsr.trans hrR) (htr.trans hrR)
    (add_nonneg hd0 hq0) hout hdecay wO
  have hradI := radial r d q hv hsr htr hd0
    (by simpa only [mul_div_assoc] using hd) posInner wI
  have htO := dist_triangle (numeratorLog k g ((R:ℂ)*u)) (numeratorLog k g ((t:ℂ)*u))
    (localLogRatio s ((t:ℂ)*u))
  have htI := dist_triangle (numeratorLog k g ((r:ℂ)*v)) (numeratorLog k g ((t:ℂ)*v))
    (localLogRatio s ((t:ℂ)*v))
  simp only [dist_eq_norm] at htO htI
  dsimp only
  linarith only [htO, htI, hradO, hradI, htail u hu, htail v hv]

#print axioms high_band_numerator_cost
end OpenMathResearch.LongCycleExcedances
