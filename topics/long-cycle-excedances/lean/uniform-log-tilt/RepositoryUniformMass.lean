import RepositoryUniformHighDegree
import UniformMassSum
import LinearTilt
import PoleMonomial
import HighAngleActualInputs

noncomputable section
namespace RepositoryQuotientAudit
open OpenMathResearch.LongCycleExcedances Finset Real

private theorem budget_of_poles {k d : ℕ} (hd : 2 ≤ d) (hdk : d < k)
    {x : ℝ} (hx : 0 ≤ x)
    (hs : Summable fun l : ℤ => ‖coherentPole x 0 / coherentPole x l‖^d)
    {B : ℝ} (hB : (1+1/(50*(k:ℝ)))^d *
      (∑' l : ℤ, ‖coherentPole x 0 / coherentPole x l‖^d) ≤ B) :
    let R := ‖coherentPole x 0‖*(1+1/(50*(k:ℝ)))
    |cutoffLogCoefficient k (-exp (-x)) d * R^d| ≤ B/(d:ℝ) := by
  dsimp only
  rw [cutoffLogCoefficient,if_neg (by omega : d ≠ 1),if_pos ⟨hd,hdk⟩]
  apply (pole_monomial_bound (by omega : 1 ≤ d) _ _ (by positivity)
    (coherentPole x 0) (coherentPole x) (LongCycleBounds.Band.moment_poles d hd x hx) hs).trans
  exact div_le_div_of_nonneg_right hB (Nat.cast_nonneg _)

/-- An absolute bound for the actual finite log tilt on the common enlarged
contour, uniform in the logarithmic modulus and minimum cycle length. -/
theorem original_uniform_log_mass {k : ℕ} (hk : 7 ≤ k) {x : ℝ} (hx : 0 ≤ x) :
    let R := ‖coherentPole x 0‖*(1+1/(50*(k:ℝ)))
    (∑ i ∈ range (k-1), |cutoffLogCoefficient k (-exp (-x)) (i+1)*R^(i+1)|) ≤
      6+9*log k := by
  let r := ‖coherentPole x 0‖
  let R := r*(1+1/(50*(k:ℝ)))
  let F (d : ℕ) := |cutoffLogCoefficient k (-exp (-x)) d * R^d|
  have hr : 0 < r := coherentPole_near_pos x
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hgeom : r^2 = x^2+π^2 := by
    have hre : (coherentPole x 0).re = x := by simp [coherentPole, Complex.add_re,
      Complex.mul_I_re, Complex.mul_im, Complex.add_im]
    have him : (coherentPole x 0).im = π := by simpa using coherentPole_im x 0
    dsimp only [r]
    rw [Complex.sq_norm,Complex.normSq_apply,hre,him]
    ring
  have lin : F 1 = |(-(-exp (-x))/(1-(-exp (-x))))*R| := by simp [F,cutoffLogCoefficient]
  have hn (d : ℕ) : 0 ≤ F d := abs_nonneg _
  have hk2 : 2 ≤ k := by omega
  have hlog : 0 ≤ log (k:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1≤k by omega))
  change (∑ i ∈ range (k-1), F (i+1)) ≤ _
  by_cases small : x ≤ 10
  · have hl : F 1 ≤ 6 := lin.trans_le (small_linear_cost hx small hr.le hgeom hk)
    have low : (∑ d ∈ Icc 2 1, F d) ≤ 0 := by norm_num
    have hi (d : ℕ) (hd : d ∈ Icc 2 (k-1)) (_ : 1 < d) : F d ≤ 9/(d:ℝ) := by
      obtain ⟨hlo,hhi⟩ := mem_Icc.mp hd
      have hdk : d < k := by omega
      exact budget_of_poles hlo hdk hx (uniform_small_modulus_coherent_poles hx small hlo).1
        (uniform_small_modulus_coherent_multiplier hx small hlo hdk)
    exact (uniform_mass_from_split hk2 F hn (by norm_num) hl low hi).trans (by linarith)
  · have hx' : 10 ≤ x := (lt_of_not_ge small).le
    have hradius := uniform_outer_radius hx' hr.le hgeom hk
    have hl : F 1 ≤ 1 := lin.trans_le (large_linear_cost hx' hR hradius.2)
    let L := lowCut k x
    have hL : L ≤ k-1 := min_le_left _ _
    have low : (∑ d ∈ Icc 2 L, F d) ≤ 4+3*log k := by
      let m (d : ℕ) := LongCycleBounds.Band.moment d (-exp (-x))
      have repr (d : ℕ) (hd : d ∈ Icc 2 L) := shifted_moment_input (mem_Icc.mp hd).1
        (show 0<x by linarith) (m d) (LongCycleBounds.Band.moment_discrete d (mem_Icc.mp hd).1 x (by linarith))
      have h := low_moment_absolute_mass (by omega : 1 ≤ k) (by omega : L ≤ k) hx' hR
        (lowCut_scale k x) hradius.1 hradius.2 m repr
      have eqF (d : ℕ) (hd : d ∈ Icc 2 L) :
          F d = |(-m d/(d.factorial:ℝ))*R^d| := by
        obtain ⟨hd1,hd2⟩ := mem_Icc.mp hd
        dsimp only [F,m]
        rw [cutoffLogCoefficient,if_neg (show d ≠ 1 by omega),if_pos ⟨hd1,(by omega : d < k)⟩]
      rw [sum_congr rfl eqF]
      linarith only [h,harmonic_full_log (k:=k) (by omega)]
    have hi (d : ℕ) (hd : d ∈ Icc 2 (k-1)) (hL' : L < d) : F d ≤ 5/(d:ℝ) := by
      obtain ⟨hd1,hd2⟩ := mem_Icc.mp hd
      have hdk : d < k := by omega
      have hcut := above_lowCut hdk hL'
      have hscale := uniform_high_degree_scale_of_cut hx' hcut
      have hs := uniform_high_degree_coherent_poles x hscale.1 (by
        simpa only [uniformTiltPole,coherentPole] using hscale.2)
      exact budget_of_poles hd1 hdk hx hs.1
        ((uniform_high_degree_coherent_multiplier hx' hcut hdk).trans (by norm_num))
    linarith only [uniform_mass_from_split hk2 F hn (by norm_num) hl low hi,hlog]

/-- The same all-angle estimate bounds every Taylor coefficient and supplies
a nonzero amplitude throughout the enlarged closed disk. -/
theorem original_uniform_tilt_envelope {k : ℕ} (hk : 7 ≤ k) {x : ℝ} (hx : 0 ≤ x) :
    let R := ‖coherentPole x 0‖*(1+1/(50*(k:ℝ)))
    let B := 6+9*log k
    let T := coherentTilt k (-exp (-x))
    (∀ j : ℕ, |PowerSeries.coeff j T| ≤ exp B/R^j) ∧
      ∀ w : ℂ, ‖w‖ ≤ R → exp (-B) ≤ ‖seriesValue T w‖ := by
  dsimp only
  have hr := coherentPole_near_pos x
  have hR : 0 < ‖coherentPole x 0‖*(1+1/(50*(k:ℝ))) := by positivity
  have hm := original_uniform_log_mass hk hx
  constructor
  · intro j
    apply (original_coherentTilt_coeff_bound (by omega : 2 ≤ k) _ _ hR j).trans
    exact div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hm) (pow_nonneg hR.le j)
  · intro w hw
    exact (Real.exp_le_exp.mpr (neg_le_neg hm)).trans
      (norm_seriesValue_coherentTilt_ge (by omega : 2 ≤ k) _ w _ hw)

#print axioms original_uniform_tilt_envelope
#print axioms original_uniform_log_mass
end RepositoryQuotientAudit
