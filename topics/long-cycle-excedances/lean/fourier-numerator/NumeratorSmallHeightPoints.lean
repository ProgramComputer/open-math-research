import NumeratorCutoffAdapter

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open scoped BigOperators Real

private theorem principal_norm_eq_radius (s : ℝ) :
    ‖(s:ℂ) + (π:ℂ)*Complex.I‖ = numeratorRadius s := by
  have hsq : ‖(s:ℂ) + (π:ℂ)*Complex.I‖^2 = s^2+π^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [pow_two]
  have hr : (numeratorRadius s)^2 = s^2+π^2 := Real.sq_sqrt (by positivity)
  have hn := norm_nonneg ((s:ℂ)+(π:ℂ)*Complex.I)
  exact (pow_left_inj₀ hn (numeratorRadius_pos s).le (by norm_num : 2 ≠ 0)).mp (hsq.trans hr.symm)

private theorem original_cutoff_range_shift {k : ℕ} (hk : 0 < k) (s : ℝ) (w : ℂ) :
    (∑ j ∈ Finset.range k, (RepositoryQuotientAudit.cutoffLogCoefficient k
      (-Real.exp (-s)) j:ℂ) * w^j) =
    ∑ i ∈ Finset.range (k-1), (RepositoryQuotientAudit.cutoffLogCoefficient k
      (-Real.exp (-s)) (i+1):ℂ) * w^(i+1) := by
  let f : ℕ → ℂ := fun j =>
    (RepositoryQuotientAudit.cutoffLogCoefficient k (-Real.exp (-s)) j:ℂ) * w^j
  change (∑ j ∈ Finset.range k, f j) = ∑ i ∈ Finset.range (k-1), f (i+1)
  have h0 : f 0 = 0 := by simp [f,RepositoryQuotientAudit.cutoffLogCoefficient]
  conv_lhs => rw [show k = (k-1)+1 by omega, Finset.sum_range_succ']
  simp only [h0,add_zero]

/-- Small-height original-polynomial comparison at the same two points as
the high-height estimate, given the analytic identification on the unit disk. -/
theorem original_small_height_numerator_at_points {k : ℕ} (hk : 100 ≤ k)
    {s : ℝ} (hs : 0 ≤ s) (hsu : s ≤ 4*Real.sqrt k)
    (L : ℂ → ℂ)
    (hL : ∀ z : ℂ, ‖z‖ < 1 →
      HasSum (fun j : ℕ => numeratorLogSeries s j * z^j) (L ((numeratorRadius s:ℂ)*z)))
    (w : ℂ) :
    let w₁ : ℂ := (s:ℂ)+(π:ℂ)*Complex.I
    let r := ‖w₁‖
    r ≤ ‖w‖ → ‖w‖ ≤ (1+1/(k:ℝ))*r →
    let w' := (((1-1/(k:ℝ))*r/‖w‖:ℝ):ℂ)*w
    let w₁' := ((1-1/(k:ℝ):ℝ):ℂ)*w₁
    let G : ℂ → ℂ := fun q =>
      ∑ i ∈ Finset.range (k-1), (RepositoryQuotientAudit.cutoffLogCoefficient k
        (-Real.exp (-s)) (i+1):ℂ) * q^(i+1)
    ‖G w-L w'‖ + ‖G w₁-L w₁'‖ ≤ (2997:ℝ)/100 := by
  let p : ℂ := (s:ℂ)+(π:ℂ)*Complex.I
  let r := numeratorRadius s
  dsimp only
  rw [principal_norm_eq_radius s]
  intro hwp hwr
  change r ≤ ‖w‖ at hwp
  change ‖w‖ ≤ (1+1/(k:ℝ))*r at hwr
  have hkr : (0:ℝ) < k := by exact_mod_cast (show 0<k by omega)
  have hr : 0 < r := numeratorRadius_pos s
  have hw : 0 < ‖w‖ := hr.trans_le hwp
  have hrc : (r:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hwc : ((‖w‖:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hw.ne'
  have hp : ‖p‖ = r := principal_norm_eq_radius s
  let R := ‖w‖/r
  let ξ : ℂ := w/(‖w‖:ℂ)
  let η : ℂ := p/(r:ℂ)
  let ρ : ℝ := 1-1/(k:ℝ)
  have hR₀ : 1 ≤ R := (le_div_iff₀ hr).2 (by simpa using hwp)
  have hR₁ : R ≤ 1+1/(k:ℝ) := (div_le_iff₀ hr).2 hwr
  have hξ : ‖ξ‖ = 1 := by
    simp only [ξ,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hw,div_self hw.ne']
  have hη : ‖η‖ = 1 := by
    simp only [η,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr,hp,div_self hr.ne']
  have hρ0 : 0 ≤ ρ := sub_nonneg.mpr ((div_le_one hkr).2 (by
    exact_mod_cast (show 1 ≤ k by omega)))
  have hρ1 : ρ < 1 := by
    dsimp only [ρ]
    have hu : 0 < 1/(k:ℝ) := by positivity
    linarith only [hu]
  have ht (u : ℂ) (hu : ‖u‖ = 1) : ‖(ρ:ℂ)*u‖ < 1 := by
    simpa only [norm_mul,hu, mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hρ0] using hρ1
  have hW : (r:ℂ)*((R:ℂ)*ξ) = w := by
    have hscale : (r:ℂ)*(R:ℂ) = (‖w‖:ℂ) := by
      unfold R
      rw [Complex.ofReal_div, ← mul_div_assoc, mul_div_cancel_left₀ _ hrc]
    rw [← mul_assoc, hscale]
    change (‖w‖:ℂ)*(w/(‖w‖:ℂ)) = w
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ hwc]
  have hP : (r:ℂ)*η = p := by
    dsimp only [η]
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ hrc]
  have hW' : (r:ℂ)*((ρ:ℂ)*ξ) = ((ρ*r/‖w‖:ℝ):ℂ)*w := by
    dsimp only [ξ]
    rw [Complex.ofReal_div,Complex.ofReal_mul]
    ring
  have hP' : (r:ℂ)*((ρ:ℂ)*η) = (ρ:ℂ)*p := by
    rw [← mul_left_comm, hP]
  have h := numerator_original_cutoff_series_contraction hs hk hsu hR₀ hR₁ hξ hη
  dsimp only at h
  rw [(hL _ (ht ξ hξ)).tsum_eq,(hL _ (ht η hη)).tsum_eq] at h
  change ‖(∑ j ∈ Finset.range k, _ * ((r:ℂ)*((R:ℂ)*ξ))^j) - L ((r:ℂ)*((ρ:ℂ)*ξ))‖ +
    ‖(∑ j ∈ Finset.range k, _ * ((r:ℂ)*η)^j) - L ((r:ℂ)*((ρ:ℂ)*η))‖ ≤ _ at h
  rw [hW,hP,hW',hP',original_cutoff_range_shift (by omega) s w,
    original_cutoff_range_shift (by omega) s p] at h
  exact h

#print axioms original_small_height_numerator_at_points
end OpenMathResearch.LongCycleExcedances
