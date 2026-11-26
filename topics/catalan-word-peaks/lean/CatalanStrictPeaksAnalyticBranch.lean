import CatalanStrictPeaksCutParameter
import CatalanStrictPeaksDiscriminant
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Analytic branch of the scaled strict-peak generating function

The discriminant is the product of four factors with simple zeros. Taking
the principal square root of each factor defines the germ normalized at
zero and its continuation away from the four radial cuts.
-/

namespace CatalanStrictPeaks.CutGeometry

open Complex Set
open scoped ComplexConjugate Topology

/-- The principal complex square root, with the cut on the negative real axis. -/
noncomputable def principalRoot (u : ℂ) : ℂ := u ^ ((2 : ℂ)⁻¹)

@[simp] theorem principalRoot_sq (u : ℂ) : principalRoot u ^ 2 = u := by
  simp [principalRoot]

@[simp] theorem principalRoot_one : principalRoot 1 = 1 := by simp [principalRoot]

theorem principalRoot_conj {u : ℂ} (hu : u ∈ slitPlane) :
    principalRoot (conj u) = conj (principalRoot u) := by
  unfold principalRoot
  rw [Complex.conj_cpow _ _ (slitPlane_arg_ne_pi hu)]
  simp [Complex.conj_ofNat]

/-- A factor's square root is cut along the ray starting at its zero. -/
noncomputable def cutFactor (ζ x : ℂ) : ℂ := principalRoot (1 - x / ζ)

/-- The square-root branch of the quartic on the common slit domain. -/
noncomputable def branch (d : ℝ) (x : ℂ) : ℂ :=
  cutFactor (nearPoint d) x * cutFactor (conj (nearPoint d)) x *
    (cutFactor (farPoint d) x * cutFactor (conj (farPoint d)) x)

/-- The complement of the four closed outward radial rays. -/
def slitDomain (d : ℝ) : Set ℂ :=
  {x | 1 - x / nearPoint d ∈ slitPlane ∧ 1 - x / conj (nearPoint d) ∈ slitPlane ∧
    1 - x / farPoint d ∈ slitPlane ∧ 1 - x / conj (farPoint d) ∈ slitPlane}

private theorem normalized_factor (x ζ : ℂ) (hζ : ζ ≠ 0) :
    1 - x / ζ = (x - ζ) / (-ζ) := by
  rw [div_neg, sub_div, div_self hζ]
  ring

theorem branch_sq {d : ℝ} (hd : 0 < d) (hD : d < 1) (x : ℂ) :
    branch d x ^ 2 = quartic (scale d) x := by
  have hz : nearPoint d ≠ 0 := by
    intro h
    simpa [h] using nearPoint_im_pos hd hD
  have hw : farPoint d ≠ 0 := by
    intro h
    simpa [h] using farPoint_im_pos hd hD
  have hzc : conj (nearPoint d) ≠ 0 := (map_ne_zero (starRingEnd ℂ)).2 hz
  have hwc : conj (farPoint d) ≠ 0 := (map_ne_zero (starRingEnd ℂ)).2 hw
  have hprod := (quartic_factor hd hD 0).symm
  simp only [quartic, zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero, one_pow, mul_zero,
    sub_zero, zero_sub] at hprod
  unfold branch cutFactor
  simp only [mul_pow, principalRoot_sq, normalized_factor x _ hz,
    normalized_factor x _ hzc, normalized_factor x _ hw, normalized_factor x _ hwc,
    div_mul_div_comm, hprod, div_one]
  exact (quartic_factor hd hD x).symm

@[simp] theorem branch_zero (d : ℝ) : branch d 0 = 1 := by simp [branch, cutFactor]

private theorem slit_ofReal {ζ : ℂ} (hζ : ζ.im ≠ 0) (x : ℝ) :
    1 - (x : ℂ) / ζ ∈ slitPlane := by
  by_cases hx : x = 0
  · simp [hx]
  · right
    simp [Complex.div_im, hx, hζ, Complex.normSq_eq_zero,
      show ζ ≠ 0 by intro h; apply hζ; simp [h]]

theorem ofReal_mem_slitDomain {d : ℝ} (hd : 0 < d) (hD : d < 1) (x : ℝ) :
    (x : ℂ) ∈ slitDomain d := by
  have hz := (nearPoint_im_pos hd hD).ne'
  have hw := (farPoint_im_pos hd hD).ne'
  exact ⟨slit_ofReal hz x, slit_ofReal (by simpa [Complex.conj_im] using hz) x,
    slit_ofReal hw x, slit_ofReal (by simpa [Complex.conj_im] using hw) x⟩

theorem zero_mem_slitDomain (d : ℝ) : (0 : ℂ) ∈ slitDomain d := by simp [slitDomain]

private theorem cutFactor_conj_ofReal {ζ : ℂ} (hζ : ζ.im ≠ 0) (x : ℝ) :
    cutFactor (conj ζ) x = conj (cutFactor ζ x) := by
  unfold cutFactor
  have h : 1 - (x : ℂ) / conj ζ = conj (1 - (x : ℂ) / ζ) := by simp
  rw [h, principalRoot_conj (slit_ofReal hζ x)]

private theorem mul_conj_re_nonneg (u v : ℂ) : 0 ≤ (u * conj u * (v * conj v)).re := by
  rw [Complex.mul_conj, Complex.mul_conj, ← Complex.ofReal_mul, Complex.ofReal_re]
  exact mul_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)

theorem branch_re_nonneg_ofReal {d : ℝ} (hd : 0 < d) (hD : d < 1) (x : ℝ) :
    0 ≤ (branch d x).re := by
  unfold branch
  rw [cutFactor_conj_ofReal (nearPoint_im_pos hd hD).ne',
    cutFactor_conj_ofReal (farPoint_im_pos hd hD).ne']
  exact mul_conj_re_nonneg _ _

private theorem cutFactor_analyticAt {ζ x : ℂ} (h : 1 - x / ζ ∈ slitPlane) :
    AnalyticAt ℂ (cutFactor ζ) x := by
  have hdiv : AnalyticAt ℂ (fun z : ℂ => z / ζ) x := by
    simpa [div_eq_mul_inv] using
      (analyticAt_id.mul (analyticAt_const :
        AnalyticAt ℂ (fun _ : ℂ => ζ⁻¹) x))
  exact (analyticAt_const.sub hdiv).cpow analyticAt_const h

theorem branch_analyticAt {d : ℝ} {x : ℂ} (h : x ∈ slitDomain d) :
    AnalyticAt ℂ (branch d) x := by
  rcases h with ⟨h₁, h₂, h₃, h₄⟩
  exact ((cutFactor_analyticAt h₁).mul (cutFactor_analyticAt h₂)).mul
    ((cutFactor_analyticAt h₃).mul (cutFactor_analyticAt h₄))

/-- The rationalized generating function, which is regular at zero and at c. -/
noncomputable def analyticGenerating (d : ℝ) (x : ℂ) : ℂ :=
  2 / (1 - x ^ 2 + branch d x)

private theorem rationalized_product {d : ℝ} (hd : 0 < d) (hD : d < 1) (x : ℂ) :
    (1 - x ^ 2 - branch d x) * (1 - x ^ 2 + branch d x) =
      4 * x * ((scale d : ℂ) - x) := by
  calc
    _ = (1 - x ^ 2) ^ 2 - branch d x ^ 2 := by ring
    _ = _ := by rw [branch_sq hd hD]; unfold quartic; ring

theorem rationalized_denominator_ne_zero {d : ℝ} (hd : 0 < d) (hD : d < 1) (x : ℂ) :
    1 - x ^ 2 + branch d x ≠ 0 := by
  intro hx
  have hprod := rationalized_product hd hD x
  rw [hx, mul_zero, eq_comm, mul_eq_zero, mul_eq_zero, sub_eq_zero] at hprod
  rcases hprod with (h | h) | h
  · norm_num at h
  · norm_num [h] at hx
  · have hbranch := branch_re_nonneg_ofReal hd hD (scale d)
    have hscale := scale_sq_lt_one hd hD
    rw [← h] at hx
    have hr := congrArg Complex.re hx
    simp only [add_re, sub_re, one_re, zero_re, ← ofReal_pow, ofReal_re] at hr
    linarith

/-- The value of the continued square root at the removable pole. -/
theorem branch_at_scale {d : ℝ} (hd : 0 < d) (hD : d < 1) :
    branch d (scale d) = 1 - (scale d : ℂ) ^ 2 := by
  have h := rationalized_product hd hD (scale d : ℂ)
  rw [sub_self, mul_zero] at h
  have hden := rationalized_denominator_ne_zero hd hD (scale d : ℂ)
  exact (sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hden)).symm

theorem analyticGenerating_analyticAt {d : ℝ} (hd : 0 < d) (hD : d < 1)
    {x : ℂ} (hx : x ∈ slitDomain d) : AnalyticAt ℂ (analyticGenerating d) x :=
  analyticAt_const.div ((analyticAt_const.sub (analyticAt_id.pow 2)).add (branch_analyticAt hx))
    (rationalized_denominator_ne_zero hd hD x)

@[simp] theorem analyticGenerating_zero (d : ℝ) : analyticGenerating d 0 = 1 := by
  norm_num [analyticGenerating]

theorem analyticGenerating_eq_quotient {d : ℝ} (hd : 0 < d) (hD : d < 1)
    {x : ℂ} (hx : x ≠ 0) (hxc : x ≠ (scale d : ℂ)) :
    analyticGenerating d x = (1 - x ^ 2 - branch d x) / (2 * x * ((scale d : ℂ) - x)) := by
  unfold analyticGenerating
  have hden := rationalized_denominator_ne_zero hd hD x
  have hsub : ((scale d : ℂ) - x) ≠ 0 := sub_ne_zero.mpr hxc.symm
  apply (div_eq_div_iff hden (mul_ne_zero (mul_ne_zero (by norm_num) hx) hsub)).mpr
  rw [rationalized_product hd hD]
  ring

theorem analyticGenerating_quadratic {d : ℝ} (hd : 0 < d) (hD : d < 1) (x : ℂ) :
    analyticGenerating d x = 1 + x ^ 2 * analyticGenerating d x +
      x * ((scale d : ℂ) - x) * analyticGenerating d x ^ 2 := by
  let a : ℂ := 1 - x ^ 2 + branch d x
  have ha : a ≠ 0 := rationalized_denominator_ne_zero hd hD x
  have hab : (1 - x ^ 2 - branch d x) * a = 4 * x * ((scale d : ℂ) - x) :=
    rationalized_product hd hD x
  change 2 / a = 1 + x ^ 2 * (2 / a) + x * ((scale d : ℂ) - x) * (2 / a) ^ 2
  have hX : x * ((scale d : ℂ) - x) = ((1 - x ^ 2 - branch d x) * a) / 4 := by
    rw [hab]
    ring
  rw [hX]
  field_simp [ha]
  dsimp [a]
  ring

private def Expands (p : PowerSeries ℂ) (f : ℂ → ℂ) : Prop :=
  HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff ℂ n p)) 0

private theorem expands_iff (p : PowerSeries ℂ) (f : ℂ → ℂ) :
    Expands p f ↔ ∀ᶠ z in 𝓝 0, HasSum (fun n => z ^ n * PowerSeries.coeff ℂ n p) (f z) := by
  simp [Expands, hasFPowerSeriesAt_iff, FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul]

private theorem expands_const (c : ℂ) : Expands (PowerSeries.C ℂ c) (fun _ => c) := by
  rw [expands_iff]
  filter_upwards with z
  refine (hasSum_ite_eq (0 : ℕ) c).congr_fun ?_
  intro n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [PowerSeries.coeff_C]
  · simp [PowerSeries.coeff_C, hn]

private theorem expands_one : Expands 1 (fun _ => 1) := by
  simpa using expands_const (1 : ℂ)

private theorem expands_X : Expands PowerSeries.X id := by
  rw [expands_iff]
  filter_upwards with z
  refine (hasSum_ite_eq (1 : ℕ) z).congr_fun ?_
  intro n
  rcases eq_or_ne n 1 with rfl | hn
  · simp [PowerSeries.coeff_X]
  · simp [PowerSeries.coeff_X, hn]

private theorem Expands.add {p q : PowerSeries ℂ} {f g : ℂ → ℂ}
    (hp : Expands p f) (hq : Expands q g) : Expands (p + q) (fun z => f z + g z) := by
  rw [expands_iff] at hp hq ⊢
  filter_upwards [hp, hq] with z hz hz'
  simpa only [map_add, mul_add] using hz.add hz'

private theorem Expands.sub {p q : PowerSeries ℂ} {f g : ℂ → ℂ}
    (hp : Expands p f) (hq : Expands q g) : Expands (p - q) (fun z => f z - g z) := by
  rw [expands_iff] at hp hq ⊢
  filter_upwards [hp, hq] with z hz hz'
  simpa only [map_sub, mul_sub] using hz.sub hz'

private theorem Expands.eventually_summable_norm {p : PowerSeries ℂ} {f : ℂ → ℂ}
    (hp : Expands p f) : ∀ᶠ z in 𝓝 0, Summable (fun n => ‖z ^ n * PowerSeries.coeff ℂ n p‖) := by
  obtain ⟨r, hr⟩ := hp
  filter_upwards [EMetric.ball_mem_nhds (0 : ℂ) hr.r_pos] with z hz
  have hz' := EMetric.ball_subset_ball hr.r_le hz
  simpa only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, mul_comm] using
    (FormalMultilinearSeries.summable_norm_apply _ hz')

private theorem Expands.mul {p q : PowerSeries ℂ} {f g : ℂ → ℂ}
    (hp : Expands p f) (hq : Expands q g) : Expands (p * q) (fun z => f z * g z) := by
  rw [expands_iff]
  filter_upwards [(expands_iff _ _).mp hp, (expands_iff _ _).mp hq,
    hp.eventually_summable_norm, hq.eventually_summable_norm] with z hf hg hfN hgN
  let u : ℕ → ℂ := fun n => z ^ n * PowerSeries.coeff ℂ n p
  let v : ℕ → ℂ := fun n => z ^ n * PowerSeries.coeff ℂ n q
  have habs := summable_norm_sum_mul_antidiagonal_of_summable_norm (f := u) (g := v) hfN hgN
  have h := habs.of_norm.hasSum
  rw [← tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm (f := u) (g := v) hfN hgN] at h
  change HasSum _ ((∑' n, z ^ n * PowerSeries.coeff ℂ n p) *
    (∑' n, z ^ n * PowerSeries.coeff ℂ n q)) at h
  rw [hf.tsum_eq, hg.tsum_eq] at h
  refine h.congr_fun ?_
  intro n
  rw [PowerSeries.coeff_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← Finset.mem_antidiagonal.mp hk, pow_add]
  dsimp [u, v]
  ring

private theorem Expands.unique {p q : PowerSeries ℂ} {f : ℂ → ℂ}
    (hp : Expands p f) (hq : Expands q f) : p = q := by
  apply PowerSeries.ext
  intro n
  have h := hp.eq_formalMultilinearSeries hq
  simpa only [FormalMultilinearSeries.coeff_ofScalars] using
    congrArg (fun s : FormalMultilinearSeries ℂ ℂ ℂ => s.coeff n) h

private theorem formal_quadratic_unique (c : ℂ) {p q : PowerSeries ℂ}
    (hp : p = 1 + PowerSeries.X ^ 2 * p +
      PowerSeries.X * (PowerSeries.C ℂ c - PowerSeries.X) * p ^ 2)
    (hq : q = 1 + PowerSeries.X ^ 2 * q +
      PowerSeries.X * (PowerSeries.C ℂ c - PowerSeries.X) * q ^ 2) : p = q := by
  let r := p - q
  let s : PowerSeries ℂ := PowerSeries.X +
    (PowerSeries.C ℂ c - PowerSeries.X) * (p + q)
  have hr : r = PowerSeries.X * (s * r) := by
    dsimp [r, s]
    linear_combination hp - hq
  have hzero (n : ℕ) : PowerSeries.coeff ℂ n r = 0 := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      conv_lhs => rw [hr]
      cases n with
      | zero => simp [PowerSeries.coeff_zero_eq_constantCoeff]
      | succ n =>
        rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mul]
        apply Finset.sum_eq_zero
        intro i hi
        have hi' := Finset.mem_antidiagonal.mp hi
        rw [ih i.2 (by omega), mul_zero]
  apply sub_eq_zero.mp
  change r = 0
  apply PowerSeries.ext
  intro n
  simpa using hzero n

private theorem analyticGenerating_expands {d : ℝ} (hd : 0 < d) (hD : d < 1) :
    Expands (PowerSeries.map Complex.ofRealHom (FirstReturn.scaled (scale d)))
      (analyticGenerating d) := by
  obtain ⟨p, hp⟩ := analyticGenerating_analyticAt hd hD (zero_mem_slitDomain d)
  let q : PowerSeries ℂ := PowerSeries.mk p.coeff
  have hq : Expands q (analyticGenerating d) := by
    rw [expands_iff]
    have h := hasFPowerSeriesAt_iff.mp hp
    simpa [q, PowerSeries.coeff_mk, smul_eq_mul] using h
  have hX := expands_X
  have hC := expands_const (scale d : ℂ)
  have hRHS := (expands_one.add ((hX.mul hX).mul hq)).add
    ((hX.mul (hC.sub hX)).mul (hq.mul hq))
  have hEQ : q = 1 + PowerSeries.X ^ 2 * q +
      PowerSeries.X * (PowerSeries.C ℂ (scale d) - PowerSeries.X) * q ^ 2 := by
    apply hq.unique
    change HasFPowerSeriesAt _ _ _ at hRHS ⊢
    simp only [pow_two]
    refine hRHS.congr (Filter.Eventually.of_forall fun x => ?_)
    simpa [pow_two] using (analyticGenerating_quadratic hd hD x).symm
  have hFormal := congrArg (PowerSeries.map Complex.ofRealHom)
    (FirstReturn.scaled_eq (scale d) (scale_pos hd).ne')
  let f := PowerSeries.map Complex.ofRealHom (FirstReturn.scaled (scale d))
  have hf : f = 1 + PowerSeries.X ^ 2 * f +
      PowerSeries.X * (PowerSeries.C ℂ (scale d) - PowerSeries.X) * f ^ 2 := by
    simpa [f] using hFormal
  change Expands f (analyticGenerating d)
  rw [← formal_quadratic_unique (scale d : ℂ) hEQ hf]
  exact hq

/-- The analytic branch has the Taylor coefficients of the Catalan-word series. -/
theorem analyticGenerating_hasFPowerSeriesAt {d : ℝ} (hd : 0 < d) (hD : d < 1) :
    HasFPowerSeriesAt (analyticGenerating d)
      (FormalMultilinearSeries.ofScalars ℂ
        (fun n => ((scale d ^ n * (C n).eval (1 - (scale d ^ 2)⁻¹) : ℝ) : ℂ))) 0 := by
  simpa only [Expands, PowerSeries.coeff_map, FirstReturn.coeff_scaled]
    using analyticGenerating_expands hd hD

private theorem factor_mem_slitPlane {x ζ : ℂ} (h : ‖x‖ < ‖ζ‖) :
    1 - x / ζ ∈ slitPlane := by
  apply mem_slitPlane_of_norm_lt_one (z := -(x / ζ))
  rw [norm_neg, norm_div]
  exact (div_lt_one (norm_nonneg x |>.trans_lt h)).mpr h

/-- Every smaller closed disk lies inside the domain of the analytic branch. -/
theorem closedBall_subset_slitDomain {d r : ℝ} (hd : 0 < d) (hD : d < 1)
    (hr : r < radius d) : Metric.closedBall (0 : ℂ) r ⊆ slitDomain d := by
  intro x hx
  have hn : ‖x‖ < ‖nearPoint d‖ :=
    (mem_closedBall_zero_iff.mp hx).trans_lt (by rwa [nearPoint_norm hd hD])
  have hf := hn.trans (norm_order hd hD)
  exact ⟨factor_mem_slitPlane hn, factor_mem_slitPlane (by simpa using hn),
    factor_mem_slitPlane hf, factor_mem_slitPlane (by simpa using hf)⟩

/-- The starting circle in the contour argument extracts the desired coefficient. -/
theorem analyticGenerating_cauchyCoeff {d : ℝ} (hd : 0 < d) (hD : d < 1)
    {r : NNReal} (h₀ : 0 < r) (hr : (r : ℝ) < radius d) (n : ℕ) :
    ((scale d ^ n * (C n).eval (1 - (scale d ^ 2)⁻¹) : ℝ) : ℂ) =
      (2 * (Real.pi : ℂ) * I)⁻¹ *
        (∮ z in C(0, (r : ℝ)), (z⁻¹) ^ (n + 1) * analyticGenerating d z) := by
  have hDiff : DifferentiableOn ℂ (analyticGenerating d) (Metric.closedBall 0 (r : ℝ)) :=
    fun x hx => (analyticGenerating_analyticAt hd hD
      (closedBall_subset_slitDomain hd hD hr hx)).differentiableAt.differentiableWithinAt
  have h := (analyticGenerating_hasFPowerSeriesAt hd hD).eq_formalMultilinearSeries
    ((hDiff.hasFPowerSeriesOnBall h₀).hasFPowerSeriesAt)
  have hcoeff := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff n) h
  simp only [FormalMultilinearSeries.coeff_ofScalars] at hcoeff
  change _ = cauchyPowerSeries (analyticGenerating d) 0 (r : ℝ) n (fun _ => 1) at hcoeff
  rw [cauchyPowerSeries_apply] at hcoeff
  simpa only [one_div, sub_zero, smul_eq_mul, pow_succ, mul_assoc] using hcoeff

end CatalanStrictPeaks.CutGeometry
