import CatalanStrictPeaksLogRoot
import OpenMathResearch.LogarithmicContour

/-!
# Logarithmic sectors for the Catalan coefficient contour

The cut angles occur in the order near, far, conjugate far, conjugate near
on a positively oriented circle starting on the positive real axis.
-/

namespace CatalanStrictPeaks.CutGeometry

open Complex Set MeasureTheory
open scoped ComplexConjugate Interval

private noncomputable def cutPoint (d : ℝ) (i : Fin 4) : ℂ :=
  match i.val with
  | 0 => nearPoint d
  | 1 => farPoint d
  | 2 => conj (farPoint d)
  | _ => conj (nearPoint d)

private theorem near_arg_bounds {d : ℝ} (hd : 0 < d) (hD : d < 1) :
    0 < (nearPoint d).arg ∧ (nearPoint d).arg < Real.pi / 2 := by
  have him := nearPoint_im_pos hd hD
  refine ⟨lt_of_le_of_ne (arg_nonneg_iff.mpr him.le) ?_,
    arg_lt_pi_div_two_iff.mpr (Or.inl (nearPoint_re_pos hd))⟩
  intro h
  exact him.ne' (arg_eq_zero_iff.mp h.symm).2

private theorem far_arg_bounds {d : ℝ} (hd : 0 < d) (hD : d < 1) :
    Real.pi / 2 < (farPoint d).arg ∧ (farPoint d).arg < Real.pi := by
  have him := farPoint_im_pos hd hD
  have hre := farPoint_re_neg hd
  refine ⟨lt_of_not_ge ?_, arg_lt_pi_iff.mpr (Or.inr him.ne')⟩
  intro h
  exact (arg_le_pi_div_two_iff.mp h).elim (not_le_of_gt hre) (not_lt_of_gt him)

/-- The real-axis endpoints and the four cut angles in increasing order. -/
noncomputable def sectorAngle (d : ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => (nearPoint d).arg
  | 2 => (farPoint d).arg
  | 3 => 2 * Real.pi - (farPoint d).arg
  | 4 => 2 * Real.pi - (nearPoint d).arg
  | _ => 2 * Real.pi

private theorem sectorAngle_step {d : ℝ} (hd : 0 < d) (hD : d < 1) {j : ℕ}
    (hj : j ≤ 4) : sectorAngle d j < sectorAngle d (j + 1) := by
  have hn := near_arg_bounds hd hD
  have hf := far_arg_bounds hd hD
  interval_cases j <;> simp only [sectorAngle, Nat.reduceAdd] <;>
    linarith [hn.1, hn.2, hf.1, hf.2]

private theorem sectorAngle_mono {d : ℝ} (hd : 0 < d) (hD : d < 1) :
    Monotone (sectorAngle d) := by
  apply monotone_nat_of_le_succ
  intro j
  by_cases hj : j ≤ 4
  · exact (sectorAngle_step hd hD hj).le
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 5 := ⟨j - 5, by omega⟩
    rfl

private theorem cutPoint_polar {d : ℝ} (hd : 0 < d) (hD : d < 1) (i : Fin 4) :
    (‖cutPoint d i‖ : ℂ) * exp ((sectorAngle d (i.val + 1) : ℂ) * I) = cutPoint d i := by
  have hn := near_arg_bounds hd hD
  have hf := far_arg_bounds hd hD
  have hPolarConj (u : ℂ) (hu : u.arg < Real.pi) :
      (‖conj u‖ : ℂ) * exp (((2 * Real.pi - u.arg : ℝ) : ℂ) * I) = conj u := by
    have hArg : (conj u).arg = -u.arg := by simp [Complex.arg_conj, hu.ne]
    have hExp : exp (((2 * Real.pi - u.arg : ℝ) : ℂ) * I) =
        exp (((-u.arg : ℝ) : ℂ) * I) := by
      rw [show 2 * Real.pi - u.arg = -u.arg + 2 * Real.pi by ring]
      push_cast
      exact Complex.exp_mul_I_periodic (-(u.arg : ℂ))
    rw [hExp, ← hArg]
    exact norm_mul_exp_arg_mul_I _
  fin_cases i
  · exact norm_mul_exp_arg_mul_I _
  · exact norm_mul_exp_arg_mul_I _
  · exact hPolarConj _ hf.2
  · exact hPolarConj _ (by linarith [hn.2, Real.pi_pos])

/-- Choose a representative of each cut angle immediately below the sector. -/
private noncomputable def liftedAngle (d : ℝ) (j : ℕ) (i : Fin 4) : ℝ :=
  if i.val < j then sectorAngle d (i.val + 1) else sectorAngle d (i.val + 1) - 2 * Real.pi

private theorem liftedAngle_polar {d : ℝ} (hd : 0 < d) (hD : d < 1) (j : ℕ) (i : Fin 4) :
    (‖cutPoint d i‖ : ℂ) * exp ((liftedAngle d j i : ℂ) * I) = cutPoint d i := by
  unfold liftedAngle
  split_ifs
  · exact cutPoint_polar hd hD i
  · rw [show exp (((sectorAngle d (i.val + 1) - 2 * Real.pi : ℝ) : ℂ) * I) =
        exp ((sectorAngle d (i.val + 1) : ℂ) * I) by
      push_cast
      exact Complex.exp_mul_I_periodic.sub_eq (sectorAngle d (i.val + 1) : ℂ)]
    exact cutPoint_polar hd hD i

private theorem liftedAngle_within_strip {d : ℝ} (hd : 0 < d) (hD : d < 1)
    {j : ℕ} (hj : j ≤ 4) (i : Fin 4) {y : ℝ}
    (hy : y ∈ Icc (sectorAngle d j) (sectorAngle d (j + 1))) :
    liftedAngle d j i ≤ y ∧ y ≤ liftedAngle d j i + 2 * Real.pi := by
  have hmono := sectorAngle_mono hd hD
  have hβ₀ : 0 ≤ sectorAngle d (i.val + 1) := hmono (Nat.zero_le _)
  have hβ₁ : sectorAngle d (i.val + 1) ≤ 2 * Real.pi := hmono (show i.val + 1 ≤ 5 by omega)
  have hlow : 0 ≤ sectorAngle d j := hmono (Nat.zero_le _)
  have hhigh : sectorAngle d (j + 1) ≤ 2 * Real.pi := hmono (show j + 1 ≤ 5 by omega)
  unfold liftedAngle
  split_ifs with hi
  · refine ⟨(hmono (show i.val + 1 ≤ j by omega)).trans hy.1, ?_⟩
    linarith [hy.2]
  · refine ⟨?_, hy.2.trans ?_⟩
    · linarith [hy.1]
    · simpa using hmono (show j + 1 ≤ i.val + 1 by omega)

private noncomputable def sectorFactor (d : ℝ) (j : ℕ) (i : Fin 4) (z : ℂ) : ℂ :=
  logStripRoot ‖cutPoint d i‖ (z - (liftedAngle d j i : ℂ) * I)

private noncomputable def logBranch (d : ℝ) (j : ℕ) (z : ℂ) : ℂ :=
  ∏ i : Fin 4, sectorFactor d j i z

private theorem cutPoint_norm_pos {d : ℝ} (hd : 0 < d) (hD : d < 1) (i : Fin 4) :
    0 < ‖cutPoint d i‖ := by
  have hn := (nearPoint_norm hd hD).symm ▸ radius_pos hd.le
  have hf := hn.trans (norm_order hd hD)
  fin_cases i
  · exact hn
  · exact hf
  · simpa [cutPoint] using hf
  · simpa [cutPoint] using hn

private theorem cutFactor_product (d : ℝ) (z : ℂ) :
    (∏ i : Fin 4, cutFactor (cutPoint d i) z) = branch d z := by
  simp [Fin.prod_univ_succ, cutPoint, branch] <;> ring

private theorem logBranch_continuous {d : ℝ} (hd : 0 < d) (hD : d < 1) (j : ℕ) :
    Continuous (logBranch d j) := by
  unfold logBranch sectorFactor
  apply continuous_finset_prod Finset.univ
  intro i _
  exact (logStripRoot_continuous (cutPoint_norm_pos hd hD i)).comp (by fun_prop)

private theorem logBranch_sq {d : ℝ} (hd : 0 < d) (hD : d < 1) {j : ℕ} (hj : j ≤ 4)
    {z : ℂ} (hz : z.im ∈ Icc (sectorAngle d j) (sectorAngle d (j + 1))) :
    logBranch d j z ^ 2 = quartic (scale d) (exp z) := by
  rw [← branch_sq hd hD, ← cutFactor_product, logBranch, ← Finset.prod_pow, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro i _
  obtain ⟨h₁, h₂⟩ := liftedAngle_within_strip hd hD hj i hz
  rw [sectorFactor, logStripRoot_sq (cutPoint_norm_pos hd hD i), cutFactor, principalRoot_sq, Complex.exp_sub,
    div_div, mul_comm (exp _), liftedAngle_polar hd hD]
  · simp [Complex.mul_im]; linarith
  · simp [Complex.mul_im]; linarith

private theorem logBranch_eq_branch_of_lifts {d : ℝ} (hd : 0 < d) (hD : d < 1)
    {j : ℕ} {z : ℂ} (hz : ∀ i : Fin 4, liftedAngle d j i < z.im ∧
      z.im < liftedAngle d j i + 2 * Real.pi) :
    logBranch d j z = branch d (exp z) := by
  rw [← cutFactor_product, logBranch]
  apply Finset.prod_congr rfl
  intro i _
  rw [sectorFactor, logStripRoot_eq_cutFactor (cutPoint_norm_pos hd hD i) (hz i).1 (hz i).2,
    liftedAngle_polar hd hD]

private theorem logBranch_eq_branch_inside {d : ℝ} (hd : 0 < d) (hD : d < 1)
    {j : ℕ} (hj : j ≤ 4) {z : ℂ}
    (hz : z.im ∈ Ioo (sectorAngle d j) (sectorAngle d (j + 1))) :
    logBranch d j z = branch d (exp z) := by
  apply logBranch_eq_branch_of_lifts hd hD
  intro i
  have h₁ := (liftedAngle_within_strip hd hD hj i
    (show sectorAngle d j ∈ Icc (sectorAngle d j) (sectorAngle d (j + 1)) from
      ⟨le_rfl, (sectorAngle_step hd hD hj).le⟩)).1
  have h₂ := (liftedAngle_within_strip hd hD hj i
    (show sectorAngle d (j + 1) ∈ Icc (sectorAngle d j) (sectorAngle d (j + 1)) from
      ⟨(sectorAngle_step hd hD hj).le, le_rfl⟩)).2
  exact ⟨h₁.trans_lt hz.1, hz.2.trans_le h₂⟩

private theorem logBranch_eq_branch_inner {d : ℝ} (hd : 0 < d) (hD : d < 1)
    {j : ℕ} (hj : j ≤ 4) {z : ℂ}
    (hz : z.im ∈ Icc (sectorAngle d j) (sectorAngle d (j + 1)))
    (hr : ‖exp z‖ ≤ radius d) :
    logBranch d j z = branch d (exp z) := by
  rw [← cutFactor_product, logBranch]
  apply Finset.prod_congr rfl
  intro i _
  have hRadius : radius d ≤ ‖cutPoint d i‖ := by
    have h : radius d ≤ ‖farPoint d‖ := by
      rw [← nearPoint_norm hd hD]
      exact (norm_order hd hD).le
    fin_cases i
    · exact (nearPoint_norm hd hD).ge
    · exact h
    · simpa [cutPoint] using h
    · simpa [cutPoint] using (nearPoint_norm hd hD).ge
  obtain ⟨h₁, h₂⟩ := liftedAngle_within_strip hd hD hj i hz
  rw [sectorFactor, logStripRoot_eq_cutFactor_of_le_radius (cutPoint_norm_pos hd hD i) h₁ h₂
    (hr.trans hRadius), liftedAngle_polar hd hD]

private theorem cutPoint_im_ne_zero {d : ℝ} (hd : 0 < d) (hD : d < 1) (i : Fin 4) :
    (cutPoint d i).im ≠ 0 := by
  have hn := (nearPoint_im_pos hd hD).ne'
  have hf := (farPoint_im_pos hd hD).ne'
  fin_cases i
  · exact hn
  · exact hf
  · simpa [cutPoint, Complex.conj_im] using hf
  · simpa [cutPoint, Complex.conj_im] using hn

private theorem exp_im_ne_zero_on_cut {d : ℝ} (hd : 0 < d) (hD : d < 1)
    (j : ℕ) (i : Fin 4) (z : ℂ)
    (hy : z.im = liftedAngle d j i ∨ z.im = liftedAngle d j i + 2 * Real.pi) :
    (exp z).im ≠ 0 := by
  have hPolar := liftedAngle_polar hd hD j i
  have hExp : exp ((z.im : ℂ) * I) = exp ((liftedAngle d j i : ℂ) * I) := by
    rcases hy with hy | hy
    · rw [hy]
    · rw [hy]
      push_cast
      exact Complex.exp_mul_I_periodic (liftedAngle d j i : ℂ)
  have hr : (‖cutPoint d i‖ : ℂ) ≠ 0 := by exact_mod_cast (cutPoint_norm_pos hd hD i).ne'
  have hS : exp z = ((Real.exp z.re / ‖cutPoint d i‖ : ℝ) : ℂ) * cutPoint d i := by
    conv_lhs => rw [← Complex.re_add_im z, exp_add, hExp]
    rw [← hPolar, ← Complex.ofReal_exp]
    push_cast
    field_simp [hr] <;> ring
  rw [hS, Complex.mul_im]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  exact mul_ne_zero (div_pos (Real.exp_pos _) (cutPoint_norm_pos hd hD i)).ne'
    (cutPoint_im_ne_zero hd hD i)

private theorem logGenerating_denominator_ne_zero {d : ℝ} (hd : 0 < d) (hD : d < 1)
    {j : ℕ} (hj : j ≤ 4) {z : ℂ}
    (hz : z.im ∈ Icc (sectorAngle d j) (sectorAngle d (j + 1))) :
    1 - (exp z) ^ 2 + logBranch d j z ≠ 0 := by
  intro h
  have hprod : (1 - (exp z) ^ 2 - logBranch d j z) *
      (1 - (exp z) ^ 2 + logBranch d j z) = 4 * exp z * ((scale d : ℂ) - exp z) := by
    calc
      _ = (1 - (exp z) ^ 2) ^ 2 - logBranch d j z ^ 2 := by ring
      _ = _ := by rw [logBranch_sq hd hD hj hz]; unfold quartic; ring
  rw [h, mul_zero, eq_comm, mul_eq_zero, mul_eq_zero] at hprod
  have hexp : exp z = (scale d : ℂ) := by
    rcases hprod with (h4 | he) | hs
    · norm_num at h4
    · exact (exp_ne_zero _ he).elim
    · exact (sub_eq_zero.mp hs).symm
  have hIm : (exp z).im = 0 := by simp [hexp]
  have hstrict (i : Fin 4) :
      liftedAngle d j i < z.im ∧ z.im < liftedAngle d j i + 2 * Real.pi := by
    obtain ⟨hlo, hhi⟩ := liftedAngle_within_strip hd hD hj i hz
    refine ⟨hlo.lt_of_ne ?_, hhi.lt_of_ne ?_⟩
    · intro he
      exact exp_im_ne_zero_on_cut hd hD j i z (Or.inl he.symm) hIm
    · intro he
      exact exp_im_ne_zero_on_cut hd hD j i z (Or.inr he) hIm
  rw [logBranch_eq_branch_of_lifts hd hD hstrict] at h
  exact rationalized_denominator_ne_zero hd hD _ h

/-- The coefficient integrand continued to a closed logarithmic sector. -/
noncomputable def logSector (d : ℝ) (n j : ℕ) (z : ℂ) : ℂ :=
  (exp z)⁻¹ ^ n * (2 / (1 - (exp z) ^ 2 + logBranch d j z))

private noncomputable def logIntegrand (d : ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  (exp z)⁻¹ ^ n * analyticGenerating d (exp z)

private theorem exp_mem_slitDomain {d : ℝ} (hd : 0 < d) (hD : d < 1)
    {j : ℕ} (hj : j ≤ 4) {z : ℂ}
    (hz : z.im ∈ Ioo (sectorAngle d j) (sectorAngle d (j + 1))) :
    exp z ∈ slitDomain d := by
  have hFactor (i : Fin 4) : 1 - exp z / cutPoint d i ∈ slitPlane := by
    have h₁ := (liftedAngle_within_strip hd hD hj i
      (show sectorAngle d j ∈ Icc (sectorAngle d j) (sectorAngle d (j + 1)) from
        ⟨le_rfl, (sectorAngle_step hd hD hj).le⟩)).1
    have h₂ := (liftedAngle_within_strip hd hD hj i
      (show sectorAngle d (j + 1) ∈ Icc (sectorAngle d j) (sectorAngle d (j + 1)) from
        ⟨(sectorAngle_step hd hD hj).le, le_rfl⟩)).2
    rw [← liftedAngle_polar hd hD j i]
    exact exp_div_mem_slitPlane_shift (cutPoint_norm_pos hd hD i)
      (h₁.trans_lt hz.1) (hz.2.trans_le h₂)
  exact ⟨hFactor 0, hFactor 3, hFactor 1, hFactor 2⟩

private theorem logSector_continuousOn {d : ℝ} (hd : 0 < d) (hD : d < 1)
    {j : ℕ} (hj : j ≤ 4) (n : ℕ) :
    ContinuousOn (logSector d n j) (im ⁻¹' Icc (sectorAngle d j) (sectorAngle d (j + 1))) := by
  have hInv : Continuous fun z : ℂ => (exp z)⁻¹ := continuous_exp.inv₀ exp_ne_zero
  have hDen : Continuous (fun z : ℂ => 1 - (exp z) ^ 2 + logBranch d j z) :=
    (continuous_const.sub (continuous_exp.pow 2)).add (logBranch_continuous hd hD j)
  exact (hInv.pow n).continuousOn.mul
    (continuousOn_const.div hDen.continuousOn fun z hz =>
      logGenerating_denominator_ne_zero hd hD hj hz)

private theorem logSector_differentiableOn {d : ℝ} (hd : 0 < d) (hD : d < 1)
    {j : ℕ} (hj : j ≤ 4) (n : ℕ) :
    DifferentiableOn ℂ (logSector d n j) (im ⁻¹' Ioo (sectorAngle d j) (sectorAngle d (j + 1))) := by
  have hDiff : DifferentiableOn ℂ (logIntegrand d n)
      (im ⁻¹' Ioo (sectorAngle d j) (sectorAngle d (j + 1))) := by
    intro z hz
    have hInv := (differentiable_exp z).inv (exp_ne_zero z)
    have hGen := (analyticGenerating_analyticAt hd hD
      (exp_mem_slitDomain hd hD hj hz)).differentiableAt.comp z (differentiable_exp z)
    exact ((hInv.pow n).mul hGen).differentiableWithinAt
  apply hDiff.congr
  intro z hz
  simp only [logSector, logIntegrand, analyticGenerating, logBranch_eq_branch_inside hd hD hj hz]

private theorem logSector_periodic_boundary (d : ℝ) (n : ℕ) (x : ℝ) :
    logSector d n 0 (x : ℂ) = logSector d n 4 ((x : ℂ) + (2 * Real.pi : ℝ) * I) := by
  have hExp : exp ((x : ℂ) + (2 * Real.pi : ℝ) * I) = exp (x : ℂ) := by
    push_cast
    exact Complex.exp_periodic (x : ℂ)
  have hBranch : logBranch d 0 (x : ℂ) = logBranch d 4 ((x : ℂ) + (2 * Real.pi : ℝ) * I) := by
    unfold logBranch
    apply Finset.prod_congr rfl
    intro i _
    simp only [sectorFactor, liftedAngle, Nat.not_lt_zero, if_false, i.isLt, if_true]
    congr 1
    push_cast
    ring
  simp only [logSector, hExp, hBranch]

private theorem inside_disk_norm {r : ℝ} (hr : 0 < r) (y : ℝ) :
    ‖exp ((Real.log r : ℂ) + (y : ℂ) * I)‖ = r := by
  simp [Complex.norm_exp, Complex.mul_re, Real.exp_log hr]

private theorem logIntegrand_continuous_on_circle {d r : ℝ} (hd : 0 < d) (hD : d < 1)
    (h₀ : 0 < r) (hr : r < radius d) (n : ℕ) :
    Continuous (fun y : ℝ => logIntegrand d n ((Real.log r : ℂ) + (y : ℂ) * I)) := by
  rw [continuous_iff_continuousAt]
  intro y
  let x : ℝ → ℂ := fun t => exp ((Real.log r : ℂ) + (t : ℂ) * I)
  have hx : x y ∈ Metric.closedBall (0 : ℂ) r :=
    mem_closedBall_zero_iff.mpr (inside_disk_norm h₀ y).le
  have hExp : ContinuousAt x y := by dsimp [x]; fun_prop
  have hGen := (analyticGenerating_analyticAt hd hD
    (closedBall_subset_slitDomain hd hD hr hx)).continuousAt
  exact ((hExp.inv₀ (exp_ne_zero _)).pow n).mul (hGen.comp hExp)

/-- The finite deformation isolates the outer arcs and the four jump integrals
in logarithmic radius. -/
theorem analyticGenerating_finiteDeformation {d : ℝ} (hd : 0 < d) (hD : d < 1)
    {r : NNReal} (h₀ : 0 < r) (hr : (r : ℝ) < radius d) (n : ℕ)
    {b : ℝ} (hb : Real.log r ≤ b) :
    ((scale d ^ n * (C n).eval (1 - (scale d ^ 2)⁻¹) : ℝ) : ℂ) =
      (2 * (Real.pi : ℂ) * I)⁻¹ * (
        (∑ j ∈ Finset.range 5,
          I • (∫ y in sectorAngle d j..sectorAngle d (j + 1),
            logSector d n j ((b : ℂ) + (y : ℂ) * I))) +
        ∑ j ∈ Finset.range 4, (
          ∫ x in Real.log r..b,
            logSector d n (j + 1) ((x : ℂ) + (sectorAngle d (j + 1) : ℂ) * I) -
              logSector d n j ((x : ℂ) + (sectorAngle d (j + 1) : ℂ) * I))) := by
  have h₀R : 0 < (r : ℝ) := by exact_mod_cast h₀
  let inner : ℝ → ℂ := fun y => logIntegrand d n ((Real.log r : ℂ) + (y : ℂ) * I)
  have hTransport := OpenMathResearch.LogarithmicContour.deform (m := 4) hb
    (sectorAngle d) (sectorAngle_mono hd hD) (logSector d n) inner
    (fun j hj => (logSector_continuousOn hd hD hj n).mono fun z hz => hz.2)
    (fun j hj => (logSector_differentiableOn hd hD hj n).mono fun z hz => hz.2)
    (by
      intro j hj y hy
      have hIm : (((Real.log r : ℂ) + (y : ℂ) * I)).im = y := by simp [Complex.mul_im]
      have hR := (inside_disk_norm h₀R y).le.trans hr.le
      simp only [logSector, inner, logIntegrand, analyticGenerating,
        logBranch_eq_branch_inner hd hD hj (hIm.symm ▸ hy) hR])
    (fun j _ => (logIntegrand_continuous_on_circle hd hD h₀R hr n).intervalIntegrable _ _)
    (by
      intro x _
      simpa only [sectorAngle, Complex.ofReal_zero, zero_mul, add_zero]
        using logSector_periodic_boundary d n x)
  have hAngular := OpenMathResearch.LogarithmicContour.circleIntegral_eq_angular
    (analyticGenerating d) (Real.log r) n
  rw [Real.exp_log h₀R] at hAngular
  rw [analyticGenerating_cauchyCoeff hd hD h₀ hr n, hAngular]
  exact congrArg ((2 * (Real.pi : ℂ) * I)⁻¹ * ·) hTransport

private noncomputable def onCut (d : ℝ) (j : Fin 4) (x : ℝ) : ℂ :=
  (x : ℂ) + (sectorAngle d (j.val + 1) : ℂ) * I

private noncomputable def otherFactors (d : ℝ) (j : Fin 4) (x : ℝ) : ℂ :=
  ∏ i ∈ Finset.univ.erase j, sectorFactor d j.val i (onCut d j x)

private theorem sectorFactor_forward (d : ℝ) (j : Fin 4) (x : ℝ) :
    sectorFactor d (j.val + 1) j (onCut d j x) = logStripRoot ‖cutPoint d j‖ (x : ℂ) := by
  simp only [sectorFactor, onCut, liftedAngle, Nat.lt_succ_self, if_true, add_sub_cancel_right]

private theorem sectorFactor_backward (d : ℝ) (j : Fin 4) (x : ℝ) :
    sectorFactor d j.val j (onCut d j x) =
      logStripRoot ‖cutPoint d j‖ ((x : ℂ) + (2 * Real.pi : ℝ) * I) := by
  simp only [sectorFactor, onCut, liftedAngle, lt_irrefl, if_false]
  congr 1
  push_cast
  ring

private theorem logBranch_cut_difference (d : ℝ) (j : Fin 4) (x : ℝ) :
    logBranch d (j.val + 1) (onCut d j x) - logBranch d j.val (onCut d j x) =
      (logStripRoot ‖cutPoint d j‖ (x : ℂ) -
        logStripRoot ‖cutPoint d j‖ ((x : ℂ) + (2 * Real.pi : ℝ) * I)) * otherFactors d j x := by
  have hprod :
      (∏ i ∈ Finset.univ.erase j, sectorFactor d (j.val + 1) i (onCut d j x)) =
        otherFactors d j x := by
    unfold otherFactors
    apply Finset.prod_congr rfl
    intro i hi
    have hij : i.val ≠ j.val := fun h => (Finset.mem_erase.mp hi).1 (Fin.ext h)
    have h : (i.val < j.val + 1) ↔ i.val < j.val := by omega
    simp only [sectorFactor, liftedAngle, h]
  have hSplit (k : ℕ) :
      logBranch d k (onCut d j x) = sectorFactor d k j (onCut d j x) *
        ∏ i ∈ Finset.univ.erase j, sectorFactor d k i (onCut d j x) :=
    (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)).symm
  rw [hSplit, hSplit, hprod, sectorFactor_forward, sectorFactor_backward, sub_mul]

private theorem logSector_eq_quotient {d : ℝ} (hd : 0 < d) (hD : d < 1)
    (n : ℕ) {j : ℕ} (hj : j ≤ 4) {z : ℂ}
    (hz : z.im ∈ Icc (sectorAngle d j) (sectorAngle d (j + 1)))
    (hzc : exp z ≠ (scale d : ℂ)) :
    logSector d n j z = (exp z)⁻¹ ^ n *
      ((1 - (exp z) ^ 2 - logBranch d j z) / (2 * exp z * ((scale d : ℂ) - exp z))) := by
  unfold logSector
  congr 1
  have hDen := logGenerating_denominator_ne_zero hd hD hj hz
  have hSub := sub_ne_zero.mpr hzc.symm
  apply (div_eq_div_iff hDen (mul_ne_zero (mul_ne_zero (by norm_num) (exp_ne_zero z)) hSub)).mpr
  have hsq := logBranch_sq hd hD hj hz
  unfold quartic at hsq
  linear_combination hsq

private theorem logSector_cut_difference {d : ℝ} (hd : 0 < d) (hD : d < 1)
    (n : ℕ) (j : Fin 4) (x : ℝ) :
    logSector d n (j.val + 1) (onCut d j x) - logSector d n j.val (onCut d j x) =
      (exp (onCut d j x))⁻¹ ^ n *
        ((logStripRoot ‖cutPoint d j‖ (x : ℂ) -
          logStripRoot ‖cutPoint d j‖ ((x : ℂ) + (2 * Real.pi : ℝ) * I)) *
          (-otherFactors d j x / (2 * exp (onCut d j x) *
            ((scale d : ℂ) - exp (onCut d j x))))) := by
  let z := onCut d j x
  have hy : z.im = sectorAngle d (j.val + 1) := by simp [z, onCut, Complex.mul_im]
  have h₁ : j.val ≤ 4 := j.isLt.le
  have h₂ : j.val + 1 ≤ 4 := Nat.succ_le_of_lt j.isLt
  have hz₁ : z.im ∈ Icc (sectorAngle d j.val) (sectorAngle d (j.val + 1)) :=
    hy.symm ▸ ⟨(sectorAngle_step hd hD h₁).le, le_rfl⟩
  have hz₂ : z.im ∈ Icc (sectorAngle d (j.val + 1)) (sectorAngle d (j.val + 1 + 1)) :=
    hy.symm ▸ ⟨le_rfl, (sectorAngle_step hd hD h₂).le⟩
  have hzc : exp z ≠ (scale d : ℂ) := by
    intro he
    apply exp_im_ne_zero_on_cut hd hD j.val j z
    · right
      simp [hy, liftedAngle]
    · simp [he]
  change logSector d n (j.val + 1) z - logSector d n j.val z = _
  rw [logSector_eq_quotient hd hD n h₂ hz₂ hzc, logSector_eq_quotient hd hD n h₁ hz₁ hzc,
    ← mul_sub, ← sub_div]
  rw [show 1 - (exp z) ^ 2 - logBranch d (j.val + 1) z -
      (1 - (exp z) ^ 2 - logBranch d j.val z) =
        -(logBranch d (j.val + 1) z - logBranch d j.val z) by ring]
  dsimp [z]
  rw [logBranch_cut_difference]
  ring

/-- The inward part of each shared radial edge has no jump. -/
theorem logSector_jump_zero {d : ℝ} (hd : 0 < d) (hD : d < 1)
    (n : ℕ) (j : Fin 4) (x : ℝ) (hx : Real.exp x / ‖cutPoint d j‖ ≤ 1) :
    logSector d n (j.val + 1) (onCut d j x) - logSector d n j.val (onCut d j x) = 0 := by
  rw [logSector_cut_difference hd hD, logStripRoot_boundary_eq _ _ hx, sub_self,
    zero_mul, mul_zero]

/-- The outward part of each radial edge has the signed square-root jump. -/
theorem logSector_jump_sqrt {d : ℝ} (hd : 0 < d) (hD : d < 1)
    (n : ℕ) (j : Fin 4) (x : ℝ) (hx : 1 ≤ Real.exp x / ‖cutPoint d j‖) :
    logSector d n (j.val + 1) (onCut d j x) - logSector d n j.val (onCut d j x) =
      (exp (onCut d j x))⁻¹ ^ n *
        ((-2 * I * (Real.sqrt (Real.exp x / ‖cutPoint d j‖ - 1) : ℂ)) *
          (-otherFactors d j x / (2 * exp (onCut d j x) *
            ((scale d : ℂ) - exp (onCut d j x))))) := by
  rw [logSector_cut_difference hd hD, logStripRoot_jump _ _ hx]

end CatalanStrictPeaks.CutGeometry
