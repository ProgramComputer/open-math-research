import CatalanStrictPeaksLogRoot
import OpenMathResearch.LogarithmicContour
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Logarithmic sectors for the Catalan coefficient contour

The cut angles occur in the order near, far, conjugate far, conjugate near
on a positively oriented circle starting on the positive real axis.
-/

namespace CatalanStrictPeaks.CutGeometry

open Complex Set MeasureTheory Filter
open scoped ComplexConjugate Interval Topology

/-- The branch points in circular order, starting with the upper near point. -/
noncomputable def cutPoint (d : ℝ) (i : Fin 4) : ℂ :=
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

private theorem radius_le_cutPoint {d : ℝ} (hd : 0 < d) (hD : d < 1) (i : Fin 4) :
    radius d ≤ ‖cutPoint d i‖ := by
  have h : radius d ≤ ‖farPoint d‖ := by
    rw [← nearPoint_norm hd hD]
    exact (norm_order hd hD).le
  fin_cases i
  · exact (nearPoint_norm hd hD).ge
  · exact h
  · simpa [cutPoint] using h
  · simpa [cutPoint] using (nearPoint_norm hd hD).ge

private theorem cutFactor_product (d : ℝ) (z : ℂ) :
    (∏ i : Fin 4, cutFactor (cutPoint d i) z) = branch d z := by
  simp [Fin.prod_univ_succ, cutPoint, branch]
  ring

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
  obtain ⟨h₁, h₂⟩ := liftedAngle_within_strip hd hD hj i hz
  rw [sectorFactor, logStripRoot_eq_cutFactor_of_le_radius (cutPoint_norm_pos hd hD i) h₁ h₂
    (hr.trans (radius_le_cutPoint hd hD i)), liftedAngle_polar hd hD]

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
    field_simp [hr]
    ring
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
    have hInv : DifferentiableAt ℂ (fun u : ℂ => (exp u)⁻¹) z :=
      (differentiable_exp z).inv (exp_ne_zero z)
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
  rfl

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

private theorem large_quotient_norm_le {c : ℝ} (hc : 0 ≤ c) (hc₁ : c ≤ 1)
    {z B : ℂ} (hz : 2 ≤ ‖z‖) (hB : B ^ 2 = quartic c z) :
    ‖(1 - z ^ 2 - B) / (2 * z * ((c : ℂ) - z))‖ ≤ 5 := by
  let r := ‖z‖
  have hr : 2 ≤ r := hz
  have hrpos : 0 < r := by linarith
  have hr₁ : 1 ≤ r := by linarith
  have hcNorm : ‖(c : ℂ)‖ = c := by simp [abs_of_nonneg hc]
  have hr₂ : 1 ≤ r ^ 2 := one_le_pow₀ hr₁
  have hr42 : r ^ 2 ≤ r ^ 4 := by
    calc
      r ^ 2 = r ^ 2 * 1 := by ring
      _ ≤ r ^ 2 * r ^ 2 := mul_le_mul_of_nonneg_left hr₂ (sq_nonneg _)
      _ = r ^ 4 := by ring
  have hr24 : r ≤ r ^ 4 := (show r ≤ r ^ 2 by
    simpa [pow_two] using mul_le_mul_of_nonneg_left hr₁ hrpos.le).trans hr42
  have h₁ : ‖1 + z ^ 2‖ ≤ 2 * r ^ 2 := by
    calc
      ‖1 + z ^ 2‖ ≤ 1 + r ^ 2 := by simpa [r, norm_pow] using norm_add_le (1 : ℂ) (z ^ (2 : ℕ))
      _ ≤ 2 * r ^ 2 := by linarith
  have h₄ : ‖4 * (c : ℂ) * z‖ ≤ 4 * r ^ 4 := by
    calc
      _ = 4 * c * r := by simp [norm_mul, Complex.norm_real, abs_of_nonneg hc, r]
      _ ≤ 4 * 1 * r := by gcongr
      _ ≤ _ := by simpa using mul_le_mul_of_nonneg_left hr24 (by norm_num : 0 ≤ (4 : ℝ))
  have hQuartic : ‖quartic c z‖ ≤ 8 * r ^ 4 := by
    unfold quartic
    calc
      _ ≤ ‖1 + z ^ 2‖ ^ 2 + ‖4 * (c : ℂ) * z‖ := by
        simpa [norm_pow] using norm_sub_le ((1 + z ^ (2 : ℕ)) ^ (2 : ℕ)) (4 * (c : ℂ) * z)
      _ ≤ (2 * r ^ 2) ^ 2 + 4 * r ^ 4 :=
        add_le_add (pow_le_pow_left₀ (norm_nonneg _) h₁ 2) h₄
      _ = _ := by ring
  have hRoot : ‖B‖ ≤ 3 * r ^ 2 := by
    apply le_of_sq_le_sq _ (by positivity)
    rw [← norm_pow, hB]
    exact hQuartic.trans (by nlinarith [pow_nonneg hrpos.le 4])
  have hNumerator : ‖1 - z ^ 2 - B‖ ≤ 5 * r ^ 2 := by
    calc
      _ ≤ ‖1 - z ^ 2‖ + ‖B‖ := norm_sub_le _ _
      _ ≤ (1 + r ^ 2) + 3 * r ^ 2 := add_le_add
        (by simpa [r, norm_pow] using norm_sub_le (1 : ℂ) (z ^ (2 : ℕ))) hRoot
      _ ≤ _ := by linarith
  have hDistance : r / 2 ≤ ‖(c : ℂ) - z‖ := by
    have h := norm_sub_norm_le z (c : ℂ)
    rw [hcNorm, norm_sub_rev] at h
    change r - c ≤ ‖(c : ℂ) - z‖ at h
    linarith
  have hDenominator : r ^ 2 ≤ ‖2 * z * ((c : ℂ) - z)‖ := by
    calc
      r ^ 2 = (2 * r) * (r / 2) := by ring
      _ ≤ (2 * r) * ‖(c : ℂ) - z‖ := mul_le_mul_of_nonneg_left hDistance (by positivity)
      _ = _ := by simp [r, norm_mul]
  rw [norm_div]
  apply (div_le_iff₀ ((pow_pos hrpos 2).trans_le hDenominator)).mpr
  exact hNumerator.trans (mul_le_mul_of_nonneg_left hDenominator (by norm_num))

/-- The coefficient integrand decays exponentially in the logarithmic radius. -/
theorem logSector_norm_le_large {d : ℝ} (hd : 0 < d) (hD : d < 1)
    (n : ℕ) {j : ℕ} (hj : j ≤ 4) {z : ℂ}
    (hz : z.im ∈ Icc (sectorAngle d j) (sectorAngle d (j + 1)))
    (hlarge : Real.log 2 ≤ z.re) :
    ‖logSector d n j z‖ ≤ 5 * Real.exp (-(n : ℝ) * z.re) := by
  have hc := scale_pos hd
  have hc₁ : scale d ≤ 1 := by nlinarith [scale_sq_lt_one hd hD]
  have hnorm : 2 ≤ ‖exp z‖ := by
    rw [norm_exp, ← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    exact Real.exp_le_exp.mpr hlarge
  have hne : exp z ≠ (scale d : ℂ) := by
    intro heq
    rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc.le] at hnorm
    linarith
  rw [logSector_eq_quotient hd hD n hj hz hne, norm_mul, norm_pow, norm_inv]
  calc
    _ ≤ ‖exp z‖⁻¹ ^ n * 5 := mul_le_mul_of_nonneg_left
      (large_quotient_norm_le hc.le hc₁ hnorm (logBranch_sq hd hD hj hz)) (by positivity)
    _ = _ := by
      rw [norm_exp, ← Real.exp_neg, ← Real.exp_nat_mul, mul_neg, neg_mul, mul_comm]

private noncomputable def outerArcs (d : ℝ) (n : ℕ) (b : ℝ) : ℂ :=
  ∑ j ∈ Finset.range 5,
    I • (∫ y in sectorAngle d j..sectorAngle d (j + 1),
      logSector d n j ((b : ℂ) + (y : ℂ) * I))

private theorem outerArcs_norm_le {d : ℝ} (hd : 0 < d) (hD : d < 1)
    (n : ℕ) {b : ℝ} (hb : Real.log 2 ≤ b) :
    ‖outerArcs d n b‖ ≤ 50 * Real.pi * Real.exp (-(n : ℝ) * b) := by
  unfold outerArcs
  apply (norm_sum_le _ _).trans
  have hm := sectorAngle_mono hd hD
  calc
    _ ≤ ∑ _j ∈ Finset.range 5, (5 * Real.exp (-(n : ℝ) * b)) * (2 * Real.pi) := by
      apply Finset.sum_le_sum
      intro j hj
      have hj' : j ≤ 4 := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      have hOrd := (sectorAngle_step hd hD hj').le
      have hlow : 0 ≤ sectorAngle d j := hm (Nat.zero_le _)
      have hhigh : sectorAngle d (j + 1) ≤ 2 * Real.pi := hm (show j + 1 ≤ 5 by omega)
      have hWidth : |sectorAngle d (j + 1) - sectorAngle d j| ≤ 2 * Real.pi := by
        rw [abs_of_nonneg (sub_nonneg.mpr hOrd)]
        linarith
      rw [norm_smul, Complex.norm_I, one_mul]
      apply (intervalIntegral.norm_integral_le_of_norm_le_const ?_).trans
        (mul_le_mul_of_nonneg_left hWidth (by positivity))
      intro y hy
      rw [uIoc_of_le hOrd] at hy
      let z := (b : ℂ) + (y : ℂ) * I
      have hzIm : z.im = y := by simp [z, Complex.mul_im]
      have hzRe : z.re = b := by simp [z, Complex.mul_re]
      have hz : z.im ∈ Icc (sectorAngle d j) (sectorAngle d (j + 1)) :=
        hzIm.symm ▸ ⟨hy.1.le, hy.2⟩
      simpa only [hzRe] using logSector_norm_le_large hd hD n hj' hz (hzRe.symm ▸ hb)
    _ = _ := by simp; ring

private theorem outerArcs_tendsto_zero {d : ℝ} (hd : 0 < d) (hD : d < 1)
    {n : ℕ} (hn : 0 < n) : Tendsto (outerArcs d n) atTop (𝓝 0) := by
  have hExp : Tendsto (fun b : ℝ => Real.exp (-(n : ℝ) * b)) atTop (𝓝 0) := by
    simpa [Function.comp_def, neg_mul] using Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop (Nat.cast_pos.mpr hn : (0 : ℝ) < n))
  have hBound : Tendsto (fun b : ℝ => 50 * Real.pi * Real.exp (-(n : ℝ) * b)) atTop (𝓝 0) := by
    simpa using (hExp.const_mul (50 * Real.pi))
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hBound
  filter_upwards [eventually_ge_atTop (Real.log 2)] with b hb
  exact outerArcs_norm_le hd hD n hb

/-- The outward radial boundary difference in logarithmic coordinates. -/
noncomputable def logRayJump (d : ℝ) (n j : ℕ) (x : ℝ) : ℂ :=
  let z := (x : ℂ) + (sectorAngle d (j + 1) : ℂ) * I
  logSector d n (j + 1) z - logSector d n j z

private theorem logSector_continuous_on_ray {d : ℝ} (hd : 0 < d) (hD : d < 1)
    (n : ℕ) {j : ℕ} (hj : j ≤ 4) {y : ℝ}
    (hy : y ∈ Icc (sectorAngle d j) (sectorAngle d (j + 1))) :
    Continuous (fun x : ℝ => logSector d n j ((x : ℂ) + (y : ℂ) * I)) := by
  have hMap : Continuous (fun x : ℝ => (x : ℂ) + (y : ℂ) * I) := by fun_prop
  apply (logSector_continuousOn hd hD hj n).comp_continuous hMap
  intro x
  simpa [Complex.mul_im] using hy

private theorem logRayJump_continuous {d : ℝ} (hd : 0 < d) (hD : d < 1)
    (n : ℕ) {j : ℕ} (hj : j < 4) : Continuous (logRayJump d n j) := by
  exact (logSector_continuous_on_ray hd hD n (Nat.succ_le_of_lt hj)
    ⟨le_rfl, (sectorAngle_step hd hD (Nat.succ_le_of_lt hj)).le⟩).sub
    (logSector_continuous_on_ray hd hD n hj.le
      ⟨(sectorAngle_step hd hD hj.le).le, le_rfl⟩)

private theorem logRayJump_norm_le_large {d : ℝ} (hd : 0 < d) (hD : d < 1)
    (n : ℕ) {j : ℕ} (hj : j < 4) {x : ℝ} (hx : Real.log 2 ≤ x) :
    ‖logRayJump d n j x‖ ≤ 10 * Real.exp (-(n : ℝ) * x) := by
  let z := (x : ℂ) + (sectorAngle d (j + 1) : ℂ) * I
  have hIm : z.im = sectorAngle d (j + 1) := by simp [z, Complex.mul_im]
  have hRe : z.re = x := by simp [z, Complex.mul_re]
  have h₁ : z.im ∈ Icc (sectorAngle d j) (sectorAngle d (j + 1)) := hIm.symm ▸
    ⟨(sectorAngle_step hd hD hj.le).le, le_rfl⟩
  have h₂ : z.im ∈ Icc (sectorAngle d (j + 1)) (sectorAngle d (j + 1 + 1)) := hIm.symm ▸
    ⟨le_rfl, (sectorAngle_step hd hD (Nat.succ_le_of_lt hj)).le⟩
  calc
    _ ≤ ‖logSector d n (j + 1) z‖ + ‖logSector d n j z‖ := norm_sub_le _ _
    _ ≤ 5 * Real.exp (-(n : ℝ) * z.re) + 5 * Real.exp (-(n : ℝ) * z.re) :=
      add_le_add (logSector_norm_le_large hd hD n (Nat.succ_le_of_lt hj) h₂ (hRe.symm ▸ hx))
        (logSector_norm_le_large hd hD n hj.le h₁ (hRe.symm ▸ hx))
    _ = _ := by rw [hRe]; ring

/-- Each logarithmic jump is absolutely integrable to infinity for positive indices. -/
theorem logRayJump_integrable {d : ℝ} (hd : 0 < d) (hD : d < 1) {n : ℕ} (hn : 0 < n)
    {j : ℕ} (hj : j < 4) (a : ℝ) : IntegrableOn (logRayJump d n j) (Ioi a) := by
  let cutoff := max a (Real.log 2)
  have hCont := logRayJump_continuous hd hD n hj
  have hDecay : -(n : ℝ) < 0 := neg_neg_of_pos (Nat.cast_pos.mpr hn)
  have hNear : IntegrableOn (logRayJump d n j) (Icc a cutoff) :=
    hCont.continuousOn.integrableOn_Icc
  have hFar : IntegrableOn (logRayJump d n j) (Ioi cutoff) := by
    refine (Integrable.const_mul (integrableOn_exp_mul_Ioi hDecay cutoff) 10).mono'
      hCont.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem (measurableSet_Ioi (a := cutoff))] with x hx
    exact logRayJump_norm_le_large hd hD n hj
      ((le_max_right a (Real.log 2)).trans hx.le)
  apply (hNear.union hFar).mono_set
  intro x hx
  rcases le_or_gt x cutoff with h | h
  · exact Or.inl ⟨hx.le, h⟩
  · exact Or.inr h

/-- The outer arcs vanish and only the four improper logarithmic jumps remain. -/
theorem analyticGenerating_logarithmicRays {d : ℝ} (hd : 0 < d) (hD : d < 1)
    {r : NNReal} (h₀ : 0 < r) (hr : (r : ℝ) < radius d) {n : ℕ} (hn : 0 < n) :
    ((scale d ^ n * (C n).eval (1 - (scale d ^ 2)⁻¹) : ℝ) : ℂ) =
      (2 * (Real.pi : ℂ) * I)⁻¹ *
        ∑ j ∈ Finset.range 4, (∫ x in Ioi (Real.log r), logRayJump d n j x) := by
  let a := Real.log (r : ℝ)
  let coefficient : ℂ := ((scale d ^ n * (C n).eval (1 - (scale d ^ 2)⁻¹) : ℝ) : ℂ)
  let normalizer : ℂ := (2 * (Real.pi : ℂ) * I)⁻¹
  have hJumps : Tendsto (fun b : ℝ => ∑ j ∈ Finset.range 4,
      (∫ x in a..b, logRayJump d n j x)) atTop
      (𝓝 (∑ j ∈ Finset.range 4, (∫ x in Ioi a, logRayJump d n j x))) :=
    tendsto_finset_sum _ fun j hj =>
      intervalIntegral_tendsto_integral_Ioi a (logRayJump_integrable hd hD hn
        (Finset.mem_range.mp hj) a) tendsto_id
  have hTotal : Tendsto (fun b : ℝ => normalizer *
      (outerArcs d n b + ∑ j ∈ Finset.range 4, (∫ x in a..b, logRayJump d n j x))) atTop
      (𝓝 (normalizer * ∑ j ∈ Finset.range 4, (∫ x in Ioi a, logRayJump d n j x))) := by
    simpa using ((outerArcs_tendsto_zero hd hD hn).add hJumps).const_mul normalizer
  have hEventually :
      (fun b : ℝ => normalizer *
        (outerArcs d n b + ∑ j ∈ Finset.range 4, (∫ x in a..b, logRayJump d n j x))) =ᶠ[atTop]
      fun _ : ℝ => coefficient := by
    filter_upwards [eventually_ge_atTop a] with b hb
    exact (analyticGenerating_finiteDeformation hd hD h₀ hr n hb).symm
  exact tendsto_nhds_unique tendsto_const_nhds (hTotal.congr' hEventually)

private theorem sectorAngle_strict {d : ℝ} (hd : 0 < d) (hD : d < 1)
    {i j : ℕ} (hij : i < j) (hj : j ≤ 5) : sectorAngle d i < sectorAngle d j :=
  (sectorAngle_step hd hD (show i ≤ 4 by omega)).trans_le
    (sectorAngle_mono hd hD (Nat.succ_le_of_lt hij))

private theorem otherFactors_principal {d : ℝ} (hd : 0 < d) (hD : d < 1)
    (j : Fin 4) (x : ℝ) :
    otherFactors d j x =
      ∏ i ∈ Finset.univ.erase j, cutFactor (cutPoint d i) (exp (onCut d j x)) := by
  unfold otherFactors
  apply Finset.prod_congr rfl
  intro i hi
  have hne : i.val ≠ j.val := fun h => (Finset.mem_erase.mp hi).1 (Fin.ext h)
  have hIm : (onCut d j x).im = sectorAngle d (j.val + 1) := by simp [onCut, Complex.mul_im]
  have h₀ (p : Fin 4) : 0 < sectorAngle d (p.val + 1) :=
    sectorAngle_strict hd hD (Nat.zero_lt_succ _) (by omega)
  have hπ (p : Fin 4) : sectorAngle d (p.val + 1) < 2 * Real.pi := by
    exact sectorAngle_strict hd hD (show p.val + 1 < 5 by omega) le_rfl
  have hLift :
      liftedAngle d j.val i < (onCut d j x).im ∧
        (onCut d j x).im < liftedAngle d j.val i + 2 * Real.pi := by
    rw [hIm]
    unfold liftedAngle
    split_ifs with h
    · exact ⟨sectorAngle_strict hd hD (by omega) (by omega), by linarith [h₀ i, hπ j]⟩
    · refine ⟨by linarith [hπ i, h₀ j], ?_⟩
      have hLT := sectorAngle_strict hd hD (show j.val + 1 < i.val + 1 by omega) (by omega)
      linarith
  rw [sectorFactor, logStripRoot_eq_cutFactor (cutPoint_norm_pos hd hD i) hLift.1 hLift.2,
    liftedAngle_polar hd hD]

private theorem exp_onCut {d : ℝ} (hd : 0 < d) (hD : d < 1)
    (j : Fin 4) (x : ℝ) :
    exp (onCut d j x) = cutPoint d j * ((Real.exp x / ‖cutPoint d j‖ : ℝ) : ℂ) := by
  have hR : (‖cutPoint d j‖ : ℂ) ≠ 0 := by exact_mod_cast (cutPoint_norm_pos hd hD j).ne'
  let e := exp ((sectorAngle d (j.val + 1) : ℂ) * I)
  calc
    exp (onCut d j x) = (Real.exp x : ℂ) * e := by simp [onCut, e, exp_add, ofReal_exp]
    _ = ((‖cutPoint d j‖ : ℂ) * e) * ((Real.exp x / ‖cutPoint d j‖ : ℝ) : ℂ) := by
      push_cast
      field_simp [hR] <;> ring
    _ = _ := by rw [show (‖cutPoint d j‖ : ℂ) * e = cutPoint d j from cutPoint_polar hd hD j]

/-- The analytic factor of a ray jump with its singular square root omitted. -/
noncomputable def rayPrefactor (d : ℝ) (j : Fin 4) (z : ℂ) : ℂ :=
  -(∏ i ∈ Finset.univ.erase j, cutFactor (cutPoint d i) z) /
    (2 * z * ((scale d : ℂ) - z))

/-- The normalized radial integrand in the coefficient identity. -/
noncomputable def rayIntegrand (d : ℝ) (n : ℕ) (j : Fin 4) (s : ℝ) : ℂ :=
  (Real.sqrt s : ℂ) * (1 + (s : ℂ))⁻¹ ^ (n + 1) *
    rayPrefactor d j (cutPoint d j * (1 + (s : ℂ)))

private theorem real_exp_log_cut {d : ℝ} (hd : 0 < d) (hD : d < 1)
    (j : Fin 4) {s : ℝ} (hs : 0 ≤ s) :
    Real.exp (Real.log (‖cutPoint d j‖ * (1 + s))) / ‖cutPoint d j‖ = 1 + s := by
  have hR := cutPoint_norm_pos hd hD j
  rw [Real.exp_log (mul_pos hR (by linarith))]
  exact mul_div_cancel_left₀ _ hR.ne'

/-- The logarithmic jump including the Jacobian equals the normalized radial integrand. -/
theorem logRayJump_eq_normalized {d : ℝ} (hd : 0 < d) (hD : d < 1)
    (n : ℕ) (j : Fin 4) {s : ℝ} (hs : 0 ≤ s) :
    (1 + s)⁻¹ • logRayJump d n j.val (Real.log (‖cutPoint d j‖ * (1 + s))) =
      (-2 * I) * (cutPoint d j)⁻¹ ^ n * rayIntegrand d n j s := by
  let x := Real.log (‖cutPoint d j‖ * (1 + s))
  have hScale : Real.exp x / ‖cutPoint d j‖ = 1 + s := real_exp_log_cut hd hD j hs
  have hOut : 1 ≤ Real.exp x / ‖cutPoint d j‖ := by rw [hScale]; linarith
  have hJump := logSector_jump_sqrt hd hD n j x hOut
  change (1 + s)⁻¹ •
    (logSector d n (j.val + 1) (onCut d j x) - logSector d n j.val (onCut d j x)) = _
  rw [hJump, otherFactors_principal hd hD, exp_onCut hd hD, hScale]
  rw [show 1 + s - 1 = s by ring]
  simp only [rayIntegrand, rayPrefactor, Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_add,
    Complex.ofReal_one, mul_inv_rev, mul_pow, pow_succ]
  ring

private theorem logRayJump_vanishes_inward {d : ℝ} (hd : 0 < d) (hD : d < 1)
    (n : ℕ) (j : Fin 4) {x : ℝ} (hx : x ≤ Real.log ‖cutPoint d j‖) :
    logRayJump d n j.val x = 0 := by
  have hR := cutPoint_norm_pos hd hD j
  have hIn : Real.exp x / ‖cutPoint d j‖ ≤ 1 :=
    (div_le_one hR).mpr (by simpa only [Real.exp_log hR] using Real.exp_le_exp.mpr hx)
  exact logSector_jump_zero hd hD n j x hIn

private theorem logRayJump_integral_cutoff {d : ℝ} (hd : 0 < d) (hD : d < 1)
    {n : ℕ} (hn : 0 < n) (j : Fin 4) {a : ℝ} (ha : a ≤ Real.log ‖cutPoint d j‖) :
    (∫ x in Ioi a, logRayJump d n j.val x) =
      ∫ x in Ioi (Real.log ‖cutPoint d j‖), logRayJump d n j.val x := by
  let b := Real.log ‖cutPoint d j‖
  have hUnion : Ioi a = Ioc a b ∪ Ioi b := by
    ext x
    constructor
    · intro hx
      rcases le_or_gt x b with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr h
    · rintro (hx | hx)
      · exact hx.1
      · exact ha.trans_lt hx
  have hDisjoint : Disjoint (Ioc a b) (Ioi b) :=
    Set.disjoint_left.mpr fun x hx hy => (not_lt_of_ge hx.2) hy
  have hInward : ∫ x in Ioc a b, logRayJump d n j.val x = 0 := by
    rw [setIntegral_congr_fun measurableSet_Ioc
      (g := fun _ => (0 : ℂ)) (fun _ hx => logRayJump_vanishes_inward hd hD n j hx.2)]
    simp
  have hInt : IntegrableOn (logRayJump d n j.val) (Ioi a) := logRayJump_integrable hd hD hn j.isLt a
  have hNear : IntegrableOn (logRayJump d n j.val) (Ioc a b) := hInt.mono_set fun _ hx => hx.1
  have hFar : IntegrableOn (logRayJump d n j.val) (Ioi b) := logRayJump_integrable hd hD hn j.isLt b
  rw [hUnion, setIntegral_union hDisjoint measurableSet_Ioi hNear hFar, hInward, zero_add]

private theorem normalizedRay_integral_data {d : ℝ} (hd : 0 < d) (hD : d < 1)
    {n : ℕ} (hn : 0 < n) (j : Fin 4) :
    IntegrableOn (rayIntegrand d n j) (Ioi 0) ∧
      (∫ x in Ioi (Real.log ‖cutPoint d j‖), logRayJump d n j.val x) =
        (-2 * I) * (cutPoint d j)⁻¹ ^ n * ∫ s in Ioi 0, rayIntegrand d n j s := by
  let R := ‖cutPoint d j‖
  let scaleFactor := (-2 * I) * (cutPoint d j)⁻¹ ^ n
  have hR : 0 < R := cutPoint_norm_pos hd hD j
  have hz : cutPoint d j ≠ 0 := norm_pos_iff.mp hR
  have hScale : scaleFactor ≠ 0 := mul_ne_zero
    (mul_ne_zero (by norm_num) I_ne_zero) (pow_ne_zero _ (inv_ne_zero hz))
  let f : ℝ → ℂ := fun s => (1 + s)⁻¹ • logRayJump d n j.val (Real.log (R * (1 + s)))
  have hSub : IntegrableOn f (Ioi 0) ∧
      (∫ x in Ioi (Real.log R), logRayJump d n j.val x) = ∫ s in Ioi 0, f s :=
    OpenMathResearch.LogarithmicContour.integral_logRadius_improper hR
      (logRayJump_continuous hd hD n j.isLt) (logRayJump_integrable hd hD hn j.isLt (Real.log R))
  have hEq : EqOn f (fun s => scaleFactor * rayIntegrand d n j s) (Ioi 0) :=
    fun s hs => logRayJump_eq_normalized hd hD n j (le_of_lt hs)
  refine ⟨?_, ?_⟩
  · apply (Integrable.const_mul hSub.1 scaleFactor⁻¹).congr_fun _ measurableSet_Ioi
    intro s hs
    rw [hEq hs, ← mul_assoc, inv_mul_cancel₀ hScale, one_mul]
  · rw [hSub.2, setIntegral_congr_fun measurableSet_Ioi hEq, MeasureTheory.integral_const_mul]

/-- Each normalized ray integrand is absolutely integrable. -/
theorem rayIntegrand_integrable {d : ℝ} (hd : 0 < d) (hD : d < 1)
    {n : ℕ} (hn : 0 < n) (j : Fin 4) : IntegrableOn (rayIntegrand d n j) (Ioi 0) :=
  (normalizedRay_integral_data hd hD hn j).1

/-- The exact Catalan coefficient as the sum of the four improper ray integrals. -/
theorem analyticGenerating_fourRays {d : ℝ} (hd : 0 < d) (hD : d < 1)
    {r : NNReal} (h₀ : 0 < r) (hr : (r : ℝ) < radius d) {n : ℕ} (hn : 0 < n) :
    ((scale d ^ n * (C n).eval (1 - (scale d ^ 2)⁻¹) : ℝ) : ℂ) =
      ∑ j : Fin 4, (-(cutPoint d j)⁻¹ ^ n / (Real.pi : ℂ)) *
        ∫ s in Ioi 0, rayIntegrand d n j s := by
  have h₀R : 0 < (r : ℝ) := by exact_mod_cast h₀
  rw [analyticGenerating_logarithmicRays hd hD h₀ hr hn, ← Fin.sum_univ_eq_sum_range,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hRadius : Real.log (r : ℝ) ≤ Real.log ‖cutPoint d j‖ :=
    Real.log_le_log h₀R (hr.le.trans (radius_le_cutPoint hd hD j))
  rw [logRayJump_integral_cutoff hd hD hn j hRadius, (normalizedRay_integral_data hd hD hn j).2]
  have hπI : (2 * (Real.pi : ℂ) * I)⁻¹ * (-2 * I) = -(Real.pi : ℂ)⁻¹ := by
    field_simp [I_ne_zero, Complex.ofReal_ne_zero.mpr Real.pi_ne_zero] <;> ring
  calc
    _ = ((2 * (Real.pi : ℂ) * I)⁻¹ * (-2 * I)) * ((cutPoint d j)⁻¹ ^ n *
        ∫ s in Ioi 0, rayIntegrand d n j s) := by ring
    _ = _ := by rw [hπI]; ring

end CatalanStrictPeaks.CutGeometry
