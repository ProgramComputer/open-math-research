import FourierLogisticPoles
import FourierResolventDerivative
import RepositoryCoherentPoles
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Complex Real Set

abbrev fourierRowPole (s : ℝ) (l : ℤ) : ℂ := (s:ℂ)+(2*(l:ℂ)+1)*π*I

private theorem fourierRowPole_im (s : ℝ) (l : ℤ) :
    (fourierRowPole s l).im=(2*(l:ℝ)+1)*π := by
  simp [fourierRowPole,Complex.add_im,Complex.mul_re,Complex.add_re]

private theorem signed_odd_im_ne_zero (l : ℤ) : (2*(l:ℝ)+1)*π ≠ 0 := by
  apply mul_ne_zero _ Real.pi_ne_zero
  exact_mod_cast (show (2*l+1:ℤ)≠0 by omega)

theorem real_not_fourierRowPole (s x : ℝ) : (x:ℂ) ∉ range (fourierRowPole s) := by
  rintro ⟨l,hl⟩
  have h := congrArg Complex.im hl
  rw [fourierRowPole_im,Complex.ofReal_im] at h
  exact signed_odd_im_ne_zero l h

theorem fourierRowPole_compl_open (s : ℝ) : IsOpen (range (fourierRowPole s))ᶜ := by
  have he : (range (fourierRowPole s))ᶜ = {w : ℂ | 1+Complex.exp (w-s)≠0} := by
    ext w
    exact not_congr (logistic_denominator_zero_iff s w).symm
  rw [he]
  exact isOpen_ne_fun (continuous_const.add (Complex.continuous_exp.comp (continuous_id.sub continuous_const))) continuous_const

private theorem rowPole_nonzero (s : ℝ) (l : ℤ) : fourierRowPole s l ≠ 0 :=
  fun he => signed_odd_im_ne_zero l (by rw [← fourierRowPole_im s l,he]; rfl)

theorem rowPole_summable (s : ℝ) (j : ℕ) :
    Summable (fun i => 1 / ‖fourierRowPole s i‖ ^ (j + 2)) := by
  have h := (RepositoryQuotientAudit.summable_coherentPole_pow s (p := j + 2) (by omega)).norm
  simpa only [norm_div, norm_one, norm_pow, RepositoryQuotientAudit.coherentPole, fourierRowPole] using h

/-- A real-axis inverse-square formula supplies the global identity on every
component of every comparison circle avoiding the odd poles. -/
theorem rowPole_inverseSquare_of_real (s : ℝ)
    (hreal : ∀ x : ℝ, x < s → inverseSquarePoleSum (fourierRowPole s) (x:ℂ) =
      -Complex.exp ((x:ℂ)-s)/(1+Complex.exp ((x:ℂ)-s))^2)
    {w : ℂ} (hw : w ∉ range (fourierRowPole s)) :
    inverseSquarePoleSum (fourierRowPole s) w =
      -Complex.exp (w-s)/(1+Complex.exp (w-s))^2 := by
  have ha := inverseSquarePoleSum_analytic (fourierRowPole s) (rowPole_nonzero s)
    (rowPole_summable s 0) (fourierRowPole_compl_open s) (fun i hp => hp ⟨i,rfl⟩)
  exact analytic_eq_off_poles_of_real_ray (countable_range _) (real_not_fourierRowPole s s)
    ha (negative_logistic_slope_analytic s) hreal hw

/-- The anchored resolvent vanishes at zero. Its derivative determines it
everywhere away from the signed odd lattice because that complement is connected. -/
theorem rowPole_anchored_of_real (s : ℝ)
    (hreal : ∀ x : ℝ, x < s → inverseSquarePoleSum (fourierRowPole s) (x:ℂ) =
      -Complex.exp ((x:ℂ)-s)/(1+Complex.exp ((x:ℂ)-s))^2)
    {w : ℂ} (hw : w ∉ range (fourierRowPole s)) :
    anchoredPoleSum (fourierRowPole s) w =
      Complex.exp (-(s:ℂ))/(1+Complex.exp (-(s:ℂ))) -
      Complex.exp (w-s)/(1+Complex.exp (w-s)) := by
  let U := (range (fourierRowPole s))ᶜ
  let H := fun w : ℂ => Complex.exp (w-s)/(1+Complex.exp (w-s))
  have hU : IsOpen U := fourierRowPole_compl_open s
  have hdim : 1 < Module.rank ℝ ℂ := by rw [Complex.rank_real_complex]; norm_num
  have hconn : IsPreconnected U :=
    ((countable_range (fourierRowPole s)).isConnected_compl_of_one_lt_rank hdim).isPreconnected
  have hp (v : ℂ) (hv : v ∈ U) := anchoredPoleSum_hasDerivAt (fourierRowPole s)
    (rowPole_nonzero s) (rowPole_summable s 0) hU (fun i h => h ⟨i,rfl⟩) hv
  have hH (v : ℂ) (hv : v ∈ U) : HasDerivAt (fun z => H 0-H z)
      (-Complex.exp (v-s)/(1+Complex.exp (v-s))^2) v := by
    have he : HasDerivAt (fun z : ℂ => Complex.exp (z-s)) (Complex.exp (v-s)) v := by
      simpa using ((hasDerivAt_id v).sub_const (s:ℂ)).cexp
    have hn : 1+Complex.exp (v-s) ≠ 0 := fun h => hv ((logistic_denominator_zero_iff s v).mp h)
    apply ((hasDerivAt_const v (H 0)).sub (he.div ((hasDerivAt_const v (1:ℂ)).add he) hn)).congr_deriv
    dsimp only [Pi.add_apply]
    ring
  have hz : (0:ℂ) ∈ U := by
    change (0:ℂ) ∉ range (fourierRowPole s)
    simpa only [Complex.ofReal_zero] using real_not_fourierRowPole s 0
  have heq := hU.eqOn_of_deriv_eq hconn
    (fun v hv => (hp v hv).differentiableAt.differentiableWithinAt)
    (fun v hv => (hH v hv).differentiableAt.differentiableWithinAt)
    (fun v hv => (hp v hv).deriv.trans ((rowPole_inverseSquare_of_real s hreal hv).trans (hH v hv).deriv.symm))
    hz (by simp [anchoredPoleSum])
  simpa [H] using heq hw

#print axioms rowPole_summable
#print axioms rowPole_inverseSquare_of_real
#print axioms rowPole_anchored_of_real
end OpenMathResearch.LongCycleExcedances
