import NestedPoleLattice
import RepositoryUniformMass
import AllAngleMinorPoles

noncomputable section
namespace RepositoryQuotientAudit
open Finset LongCycles OpenMathResearch.LongCycleExcedances
open scoped Real

/-- The exact original row is approximated by the full numerator values at
the poles inside the fixed inner radius. The only lattice input is the
summability of the squared pole ratios. -/
theorem original_nested_row_error {n k : ℕ} (hn : 0 < n) (hk : 7 ≤ k)
    {x : ℝ} (hx : 0 ≤ x)
    (hSquare : Summable fun l : ℤ => (‖coherentPole x 0‖/‖coherentPole x l‖)^2) :
    let r := ‖coherentPole x 0‖
    let R₁ := r*(1+1/(100*(k:ℝ)))
    let R₀ := r*(1+3/(200*(k:ℝ)))
    let Rstar := r*(1+1/(50*(k:ℝ)))
    let A := Real.exp (6+9*Real.log k)
    let t := -Real.exp (-x)
    let T := coherentTilt k t
    let a (l : ℤ) := if ‖coherentPole x l‖ ≤ R₀ then
      ((r:ℂ)/coherentPole x l)^(n+1) * seriesValue T (coherentPole x l) else 0
    Summable a ∧
    |r^(n+1)/2 * ((enumerator n k).eval t/((1-t)^(n+1)*n.factorial)) -
      (∑' l, a l).re/2| ≤
        ((200*(k:ℝ)+3)*(A*(r/R₁)^(n-1))*(∑' l : ℤ, (r/‖coherentPole x l‖)^2) +
          r*A*(r/Rstar)^n)/2 := by
  dsimp only
  let r := ‖coherentPole x 0‖
  let R₁ := r*(1+1/(100*(k:ℝ)))
  let R₀ := r*(1+3/(200*(k:ℝ)))
  let Rstar := r*(1+1/(50*(k:ℝ)))
  let A := Real.exp (6+9*Real.log k)
  let t := -Real.exp (-x)
  let T := coherentTilt k t
  let c (j : ℕ) := ((PowerSeries.coeff j T : ℝ) : ℂ)
  let f (l : ℤ) := normalizedPolePrefix c n r (coherentPole x l)
  let a (l : ℤ) := normalizedPoleApprox c n r R₀ (coherentPole x l)
  let F := (enumerator n k).eval t/((1-t)^(n+1)*n.factorial)
  have hr : 0 < r := coherentPole_near_pos x
  have hA : 0 < A := Real.exp_pos _
  have hT (j : ℕ) : ‖c j‖ ≤ A/Rstar^j := by
    dsimp only [c]
    rw [Complex.norm_real,Real.norm_eq_abs]
    exact (original_uniform_tilt_envelope hk hx).1 j
  obtain ⟨h₁,h₀,hstar,hbudget⟩ := fixed_nested_radius_budget hr (by omega : 0 < k)
  have hPrefix : Summable f := by
    unfold f normalizedPolePrefix
    apply Summable.mul_left
    apply summable_sum
    intro j hj
    exact (summable_coherentPole_pow x (by have := mem_range.mp hj; omega :
      2 ≤ n-j+1)).mul_left _
  have hSquare' : Summable fun l : ℤ => (r/‖coherentPole x l‖)^2 := hSquare
  obtain ⟨hApprox,hError⟩ := nested_pole_lattice_error (coherentPole x) c hn hA.le hr h₁ h₀ hstar
    (coherentPole_near_le x) hT hSquare' hPrefix
  rw [hbudget] at hError
  have hAdef (l : ℤ) : a l = if ‖coherentPole x l‖ ≤ R₀ then
      ((r:ℂ)/coherentPole x l)^(n+1)*seriesValue T (coherentPole x l) else 0 := rfl
  have hRow := (original_coherent_row_pair n k (by omega : 2 ≤ k) x hx).1
  change (F:ℂ) = ((PowerSeries.coeff n T/(1+Real.exp (-x)):ℝ):ℂ) +
    ∑' l : ℤ, ∑ j ∈ range n, c j*(1/coherentPole x l^(n-j+1)) at hRow
  have hNormalized :
      (r:ℂ)^(n+1)*(F:ℂ) = (r:ℂ)^(n+1)*
      ((PowerSeries.coeff n T/(1+Real.exp (-x)):ℝ):ℂ) + ∑' l : ℤ, f l := by
    rw [hRow,mul_add,←tsum_mul_left]
    rfl
  have hReal := congrArg Complex.re hNormalized
  simp only [Complex.add_re, ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re] at hReal
  have hRealError := (Complex.abs_re_le_norm ((∑' l, f l)-(∑' l, a l))).trans hError
  rw [Complex.sub_re] at hRealError
  have hZ : |r^(n+1)*(PowerSeries.coeff n T/(1+Real.exp (-x)))| ≤ r*A*(r/Rstar)^n := by
    have hden : 1 ≤ 1+Real.exp (-x) := by linarith [Real.exp_pos (-x)]
    have hbound : |PowerSeries.coeff n T| ≤ A/Rstar^n := by
      simpa only [c,Complex.norm_real,Real.norm_eq_abs] using hT n
    rw [abs_mul,abs_of_pos (pow_pos hr _),abs_div,abs_of_pos (by positivity : 0 < 1+Real.exp (-x))]
    calc
      _ ≤ r^(n+1)*|PowerSeries.coeff n T| := by
        exact mul_le_mul_of_nonneg_left (div_le_self (abs_nonneg _) hden) (by positivity)
      _ ≤ r^(n+1)*(A/Rstar^n) := mul_le_mul_of_nonneg_left hbound (by positivity)
      _ = _ := by rw [pow_succ r,div_pow]; ring
  constructor
  · change Summable a
    exact hApprox
  · change |r^(n+1)/2 * F -
      (∑' l : ℤ, if ‖coherentPole x l‖ ≤ R₀ then
       ((r:ℂ)/coherentPole x l)^(n+1)*seriesValue T (coherentPole x l) else 0).re/2| ≤ _
    simp_rw [←hAdef]
    rw [show r^(n+1)/2*F = r^(n+1)*F/2 by ring,hReal,←sub_div,abs_div,
      abs_of_pos (by norm_num : (0:ℝ)<2),add_sub_assoc]
    simpa only [add_comm] using div_le_div_of_nonneg_right
      ((abs_add_le _ _).trans (add_le_add hZ hRealError)) (by norm_num : (0:ℝ) ≤ 2)

/-- Actual middle-angle row error with the signed-lattice square mass
replaced by its explicit size bound. -/
theorem original_middle_nested_row_error {n k : ℕ} (hk : 7 ≤ k)
    {x : ℝ} (hx : 0 ≤ x)
    (hm : 1 ≤ (n:ℝ)*(π/‖coherentPole x 0‖)^2) :
    let r := ‖coherentPole x 0‖
    let R₁ := r*(1+1/(100*(k:ℝ)))
    let R₀ := r*(1+3/(200*(k:ℝ)))
    let Rstar := r*(1+1/(50*(k:ℝ)))
    let A := Real.exp (6+9*Real.log k)
    let t := -Real.exp (-x)
    let T := coherentTilt k t
    let a (l : ℤ) := if ‖coherentPole x l‖ ≤ R₀ then
      ((r:ℂ)/coherentPole x l)^(n+1) * seriesValue T (coherentPole x l) else 0
    Summable a ∧
    |r^(n+1)/2 * ((enumerator n k).eval t/((1-t)^(n+1)*n.factorial)) -
      (∑' l, a l).re/2| ≤
        ((200*(k:ℝ)+3)*(A*(r/R₁)^(n-1))*(2+(n:ℝ)/2) +
          r*A*(r/Rstar)^n)/2 := by
  have hn : 0 < n := by
    by_contra! hn
    have he : n = 0 := by omega
    norm_num [he] at hm
  obtain ⟨hs,hb⟩ := middle_coherent_square_sum x hm
  obtain ⟨ha,he⟩ := original_nested_row_error hn hk hx hs
  refine ⟨ha,he.trans ?_⟩
  have hr : 0 < ‖coherentPole x 0‖ := coherentPole_near_pos x
  apply div_le_div_of_nonneg_right _ (by norm_num)
  exact add_le_add (mul_le_mul_of_nonneg_left hb (by positivity)) le_rfl

#print axioms original_nested_row_error
#print axioms original_middle_nested_row_error
end RepositoryQuotientAudit
