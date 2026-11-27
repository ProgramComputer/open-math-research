import WidePoleChord
import WideOddRadius
import WideGeometry
import RepositoryLogTiltDiscrete
import TiltAnalyticEvaluation

set_option autoImplicit false
noncomputable section
namespace RepositoryQuotientAudit
open OpenMathResearch.LongCycleExcedances Finset Real Set

/-- The logarithm of the original finite tilt at a complex contour point. -/
def wideLogNumerator (k : ℕ) (x : ℝ) (w : ℂ) : ℂ :=
  logPolyAt (k-1) (fun d => (cutoffLogCoefficient k (-Real.exp (-x)) d : ℂ)) w

private theorem odd_pole_norm_square (x : ℝ) (j : ℤ) :
    ‖coherentPole x j‖^2 = x^2 + ((2*(j:ℝ)+1)*π)^2 := by
  rw [Complex.sq_norm,Complex.normSq_apply]
  simp [coherentPole,Complex.add_re,Complex.add_im,Complex.mul_I_re,Complex.mul_I_im,Complex.mul_re,Complex.mul_im]
  ring

private theorem verticalArgument_odd_pole (x : ℝ) (j : ℤ) :
    verticalArgument x ((2*(j:ℝ)+1)*π) = coherentPole x j := by
  unfold verticalArgument coherentPole
  push_cast
  rfl


/-- Difference of the literal finite log numerator at two enclosed odd poles. -/
theorem actual_wide_logTilt_chord {k : ℕ} (hk : 100 ≤ k) {x R : ℝ}
    (hx : 125/2 ≤ x) (hpower : R^(k-1) ≤ x^(k-1)*(31/10))
    {l u : ℤ} (hlu : l < u)
    (hl : ‖coherentPole x l‖ ≤ R) (hu : ‖coherentPole x u‖ ≤ R) :
    ‖wideLogNumerator k x (coherentPole x u)-wideLogNumerator k x (coherentPole x l)‖ <
      (28/25)*((u:ℝ)-(l:ℝ)) := by
  have hx₀ : 0 < x := by linarith
  let L : ℝ := (2*(l:ℝ)+1)*π
  let U : ℝ := (2*(u:ℝ)+1)*π
  have hlU : L < U := by
    have hh : (l:ℝ) < (u:ℝ) := by exact_mod_cast hlu
    dsimp only [L,U]
    exact mul_lt_mul_of_pos_right (by linarith) pi_pos
  have hL : verticalArgument x L = coherentPole x l := verticalArgument_odd_pole x l
  have hU : verticalArgument x U = coherentPole x u := verticalArgument_odd_pole x u
  let t : ℂ := ((-Real.exp (-x):ℝ):ℂ)
  let g (d : ℕ) : ℂ := (cutoffLogCoefficient k (-Real.exp (-x)) d : ℂ)
  have hc (j : ℕ) (hj : j ∈ range (k-1)) :
      HasSum (fun i : ℕ => t^(i+1)*((i+1:ℕ):ℂ)^j)
        (-g (j+1)*((j+1).factorial:ℂ)) := by
    have hjk : j+1 < k := by have := mem_range.mp hj; omega
    have hm := cutoffLogCoefficient_hasSum (d := j+1) (Nat.succ_pos j) hjk hx₀
    rw [show j+1-1 = j by omega] at hm
    exact hm
  have hb := wide_log_chord_bound hk hx hlU
    (fun v hv => (pow_le_pow_left₀ (norm_nonneg _)
      (segment_in_radius (hL.symm ▸ hl) (hU.symm ▸ hu) v hv) _).trans hpower)
    t (hL.symm ▸ coherentPole_exp_neg x l) (hU.symm ▸ coherentPole_exp_neg x u) g hc
  rw [hL,hU] at hb
  have hs : (14/25:ℝ)*(U-L) = π*((28/25)*((u:ℝ)-(l:ℝ))) := by
    dsimp only [L,U]
    ring
  rw [hs] at hb
  by_contra! h
  exact (not_lt_of_ge (mul_le_mul_of_nonneg_left h pi_pos.le)) hb

/-- For each enclosed positive nonprincipal pole, the normalized Fourier
residue is bounded by the principal-to-pole chord and radial decay. -/
theorem actual_wide_enclosed_ratio
    {n k : ℕ} (hk : 100 ≤ k) {x R : ℝ} (hx : 0 < x) (hR : 0 ≤ R)
    (hcap : R^2 ≤ ‖coherentPole x 0‖^2*(1+2/(k:ℝ)))
    (hmid : 1 ≤ (n:ℝ)*(π/‖coherentPole x 0‖)^2)
    {j : ℕ} (hj : 1 ≤ j) (henc : ‖coherentPole x (j:ℤ)‖ ≤ R) :
    let p : ℝ := 2*j+1
    let L := wideLogNumerator k x
    (‖coherentPole x 0‖/‖coherentPole x (j:ℤ)‖)^n *
      ‖Complex.exp (L (coherentPole x (j:ℤ))) /
        Complex.exp (L (coherentPole x 0))‖ ≤
          exp (-(49/100)*(p^2-1)+(14/25)*(p-1)) := by
  intro p L
  let r := ‖coherentPole x 0‖
  let W := ‖coherentPole x (j:ℤ)‖
  have hp : 3 ≤ p := by
    have : (1:ℝ) ≤ j := by exact_mod_cast hj
    dsimp [p]
    linarith
  have hsqW : W^2 = x^2+(p*π)^2 := by
    rw [odd_pole_norm_square,Int.cast_natCast]
  have hsqR : r^2 = x^2+π^2 := by simp [r,odd_pole_norm_square]
  have hbelow : x^2+9*π^2 ≤ W^2 := by
    rw [hsqW,mul_pow]
    have hm := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 3) hp 2
    nlinarith only [mul_le_mul_of_nonneg_right hm (sq_nonneg π)]
  have hWr := pow_le_pow_left₀ (norm_nonneg _) henc 2
  obtain ⟨hheight,hpower⟩ := wide_residue_height_power hk hx hsqR hR (hbelow.trans hWr) hcap
  have hr : 0 < r := by
    have h := norm_nonneg (coherentPole x 0)
    dsimp only [r] at hsqR ⊢
    nlinarith [sq_pos_of_pos hx, sq_nonneg π]
  have hrW : r ≤ W := by
    apply le_of_sq_le_sq _ (norm_nonneg _)
    rw [hsqR]
    linarith only [hbelow,sq_nonneg π]
  have hW : 0 < W := hr.trans_le hrW
  have hZ : (W/r)^2 = 1+(p^2-1)*(π/r)^2 := by
    rw [div_pow, hsqW, div_pow]
    field_simp [hr.ne']
    rw [hsqR]
    ring
  have hlim : (W/r)^2 ≤ 51/50 := by
    rw [div_pow, div_le_iff₀ (sq_pos_of_pos hr)]
    have hk' : (100:ℝ) ≤ k := by exact_mod_cast hk
    have hc : 2/(k:ℝ) ≤ 1/50 := by
      rw [div_le_iff₀ (by linarith : (0:ℝ) < k)]
      linarith
    have he : 1+2/(k:ℝ) ≤ 51/50 := by linarith only [hc]
    change R^2 ≤ r^2*(1+2/(k:ℝ)) at hcap
    exact hWr.trans (hcap.trans (by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left he (sq_nonneg r)))
  have hrad := wide_enclosed_radius_decay hr hW (show 1 ≤ p by linarith) hZ hlim hmid
  have hj' : (0:ℤ) < (j:ℤ) := by omega
  have hc := actual_wide_logTilt_chord hk hheight hpower hj' (hrW.trans henc) henc
  have hi : (28/25:ℝ)*(((j:ℤ):ℝ)-(0:ℤ)) = (14/25)*(p-1) := by
    dsimp [p]
    push_cast
    ring
  rw [hi] at hc
  have htilt : ‖Complex.exp (L (coherentPole x (j:ℤ))) /
      Complex.exp (L (coherentPole x 0))‖ ≤ exp ((14/25)*(p-1)) := by
    rw [←Complex.exp_sub, Complex.norm_exp]
    exact exp_le_exp.mpr ((le_abs_self _).trans
      ((Complex.abs_re_le_norm _).trans hc.le))
  rw [exp_add]
  exact mul_le_mul hrad htilt (norm_nonneg _) (exp_pos _).le

/-- Weighted and unweighted budgets for the positive half of the enclosed
nonprincipal residues. Paired conjugate residues have the same ratio. -/
theorem actual_wide_enclosed_budgets
    {n k : ℕ} (hk : 100 ≤ k) {x R : ℝ} (hx : 0 < x) (hR : 0 ≤ R)
    (hcap : R^2 ≤ ‖coherentPole x 0‖^2*(1+2/(k:ℝ)))
    (hmid : 1 ≤ (n:ℝ)*(π/‖coherentPole x 0‖)^2)
    (s : Finset ℕ) (henc : ∀ i ∈ s, ‖coherentPole x ((i+1:ℕ):ℤ)‖ ≤ R) :
    let L := wideLogNumerator k x
    let f (i : ℕ) := (‖coherentPole x 0‖/‖coherentPole x ((i+1:ℕ):ℤ)‖)^n *
      ‖Complex.exp (L (coherentPole x ((i+1:ℕ):ℤ))) /
        Complex.exp (L (coherentPole x 0))‖
    (∑ i ∈ s, (2*(i+1:ℕ)+1:ℝ)*f i) ≤ 1/4 ∧ (∑ i ∈ s, f i) ≤ 1/12 := by
  intro L f
  have hw : (∑ i ∈ s, (2*(i+1:ℕ)+1:ℝ)*f i) ≤ 1/4 := by
    apply wide_weighted_minor_poles_le_quarter
    intro i hi
    have hp : 0 ≤ (2*(i+1:ℕ)+1:ℝ) := by positivity
    exact mul_le_mul_of_nonneg_left
      (actual_wide_enclosed_ratio hk hx hR hcap hmid (Nat.succ_pos i) (henc i hi)) hp
  refine ⟨hw, ?_⟩
  have h : (∑ i ∈ s, 3*f i) ≤ ∑ i ∈ s, (2*(i+1:ℕ)+1:ℝ)*f i := by
    apply sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_right _ (by unfold f; positivity)
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) i]
  rw [←mul_sum] at h
  linarith only [h,hw]

/-- Literal original tilt in the normalized Fourier residues. -/
theorem original_fourier_enclosed_budgets
    {n k : ℕ} (hk : 100 ≤ k) {x R : ℝ} (hx : 0 < x) (hR : 0 ≤ R)
    (hcap : R^2 ≤ ‖coherentPole x 0‖^2*(1+2/(k:ℝ)))
    (hmid : 1 ≤ (n:ℝ)*(π/‖coherentPole x 0‖)^2)
    (s : Finset ℕ) (henc : ∀ i ∈ s, ‖coherentPole x ((i+1:ℕ):ℤ)‖ ≤ R) :
    let T := coherentTilt k (-exp (-x))
    let f (i : ℕ) := (‖coherentPole x 0‖/‖coherentPole x ((i+1:ℕ):ℤ)‖)^n *
      ‖seriesValue T (coherentPole x ((i+1:ℕ):ℤ))/seriesValue T (coherentPole x 0)‖
    (∑ i ∈ s, (2*(i+1:ℕ)+1:ℝ)*f i) ≤ 1/4 ∧ (∑ i ∈ s, f i) ≤ 1/12 := by
  intro T f
  have he (w : ℂ) : seriesValue T w = Complex.exp (wideLogNumerator k x w) :=
    seriesValue_original_coherentTilt (by omega) _ _
  simp only [f, he]
  exact actual_wide_enclosed_budgets hk hx hR hcap hmid s henc

#print axioms original_fourier_enclosed_budgets
#print axioms actual_wide_logTilt_chord
#print axioms actual_wide_enclosed_ratio
#print axioms actual_wide_enclosed_budgets
end RepositoryQuotientAudit
