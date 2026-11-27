import SmallResidueChord
import SmallResidueGeometry
import SmallResidueRadius
import SmallResidueMass
import RepositoryWideResidues

set_option autoImplicit false
noncomputable section
namespace RepositoryQuotientAudit
open OpenMathResearch.LongCycleExcedances Finset Real Set

open private verticalArgument_odd_pole odd_pole_norm_square from RepositoryWideResidues
/-- Difference of the literal finite log numerator at two enclosed odd poles. -/
theorem small_logTilt_chord {k : ℕ} {x R D : ℝ}
    (hx₀ : 0 < x) (hbnd : π*(31/10)*(∑' i : ℕ, poissonTerm (k-1) (x*(i+1:ℕ))) < D)
    (hpower : R^(k-1) ≤ x^(k-1)*(31/10))
    {l u : ℤ} (hlu : l < u)
    (hl : ‖coherentPole x l‖ ≤ R) (hu : ‖coherentPole x u‖ ≤ R) :
    ‖wideLogNumerator k x (coherentPole x u)-wideLogNumerator k x (coherentPole x l)‖ <
      (2*D)*((u:ℝ)-(l:ℝ)) := by
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
  have hb := small_log_chord_bound hx₀ hbnd hlU
    (fun v hv => (pow_le_pow_left₀ (norm_nonneg _)
      (segment_in_radius (hL.symm ▸ hl) (hU.symm ▸ hu) v hv) _).trans hpower)
    t (hL.symm ▸ coherentPole_exp_neg x l) (hU.symm ▸ coherentPole_exp_neg x u) g hc
  rw [hL,hU] at hb
  have hs : D*(U-L) = π*((2*D)*((u:ℝ)-(l:ℝ))) := by
    dsimp only [L,U]
    ring
  rw [hs] at hb
  by_contra! h
  exact (not_lt_of_ge (mul_le_mul_of_nonneg_left h pi_pos.le)) hb

/-- For each enclosed positive nonprincipal pole, the normalized Fourier
residue is bounded by the principal-to-pole chord and radial decay. -/
theorem small_enclosed_ratio
    {n k : ℕ} (hn : 10000 ≤ n) (hk : 8 ≤ k) (hk' : k ≤ 99)
    {x R : ℝ} (hx : 0 ≤ x) (hR : 0 ≤ R)
    (hcap : R^2 ≤ ‖coherentPole x 0‖^2*(1+2/(k:ℝ)))
    (hmid : 1 ≤ (n:ℝ)*(π/‖coherentPole x 0‖)^2)
    {j : ℕ} (hj : 1 ≤ j) (henc : ‖coherentPole x (j:ℤ)‖ ≤ R) :
    let L := wideLogNumerator k x
    (‖coherentPole x 0‖/‖coherentPole x (j:ℤ)‖)^n *
      ‖Complex.exp (L (coherentPole x (j:ℤ))) /
        Complex.exp (L (coherentPole x 0))‖ ≤
          exp (-3*(j:ℝ)) := by
  intro L
  let p : ℝ := 2*j+1
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
  obtain ⟨hheight,hpower⟩ := small_residue_height_power hk hx hsqR hR (hbelow.trans hWr) hcap
  have hr : 0 < r := by
    have h := norm_nonneg (coherentPole x 0)
    dsimp only [r] at hsqR ⊢
    nlinarith [sq_nonneg x, sq_pos_of_pos pi_pos]
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
  have hlim : (W/r)^2 ≤ 5/4 := by
    rw [div_pow, div_le_iff₀ (sq_pos_of_pos hr)]
    have hkr : (8:ℝ) ≤ k := by exact_mod_cast hk
    have hc : 2/(k:ℝ) ≤ 1/4 := by
      rw [div_le_iff₀ (by linarith : (0:ℝ) < k)]
      linarith
    have he : 1+2/(k:ℝ) ≤ 5/4 := by linarith only [hc]
    change R^2 ≤ r^2*(1+2/(k:ℝ)) at hcap
    exact hWr.trans (hcap.trans (by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left he (sq_nonneg r)))
  obtain ⟨t,D,htD,ht,hbnd⟩ : ∃ t D : ℝ, ((t=12/5 ∧ D=9/4) ∨ (t=1 ∧ D=1/10)) ∧
      t ≤ (n:ℝ)*(π/r)^2 ∧ π*(31/10)*(∑' i : ℕ, poissonTerm (k-1) (x*(i+1:ℕ))) < D := by
    by_cases h200 : x ≤ 200
    · exact ⟨12/5,9/4,Or.inl ⟨rfl,rfl⟩,small_height_middle hn hx h200 hr hsqR,small_mid_vertical_budget hk hheight⟩
    · exact ⟨1,1/10,Or.inr ⟨rfl,rfl⟩,hmid,small_far_vertical_budget hk' (le_of_not_ge h200)⟩
  have hrad := small_enclosed_radius_decay hr hW (show 1 ≤ p by linarith) hZ hlim ht
  have hj' : (0:ℤ) < (j:ℤ) := by omega
  have hc := small_logTilt_chord (by linarith only [hheight] : 0 < x) hbnd hpower hj' (hrW.trans henc) henc
  have hi : (2*D)*(((j:ℤ):ℝ)-(0:ℤ)) = D*(p-1) := by
    dsimp [p]
    push_cast
    ring
  rw [hi] at hc
  have htilt : ‖Complex.exp (L (coherentPole x (j:ℤ))) /
      Complex.exp (L (coherentPole x 0))‖ ≤ exp (D*(p-1)) := by
    rw [←Complex.exp_sub, Complex.norm_exp]
    exact exp_le_exp.mpr ((le_abs_self _).trans
      ((Complex.abs_re_le_norm _).trans hc.le))
  apply (mul_le_mul hrad htilt (norm_nonneg _) (exp_pos _).le).trans
  rw [←exp_add]
  exact exp_le_exp.mpr (small_joint_residue_exponent hj htD)

/-- Weighted and unweighted budgets for the positive half of the enclosed
nonprincipal residues. Paired conjugate residues have the same ratio. -/
theorem small_enclosed_budgets
    {n k : ℕ} (hn : 10000 ≤ n) (hk : 8 ≤ k) (hk' : k ≤ 99)
    {x R : ℝ} (hx : 0 ≤ x) (hR : 0 ≤ R)
    (hcap : R^2 ≤ ‖coherentPole x 0‖^2*(1+2/(k:ℝ)))
    (hmid : 1 ≤ (n:ℝ)*(π/‖coherentPole x 0‖)^2)
    (s : Finset ℕ) (henc : ∀ i ∈ s, ‖coherentPole x ((i+1:ℕ):ℤ)‖ ≤ R) :
    let L := wideLogNumerator k x
    let f (i : ℕ) := (‖coherentPole x 0‖/‖coherentPole x ((i+1:ℕ):ℤ)‖)^n *
      ‖Complex.exp (L (coherentPole x ((i+1:ℕ):ℤ))) /
        Complex.exp (L (coherentPole x 0))‖
    (∑ i ∈ s, (2*(i+1:ℕ)+1:ℝ)*f i) ≤ 1/5 ∧ (∑ i ∈ s, f i) ≤ 1/15 := by
  intro L f
  have hw : (∑ i ∈ s, (2*(i+1:ℕ)+1:ℝ)*f i) ≤ 1/5 := by
    apply small_weighted_residue_sum
    intro i hi
    exact small_enclosed_ratio hn hk hk' hx hR hcap hmid (Nat.succ_pos i) (henc i hi)
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
theorem original_small_cutoff_enclosed_budgets
    {n k : ℕ} (hn : 10000 ≤ n) (hk : 8 ≤ k) (hk' : k ≤ 99)
    {x R : ℝ} (hx : 0 ≤ x) (hR : 0 ≤ R)
    (hcap : R^2 ≤ ‖coherentPole x 0‖^2*(1+2/(k:ℝ)))
    (hmid : 1 ≤ (n:ℝ)*(π/‖coherentPole x 0‖)^2)
    (s : Finset ℕ) (henc : ∀ i ∈ s, ‖coherentPole x ((i+1:ℕ):ℤ)‖ ≤ R) :
    let T := coherentTilt k (-exp (-x))
    let f (i : ℕ) := (‖coherentPole x 0‖/‖coherentPole x ((i+1:ℕ):ℤ)‖)^n *
      ‖seriesValue T (coherentPole x ((i+1:ℕ):ℤ))/seriesValue T (coherentPole x 0)‖
    (∑ i ∈ s, (2*(i+1:ℕ)+1:ℝ)*f i) ≤ 1/5 ∧ (∑ i ∈ s, f i) ≤ 1/15 := by
  intro T f
  have he (w : ℂ) : seriesValue T w = Complex.exp (wideLogNumerator k x w) :=
    seriesValue_original_coherentTilt (by omega) _ _
  simp only [f, he]
  exact small_enclosed_budgets hn hk hk' hx hR hcap hmid s henc

#print axioms original_small_cutoff_enclosed_budgets
#print axioms small_logTilt_chord
#print axioms small_enclosed_ratio
#print axioms small_enclosed_budgets
end RepositoryQuotientAudit
