import FourierSelectedAmplitude
import SmallCutoffCircleDecay

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real

/-- Uniform exponential decay on either candidate circle down to cutoff eight. -/
theorem small_cutoff_circle_decay {k r R a : ℝ} (hk : 8 ≤ k) (hr : 0 < r) (hR : 0 < R)
    (ha : 48/25 ≤ a) (hhi : a ≤ 2) (hR2 : R^2=r^2*(1+a/k)) (n : ℕ) :
    (r/R)^n ≤ exp (-(4/5)*((n:ℝ)/k)) := by
  have hk0 : 0 < k := by linarith
  let t := R/r
  have ht : 0 < t := div_pos hR hr
  have hsq : t^2=1+a/k := by
    dsimp only [t]; rw [div_pow,hR2]; field_simp <;> ring
  have hv : a/k ≤ 1/4 := (div_le_iff₀ hk0).mpr (by linarith)
  have hThi : t ≤ 9/8 := by nlinarith only [hsq,hv,sq_nonneg (t-9/8)]
  have hden : t*(1+t) ≤ 12/5 := by linarith only [hsq,hv,hThi,show t*(1+t)=t+t^2 by ring]
  have hlog : log (r/R) ≤ 1/t-1 := by
    have he : r/R = 1/t := by dsimp [t]; field_simp
    rw [he]; exact log_le_sub_one_of_pos (by positivity)
  have hi : (4/5)/k ≤ 1-1/t := by
    have hp : 0 < t*(1+t) := by positivity
    have he : 1-1/t=(a/k)/(t*(1+t)) := by
      rw [show a/k=t^2-1 by linarith only [hsq]]
      field_simp <;> ring
    rw [he,le_div_iff₀ hp,div_mul_eq_mul_div,div_le_div_iff_of_pos_right hk0]
    nlinarith only [hden,ha]
  apply (log_le_log_iff (pow_pos (div_pos hr hR) _) (exp_pos _)).mp
  rw [log_pow,log_exp]
  have hle : log (r/R) ≤ -((4/5)/k) := by linarith
  have hmul := mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg (α:=ℝ) n)
  linarith only [hmul,show (n:ℝ)*-((4/5)/k)= -(4/5)*((n:ℝ)/k) by ring]

open private gap_of_squared_gap from FourierOriginalDenominators in
/-- The squared gap is at least four times $r^2/n$ when $n/k$ exceeds 100.
It gives a pointwise distance of at least $r/n$ everywhere on the circle. -/
theorem small_cutoff_selected_circle {n k s r : ℝ} (hn : 10000≤n) (hk : 8≤k) (hk' : k≤100)
    (hr : 0<r) (hsq : r^2=s^2+π^2) (hm : 1≤n*(π/r)^2) :
    let x := n/k
    let c := min (1/25:ℝ) (4/x)
    ∃ a ∈ ({2-2*c,2}:Set ℝ), 48/25≤a ∧ a≤2 ∧ ∃ R : ℝ, 0<R ∧ R^2=r^2*(1+a/k) ∧
    r≤R ∧ R≤(1+1/k)*r ∧
    (∀ l : ℤ, c*r^2/k ≤ |R^2-‖(s:ℂ)+(2*(l:ℂ)+1)*π*Complex.I‖^2|) ∧
    ∀ w : ℂ, ‖w‖=R → ∀ l : ℤ, r/n ≤ ‖w-((s:ℂ)+(2*(l:ℂ)+1)*π*Complex.I)‖ := by
  intro x c
  have hk0 : 0<k := by linarith
  have hn0 : 0<n := by linarith
  have hx : 100≤x := (le_div_iff₀ hk0).mpr (by linarith)
  have hx0 : 0<x := by linarith
  have he : x*k=n := div_mul_cancel₀ _ hk0.ne'
  have hc : c=4/x := min_eq_right ((div_le_iff₀ hx0).mpr (by linarith))
  have hsize : 1≤x*(k*(π/r)^2) := by rw [←mul_assoc,he]; exact hm
  obtain ⟨a,ha,hal,hah,R,hR,hR2,hgap⟩ := original_odd_circle_modulus_gap (by linarith : 44≤x) hk0 hr hsq hsize
  have hq : 0≤a/k := div_nonneg (by linarith) hk0.le
  have hrR : r≤R := by nlinarith [mul_nonneg (sq_nonneg r) hq]
  have hRR : R≤(1+1/k)*r := by
    apply (sq_le_sq₀ hR.le (by positivity)).mp
    calc
      R^2 ≤ r^2*(1+2/k) := by rw [hR2]; gcongr
      _ ≤ r^2*(1+2/k)+(r/k)^2 := le_add_of_nonneg_right (sq_nonneg _)
      _ = _ := by ring
  have hcap : R≤(9/8)*r := hRR.trans (mul_le_mul_of_nonneg_right
    (by linarith only [(div_le_iff₀ hk0).mpr (by linarith : (1:ℝ)≤(1/8)*k)] : 1+1/k≤9/8) hr.le)
  have hd : 0<r/n := div_pos hr hn0
  have hsum : 2*R+r/n ≤ 4*r := by
    linarith only [hcap, div_le_self hr.le (by linarith : 1≤n), hr]
  have hsmall : (r/n)*(2*R+r/n) ≤ c*r^2/k := by
    apply (mul_le_mul_of_nonneg_left hsum hd.le).trans
    apply le_of_eq
    rw [hc]
    dsimp only [x]; field_simp <;> ring
  have hsquared (l : ℤ) : c*r^2/k ≤ |R^2-‖(s:ℂ)+(2*(l:ℂ)+1)*π*Complex.I‖^2| := by
    have e : (s:ℂ)+(2*(l:ℂ)+1)*π*Complex.I = (⟨s,(2*(l:ℝ)+1)*π⟩ : ℂ) := by
      apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im]
    rw [e]; exact hgap l
  exact ⟨a,ha,hal,hah,R,hR,hR2,hrR,hRR,hsquared,
    fun w hw l => gap_of_squared_gap _ _ _ _ _ hw (hsquared l) hsmall⟩

#print axioms small_cutoff_circle_decay
#print axioms small_cutoff_selected_circle
end OpenMathResearch.LongCycleExcedances
