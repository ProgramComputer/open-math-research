import FourierCircleChoice
import FourierLogarithmicGap

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Complex Real

private theorem gap_of_squared_gap (w p : ℂ) (R δ h : ℝ) (hw : ‖w‖ = R)
    (hg : h ≤ |R^2 - ‖p‖^2|) (hh : δ*(2*R+δ) ≤ h) : δ ≤ ‖w-p‖ := by
  by_contra! hsmall
  have hrad : |R-‖p‖| < δ := (hw ▸ abs_norm_sub_norm_le w p).trans_lt hsmall
  have hR : 0 ≤ R := hw ▸ norm_nonneg w
  have hP : R+‖p‖ ≤ 2*R+δ := by linarith [(abs_lt.mp hrad).1]
  have he : |R^2-‖p‖^2| = |R-‖p‖| * (R+‖p‖) := by
    rw [sq_sub_sq,abs_mul,abs_of_nonneg (add_nonneg hR (norm_nonneg p))]
    ring
  rw [he] at hg
  have hδ' : 0 < δ := (norm_nonneg _).trans_lt hsmall
  have hb := calc
    |R-‖p‖| * (R+‖p‖) ≤ |R-‖p‖| * (2*R+δ) := mul_le_mul_of_nonneg_left hP (abs_nonneg _)
    _ < δ*(2*R+δ) := mul_lt_mul_of_pos_right hrad (by linarith)
  linarith

/-- One of the two explicit comparison radii has an ordinary distance gap
at least (49/100) c r/K at every point and satisfies the contraction bound
there for all radial contractions simultaneously. -/
theorem original_circle_kernel_gap_and_denominators {x K s r : ℝ} (hx : 44 ≤ x) (hk : 100 ≤ K)
    (hs : 0 ≤ s) (hr : 0 < r) (hr2 : r^2=s^2+π^2) (hu : 1 ≤ x*(K*(π/r)^2)) :
    let c := min (1/25 : ℝ) (4/x)
    let δ := (49/100)*(c*r/K)
    ∃ a ∈ ({2-2*c,2} : Set ℝ), ∃ R : ℝ, 0 < R ∧ R^2=r^2*(1+a/K) ∧
      (∀ l : ℤ, c*r^2/K ≤ |R^2-‖(s:ℂ)+(2*(l:ℂ)+1)*π*I‖^2|) ∧
      ∀ w : ℂ, ‖w‖=R →
        (∀ l : ℤ, δ ≤ ‖w-((s:ℂ)+(2*(l:ℂ)+1)*π*I)‖) ∧
        ∀ α : ℝ, 0 ≤ α → α ≤ 1 →
          ‖1+Complex.exp ((α:ℂ)*w-s)‖ / ‖1+Complex.exp (w-s)‖ ≤
            1+‖(α:ℂ)*w-w‖*(1+δ)/δ := by
  let c := min (1/25 : ℝ) (4/x)
  let d := c*r/K
  let δ := (49/100)*d
  have hK : 0 < K := by linarith
  have hx0 : 0 < x := by linarith
  have hc : 0 < c := lt_min (by norm_num) (by positivity)
  have hc1 : c ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hd : 0 < d := div_pos (mul_pos hc hr) hK
  have hδ : 0 < δ := mul_pos (by norm_num) hd
  obtain ⟨a,ha,_,hahi,R,hR,hR2,hgap⟩ := original_odd_circle_modulus_gap hx hK hr hr2 hu
  have haK : a/K ≤ 2/100 := (div_le_iff₀ hK).mpr (by linarith)
  have hRmax : R ≤ (101/100)*r := by
    have he := mul_le_mul_of_nonneg_left (add_le_add_left haK 1) (sq_nonneg r)
    nlinarith [sq_nonneg r]
  have hdmax : d ≤ r/100 := (div_le_iff₀ hK).mpr (by
    have h1 := mul_le_mul_of_nonneg_right hc1 hr.le
    have h2 := mul_le_mul_of_nonneg_left hk (by positivity : 0 ≤ r/100)
    linarith)
  have hsum : 2*R+δ ≤ (203/100)*r := by dsimp only [δ]; linarith
  have hsize : δ*(2*R+δ) ≤ c*r^2/K := calc
    _ ≤ δ*((203/100)*r) := mul_le_mul_of_nonneg_left hsum hδ.le
    _ ≤ d*r := by dsimp only [δ]; nlinarith [mul_pos hd hr]
    _ = _ := by dsimp only [d]; ring
  have hsquared (l : ℤ) : c*r^2/K ≤ |R^2-‖(s:ℂ)+(2*(l:ℂ)+1)*π*I‖^2| := by
    have he : (s:ℂ)+(2*(l:ℂ)+1)*π*I = (⟨s,(2*(l:ℝ)+1)*π⟩ : ℂ) := by
      apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im]
    rw [he]
    exact hgap l
  refine ⟨a,ha,R,hR,hR2,hsquared,?_⟩
  intro w hw
  have hg (l : ℤ) : δ ≤ ‖w-((s:ℂ)+(2*(l:ℂ)+1)*π*I)‖ :=
    gap_of_squared_gap _ _ R δ (c*r^2/K) hw (hsquared l) hsize
  exact ⟨hg,fun α ha' hα => original_contracted_circle_ratio hs ha' hα hδ w hg⟩

/-- Projection of the simultaneous choice onto the physical denominator bounds. -/
theorem original_circle_uniform_denominators {x K s r : ℝ} (hx : 44 ≤ x) (hk : 100 ≤ K)
    (hs : 0 ≤ s) (hr : 0 < r) (hr2 : r^2=s^2+π^2) (hu : 1 ≤ x*(K*(π/r)^2)) :
    let c := min (1/25 : ℝ) (4/x)
    let δ := (49/100)*(c*r/K)
    ∃ a ∈ ({2-2*c,2} : Set ℝ), ∃ R : ℝ, 0 < R ∧ R^2=r^2*(1+a/K) ∧
      ∀ w : ℂ, ‖w‖=R →
        (∀ l : ℤ, δ ≤ ‖w-((s:ℂ)+(2*(l:ℂ)+1)*π*I)‖) ∧
        ∀ α : ℝ, 0 ≤ α → α ≤ 1 →
          ‖1+Complex.exp ((α:ℂ)*w-s)‖ / ‖1+Complex.exp (w-s)‖ ≤
            1+‖(α:ℂ)*w-w‖*(1+δ)/δ := by
  obtain ⟨a,ha,R,hR,hR2,_,hden⟩ := original_circle_kernel_gap_and_denominators hx hk hs hr hr2 hu
  exact ⟨a,ha,R,hR,hR2,hden⟩

#print axioms original_circle_kernel_gap_and_denominators
#print axioms original_circle_uniform_denominators
end OpenMathResearch.LongCycleExcedances
