import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Real.Pi.Bounds

namespace OpenMathResearch.LongCycleExcedances
open Set Real

private theorem variation_of_derivative_bound {a b : ℝ} (hab : a ≤ b)
    {F B f g : ℝ → ℝ}
    (hF : ∀ x ∈ Icc a b, HasDerivAt F (f x) x)
    (hB : ∀ x ∈ Icc a b, HasDerivAt B (g x) x)
    (h : ∀ x ∈ Icc a b, |f x| ≤ g x) : |F b - F a| ≤ B b - B a := by
  have mono (s : ℝ) (hs : s = 1 ∨ s = -1) : MonotoneOn (fun x => B x + s*F x) (Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
    · intro x hx
      exact ((hB x hx).add ((hF x hx).const_mul s)).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hxClosed := Ioo_subset_Icc_self hx
      exact ((hB x hxClosed).add ((hF x hxClosed).const_mul s)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hx' := Ioo_subset_Icc_self hx
      have hd : HasDerivAt (fun y => B y+s*F y) (g x+s*f x) x :=
        (hB x hx').add ((hF x hx').const_mul s)
      rw [hd.deriv]
      have hb := abs_le.mp (h x hx')
      rcases hs with hs | hs <;> rw [hs] <;> linarith
  have left := (mono 1 (Or.inl rfl)) (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) hab
  have right := (mono (-1) (Or.inr rfl)) (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) hab
  dsimp only at left right
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Integration by parts as a derivative barrier. Subtracting the oscillatory
primitive leaves its differentiated cosecant weight and the supplied error. -/
theorem cosecant_oscillation_variation {a b m D C : ℝ} {F e : ℝ → ℝ}
    (hm : 0 < m) (hD : 0 ≤ D) (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ π/2)
    (hF : ∀ x ∈ Icc a b, HasDerivAt F (-sin (m*x)/sin x+e x) x)
    (hErr : ∀ x ∈ Icc a b, |e x| ≤ D/sin x)
    (hC : ∀ x ∈ Icc a b, 1/sin x ≤ C) :
    |(F b - cos (m*b)/(m*sin b)) - (F a - cos (m*a)/(m*sin a))| ≤
      (1/sin a-1/sin b)/m + D*C*(b-a) := by
  let H (x : ℝ) := F x-cos (m*x)/(m*sin x)
  let B (x : ℝ) := -(1/sin x)/m+D*C*x
  let f (x : ℝ) := e x + cos (m*x)*cos x/(m*(sin x)^2)
  let g (x : ℝ) := cos x/(m*(sin x)^2)+D*C
  have hs (x : ℝ) (hx : x ∈ Icc a b) : 0 < sin x :=
    sin_pos_of_pos_of_lt_pi (ha.trans_le hx.1) (by linarith [hx.2, pi_pos])
  have hH (x : ℝ) (hx : x ∈ Icc a b) : HasDerivAt H (f x) x := by
    have hmc := ((hasDerivAt_id x).const_mul m).cos
    have hd := (hF x hx).sub (hmc.div ((hasDerivAt_sin x).const_mul m)
      (mul_ne_zero hm.ne' (hs x hx).ne'))
    change HasDerivAt H
      ((-sin (m*x)/sin x+e x)-
        (-sin (m*x)*(m*1)*(m*sin x)-cos (m*x)*(m*cos x))/(m*sin x)^2) x at hd
    have he :
        (-sin (m*x)/sin x+e x)-
          (-sin (m*x)*(m*1)*(m*sin x)-cos (m*x)*(m*cos x))/(m*sin x)^2 = f x := by
      dsimp [f]
      field_simp [hm.ne', (hs x hx).ne'] <;> ring
    rwa [he] at hd
  have hB (x : ℝ) (hx : x ∈ Icc a b) : HasDerivAt B (g x) x := by
    have hd := (((hasDerivAt_const x (1:ℝ)).div (hasDerivAt_sin x)
      (hs x hx).ne').neg.div_const m).add ((hasDerivAt_id x).const_mul (D*C))
    change HasDerivAt B
      (-((0*sin x-1*cos x)/(sin x)^2)/m+D*C*1) x at hd
    have he : -((0*sin x-1*cos x)/(sin x)^2)/m+D*C*1 = g x := by
      dsimp [g]
      field_simp [hm.ne', (hs x hx).ne'] <;> ring
    rwa [he] at hd
  have hbound (x : ℝ) (hx : x ∈ Icc a b) : |f x| ≤ g x := by
    have hc : 0 ≤ cos x := cos_nonneg_of_mem_Icc ⟨by linarith [hx.1, pi_pos], hx.2.trans hb⟩
    have he := (hErr x hx).trans (show D/sin x ≤ D*C by
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left (hC x hx) hD)
    have hp : |cos (m*x)*cos x/(m*(sin x)^2)| ≤ cos x/(m*(sin x)^2) := by
      rw [abs_div, abs_mul, abs_of_nonneg hc, abs_of_nonneg (by positivity : 0 ≤ m*(sin x)^2)]
      exact div_le_div_of_nonneg_right (by simpa using mul_le_mul_of_nonneg_right (abs_cos_le_one _) hc) (by positivity)
    exact (abs_add_le _ _).trans (by dsimp [g]; linarith)
  have hi := variation_of_derivative_bound hab hH hB hbound
  change _ ≤ _
  apply hi.trans_eq
  dsimp [B]
  ring

theorem high_angle_displacement {k : ℕ} (hk : 7 ≤ k) {F e : ℝ → ℝ}
    (hend : F (π/2) = 0)
    (hF : ∀ x ∈ Icc (π/6) (π/2),
      HasDerivAt F (-sin ((2*(k:ℝ)-1)*x)/sin x+e x) x)
    (hErr : ∀ x ∈ Icc (π/6) (π/2), |e x| ≤ 2*(3/5:ℝ)^(k-2)/sin x)
    {a : ℝ} (ha : π/6 ≤ a) (hb : a ≤ π/2) : |F a| < 1/2 := by
  let m : ℝ := 2*(k:ℝ)-1
  let D : ℝ := 2*(3/5:ℝ)^(k-2)
  let H (x : ℝ) := F x - cos (m*x)/(m*sin x)
  have hm₀ : (13:ℝ) ≤ m := by dsimp [m]; exact_mod_cast (show 13 ≤ (2:ℤ)*k-1 by omega)
  have hm : 0 < m := by linarith
  have hD : 0 ≤ D := by positivity
  have ha₀ : 0 < a := by linarith [pi_pos]
  have hsin (x : ℝ) (hx : x ∈ Icc (π/6) (π/2)) : 1/2 ≤ sin x := by
    rw [← sin_pi_div_six]
    exact sin_le_sin_of_le_of_le_pi_div_two (by linarith [pi_pos]) hx.2 hx.1
  have hc₁ (x : ℝ) (hx : x ∈ Icc (π/6) (π/2)) : 1/sin x ≤ 2 := by
    apply (div_le_iff₀ (by linarith [hsin x hx] : 0 < sin x)).2
    linarith [hsin x hx]
  have hc₂ (x : ℝ) (hx : x ∈ Icc (π/4) (π/2)) : 1/sin x ≤ 3/2 := by
    have h := sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [pi_pos] : -(π/2) ≤ π/4) hx.2 hx.1
    rw [sin_pi_div_four] at h
    have hsq := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
    have hs : (4:ℝ)/3 ≤ √2 := by
      by_contra! hh
      nlinarith [mul_nonneg (sub_nonneg.mpr hh.le)
        (show 0 ≤ (4:ℝ)/3 + √2 by positivity)]
    apply (div_le_iff₀ (by linarith : 0 < sin x)).2
    linarith
  have hendcos : cos (m*(π/2)) = 0 := by
    have he : ((k-1:ℕ):ℝ) = (k:ℝ)-1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
    rw [show m*(π/2) = π/2+((k-1:ℕ):ℝ)*π by dsimp [m]; rw [he]; ring,
      cos_add_nat_mul_pi, cos_pi_div_two, mul_zero]
  have hHend : H (π/2) = 0 := by simp [H, hend, hendcos]
  have segment {u v C : ℝ} (hu : π/6 ≤ u) (huv : u ≤ v) (hv : v ≤ π/2)
      (hc : ∀ x ∈ Icc u v, 1/sin x ≤ C) :
      |H v-H u| ≤ (1/sin u-1/sin v)/m + D*C*(v-u) :=
    cosecant_oscillation_variation hm hD (by linarith [pi_pos]) huv hv
      (fun x hx => hF x ⟨hu.trans hx.1, hx.2.trans hv⟩)
      (fun x hx => hErr x ⟨hu.trans hx.1, hx.2.trans hv⟩) hc
  have hmain : |H (π/2)-H a| ≤ (1/sin a-1)/m + D*(13*π/24) := by
    by_cases h : a ≤ π/4
    · have h₁ := segment ha h (by linarith [pi_pos])
        (fun x hx => hc₁ x ⟨ha.trans hx.1, by linarith [hx.2, pi_pos]⟩)
      have h₂ := segment (show π/6 ≤ π/4 by linarith [pi_pos])
        (show π/4 ≤ π/2 by linarith [pi_pos]) le_rfl hc₂
      rw [show H (π/2)-H a = (H (π/2)-H (π/4))+(H (π/4)-H a) by ring]
      apply (abs_add_le _ _).trans
      rw [sin_pi_div_two, div_one] at h₂
      simp only [sub_div] at h₁ h₂ ⊢
      nlinarith [mul_nonneg hD (sub_nonneg.mpr ha)]
    · have h' := le_of_not_ge h
      have h₁ := segment ha hb le_rfl (fun x hx => hc₂ x ⟨h'.trans hx.1,hx.2⟩)
      rw [sin_pi_div_two, div_one] at h₁
      exact h₁.trans (by nlinarith [mul_nonneg hD (sub_nonneg.mpr h'), mul_nonneg hD pi_pos.le])
  have hSa := hsin a ⟨ha,hb⟩
  have hcos : |cos (m*a)/(m*sin a)| ≤ 2/m := by
    rw [abs_div, abs_of_pos (mul_pos hm (by linarith)), div_mul_eq_div_div, div_right_comm]
    apply div_le_div_of_nonneg_right _ hm.le
    exact (div_le_div_of_nonneg_right (abs_cos_le_one _) (by linarith)).trans (hc₁ a ⟨ha,hb⟩)
  rw [hHend, zero_sub, abs_neg] at hmain
  have hphase : |F a| ≤ 3/m + D*(13*π/24) := by
    rw [show F a = H a + cos (m*a)/(m*sin a) by dsimp [H]; ring]
    have hc := div_le_div_of_nonneg_right (hc₁ a ⟨ha,hb⟩) hm.le
    exact (abs_add_le _ _).trans (by rw [sub_div] at hmain; rw [show (3:ℝ)/m = 2/m+2/m-1/m by ring]; linarith)
  have hPow : D ≤ 2*(3/5:ℝ)^5 := by
    dsimp [D]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)) (by norm_num)
  have hNum := add_le_add (div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 3)
    (by norm_num : (0:ℝ)<13) hm₀)
    (mul_le_mul hPow (show 13*π/24 ≤ 13*(3.15:ℝ)/24 by linarith [pi_lt_d2])
      (by positivity) (by positivity))
  exact (hphase.trans hNum).trans_lt (by norm_num)

theorem high_angle_displacement_of_deriv {k : ℕ} (hk : 7 ≤ k) {γ : ℝ → ℝ}
    (hend : γ (π/2) = π/2)
    (hdiff : ∀ x ∈ Icc (π/6) (π/2), DifferentiableAt ℝ γ x)
    (hErr : ∀ x ∈ Icc (π/6) (π/2),
      |deriv γ x - 1 + sin (((2*k-1:ℕ):ℝ)*x)/sin x| ≤ 2*(3/5:ℝ)^(k-2)/sin x)
    {a : ℝ} (ha : π/6 ≤ a) (hb : a ≤ π/2) : |γ a-a| < 1/2 := by
  let e (x : ℝ) := deriv γ x - 1 + sin (((2*k-1:ℕ):ℝ)*x)/sin x
  have hc : ((2*k-1:ℕ):ℝ) = 2*(k:ℝ)-1 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    rfl
  apply high_angle_displacement hk (F := fun x => γ x-x) (e := e) _ _ hErr ha hb
  · exact sub_eq_zero.mpr hend
  · intro x hx
    have h := (hdiff x hx).hasDerivAt.sub (hasDerivAt_id x)
    have he : -sin ((2*(k:ℝ)-1)*x)/sin x+e x = deriv γ x-1 := by
      dsimp [e]
      rw [hc]
      ring
    rwa [he]


#print axioms cosecant_oscillation_variation
#print axioms high_angle_displacement
#print axioms high_angle_displacement_of_deriv
end OpenMathResearch.LongCycleExcedances
