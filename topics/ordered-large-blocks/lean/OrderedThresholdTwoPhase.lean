import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! The scalar equation for the imaginary parts of the nonreal poles of the
ordered-partition generating function at threshold two. -/

namespace OrderedThresholdTwoPhase

open Real Set

noncomputable def polePhase (t : ℝ) : ℝ :=
  t * cos t / sin t - log (t / sin t)

/-- The exponential pole equation reduces exactly to a single real phase equation
in the upper half-plane. -/
theorem upper_pole_iff {u : ℂ} {p : ℝ} (hp : 0 < p) (ht : 0 < u.im) :
    Complex.exp u = (p : ℂ)*u ↔
      0 < sin u.im ∧ u.re = u.im * cos u.im / sin u.im ∧
      polePhase u.im = log p := by
  constructor
  · intro he
    have hre := congrArg Complex.re he
    have him := congrArg Complex.im he
    simp only [Complex.exp_re, Complex.exp_im, Complex.ofReal_mul'] at hre him
    have hprod : 0 < exp u.re * sin u.im := by rw [him]; exact mul_pos hp ht
    have hs : 0 < sin u.im := pos_of_mul_pos_right hprod (le_of_lt (exp_pos _))
    have he' : exp u.re = p * (u.im / sin u.im) := by
      rw [← mul_div_assoc]
      exact (eq_div_iff hs.ne').2 him
    have hr : u.re = u.im * cos u.im / sin u.im := by
      rw [he'] at hre
      field_simp [hs.ne'] at hre ⊢
      apply mul_left_cancel₀ (a := p) hp.ne'
      linear_combination -hre
    refine ⟨hs, hr, ?_⟩
    unfold polePhase
    rw [← hr]
    have hlog := congrArg log he'
    rw [Real.log_exp, Real.log_mul hp.ne' (div_pos ht hs).ne'] at hlog
    linarith
  · rintro ⟨hs, hr, hphase⟩
    unfold polePhase at hphase
    rw [← hr] at hphase
    have hlog : u.re = log (p * (u.im / sin u.im)) := by
      rw [Real.log_mul hp.ne' (div_pos ht hs).ne']
      linarith
    have he : exp u.re = p * (u.im / sin u.im) := by
      rw [hlog, Real.exp_log (mul_pos hp (div_pos ht hs))]
    apply Complex.ext
    · simp only [Complex.exp_re, Complex.ofReal_mul', he]
      rw [hr]
      ring
    · simp only [Complex.exp_im, Complex.ofReal_mul', he]
      field_simp [hs.ne']

theorem derivative_polePhase {t : ℝ} (ht : 0 < t) (hs : 0 < sin t) :
    HasDerivAt polePhase (-t - (t * cos t / sin t - 1)^2 / t) t := by
  have h := (((hasDerivAt_id t).mul (Real.hasDerivAt_cos t)).div
    (Real.hasDerivAt_sin t) hs.ne').sub
    (((hasDerivAt_id t).div (Real.hasDerivAt_sin t) hs.ne').log
      (div_ne_zero ht.ne' hs.ne'))
  convert h using 1
  simp only [id_eq, one_mul]
  field_simp [ht.ne', hs.ne']
  ring

theorem strictAntiOn_polePhase {D : Set ℝ} (hc : Convex ℝ D)
    (hpos : ∀ t ∈ D, 0 < t ∧ 0 < sin t) : StrictAntiOn polePhase D := by
  apply strictAntiOn_of_deriv_neg hc
  · intro t ht
    exact (derivative_polePhase (hpos t ht).1 (hpos t ht).2).continuousAt.continuousWithinAt
  · intro t ht
    obtain ⟨h, hs⟩ := hpos t (interior_subset ht)
    rw [(derivative_polePhase h hs).deriv]
    have := div_nonneg (sq_nonneg (t * cos t / sin t - 1)) h.le
    linarith

theorem angle_unique {D : Set ℝ} (hc : Convex ℝ D)
    (hpos : ∀ t ∈ D, 0 < t ∧ 0 < sin t) {s t p : ℝ}
    (hs : s ∈ D) (ht : t ∈ D) (hp : polePhase s = p) (hq : polePhase t = p) : s = t :=
  (strictAntiOn_polePhase hc hpos).injOn hs ht (hp.trans hq.symm)

/-- In each upper pole band the imaginary part is uniquely determined by the level. -/
theorem unique_in_pole_band (k : ℕ) {s t p : ℝ}
    (hs : s ∈ Ioo (k * (2*π)) (k * (2*π) + π))
    (ht : t ∈ Ioo (k * (2*π)) (k * (2*π) + π))
    (hp : polePhase s = p) (hq : polePhase t = p) : s = t := by
  apply angle_unique (convex_Ioo _ _) _ hs ht hp hq
  intro x hx
  have h0 : 0 ≤ (k : ℝ) * (2*π) := by positivity
  obtain ⟨hl, hr⟩ := hx
  refine ⟨lt_of_le_of_lt h0 hl, ?_⟩
  rw [← Real.sin_sub_nat_mul_two_pi x k]
  exact Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hl) (by linarith)

theorem at_most_one_upper_pole (k : ℕ) {p : ℝ} (hp : 0 < p) {u w : ℂ}
    (hu : u.im ∈ Ioo (k * (2*π)) (k * (2*π) + π))
    (hw : w.im ∈ Ioo (k * (2*π)) (k * (2*π) + π))
    (eu : Complex.exp u = (p : ℂ)*u) (ew : Complex.exp w = (p : ℂ)*w) : u = w := by
  have h0 : 0 ≤ (k : ℝ) * (2*π) := by positivity
  obtain ⟨_, hru, hpu⟩ := (upper_pole_iff hp (lt_of_le_of_lt h0 hu.1)).mp eu
  obtain ⟨_, hrw, hpw⟩ := (upper_pole_iff hp (lt_of_le_of_lt h0 hw.1)).mp ew
  have him := unique_in_pole_band k hu hw hpu hpw
  exact Complex.ext (by rw [hru, hrw, him]) him

theorem consecutive_sign {s phase shift e₁ e₂ θ : ℝ} (hs : |s| = 1) (hθ : 0 < θ)
    (hroot : cos phase = e₁) (hprev : |e₁| ≤ θ / 16)
    (hnext : |e₂| ≤ θ / 16) (hband : 1/2 ≤ s * sin phase)
    (hshift : 4*θ/9 ≤ sin shift) : 0 < s * (-cos (phase+shift) + e₂) := by
  have hm : 0 ≤ sin shift := by linarith
  have hp := mul_le_mul_of_nonneg_right hband hm
  have ha : |s * e₁ * cos shift| ≤ θ/16 := by
    rw [abs_mul, abs_mul, hs, one_mul]
    exact (mul_le_mul_of_nonneg_left (abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩)
      (abs_nonneg e₁)).trans (by simpa using hprev)
  have hb : |s * e₂| ≤ θ/16 := by simpa only [abs_mul, hs, one_mul] using hnext
  rw [Real.cos_add, hroot]
  have h1 := (abs_le.mp ha).2
  have h2 := (abs_le.mp hb).1
  nlinarith

end OrderedThresholdTwoPhase
