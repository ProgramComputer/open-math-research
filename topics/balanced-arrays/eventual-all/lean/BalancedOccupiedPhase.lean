import BalancedPhaseFirstHit
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Nat.Choose.Basic

namespace BalancedEventual.OccupiedPhase

open scoped BigOperators Topology
open Finset Filter

noncomputable section

def angle (d : ℕ) : ℝ := Real.pi / d

def direction (d s : ℕ) : ℂ := Complex.exp (Complex.ofReal ((s : ℝ) * angle d) * Complex.I)

/-- The row-size polynomial on the ray of angle pi/d. -/
def raySum (d r : ℕ) (w : ℕ → ℝ) (v : ℝ) : ℂ :=
  ∑ s ∈ range (r + 1), ((w s * v ^ s : ℝ) : ℂ) * direction d s

def rowWeight (d s : ℕ) : ℝ := d.choose s

/-- The common factor d(d-1) in the moment weights is omitted. -/
def momentWeight (d s : ℕ) : ℝ :=
  rowWeight d s * s * (d - s : ℕ)

abbrev rowSum (d r : ℕ) := raySum d r (rowWeight d)
abbrev momentSum (d r : ℕ) := raySum d r (momentWeight d)

/-- Dividing the moment sum by the positive radius removes its zero at zero. -/
def momentShift (d r : ℕ) (v : ℝ) : ℂ :=
  ∑ s ∈ range r, ((momentWeight d (s + 1) * v ^ s : ℝ) : ℂ) * direction d (s + 1)

theorem continuous_raySum (d r : ℕ) (w : ℕ → ℝ) : Continuous (raySum d r w) := by
  unfold raySum
  fun_prop

theorem continuous_momentShift (d r : ℕ) : Continuous (momentShift d r) := by
  unfold momentShift
  fun_prop

theorem momentSum_eq_mul_shift (d r : ℕ) (v : ℝ) :
    momentSum d r v = (v : ℂ) * momentShift d r v := by
  change raySum d r (momentWeight d) v = _
  unfold raySum momentShift
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp only [momentWeight, Nat.cast_zero, mul_zero, zero_mul, Complex.ofReal_zero, add_zero]
  apply Finset.sum_congr rfl
  intro s _
  simp only [pow_succ, Complex.ofReal_mul]
  ring

theorem raySum_im (d r : ℕ) (w : ℕ → ℝ) (v : ℝ) :
    (raySum d r w v).im = ∑ s ∈ range (r + 1), w s * v ^ s * Real.sin (s * angle d) := by
  simp only [raySum, Complex.im_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [direction, Complex.exp_mul_I, ← Complex.ofReal_sin, ← Complex.ofReal_cos]
  simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.add_im, zero_mul, mul_zero, one_mul, mul_one, add_zero, zero_add]

theorem raySum_im_pos {d r : ℕ} {w : ℕ → ℝ} {v : ℝ}
    (hr : 1 ≤ r) (hrd : r < d) (hv : 0 < v)
    (hw : ∀ s, 0 ≤ w s) (hw1 : 0 < w 1) :
    0 < (raySum d r w v).im := by
  have hd : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hangle : 0 < angle d := div_pos Real.pi_pos hd
  have hsine (s : ℕ) (hs : s ≤ r) : 0 ≤ Real.sin (s * angle d) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi (mul_nonneg (Nat.cast_nonneg _) hangle.le)
    have hs' : (s : ℝ) ≤ d := by exact_mod_cast (hs.trans hrd.le)
    calc
      (s : ℝ) * angle d ≤ (d : ℝ) * angle d :=
        mul_le_mul_of_nonneg_right hs' hangle.le
      _ = Real.pi := by rw [angle, mul_div_cancel₀ _ hd.ne']
  have h1 : angle d < Real.pi := by
    have hd1 : (1 : ℝ) < d := by exact_mod_cast (show 1 < d by omega)
    exact (div_lt_iff₀ hd).2 (by simpa using mul_lt_mul_of_pos_left hd1 Real.pi_pos)
  rw [raySum_im]
  apply Finset.sum_pos' (fun s hs =>
    mul_nonneg (mul_nonneg (hw s) (pow_nonneg hv.le _)) (hsine s (Nat.le_of_lt_succ (Finset.mem_range.mp hs))))
  refine ⟨1, Finset.mem_range.mpr (by omega), ?_⟩
  simpa using mul_pos (mul_pos hw1 hv) (Real.sin_pos_of_pos_of_lt_pi hangle h1)

theorem rowSum_im_pos {d r : ℕ} {v : ℝ} (hr : 1 ≤ r) (hrd : r < d) (hv : 0 < v) :
    0 < (rowSum d r v).im := by
  apply raySum_im_pos hr hrd hv
  · intro s
    unfold rowWeight
    positivity
  · simp only [rowWeight, Nat.choose_one_right]
    exact_mod_cast (show 0 < d by omega)

theorem momentSum_im_pos {d r : ℕ} {v : ℝ} (hr : 1 ≤ r) (hrd : r < d) (hv : 0 < v) :
    0 < (momentSum d r v).im := by
  apply raySum_im_pos hr hrd hv
  · intro s
    unfold momentWeight rowWeight
    positivity
  · unfold momentWeight rowWeight
    have hd : 0 < d := by omega
    have hd1 : 0 < d - 1 := by omega
    rw [Nat.choose_one_right]
    positivity

/-- The unwrapped phase is the difference of two principal arguments,
with the first argument also counted in the denominator correction. -/
def phase (n d r : ℕ) (v : ℝ) : ℝ :=
  (n : ℝ) * (rowSum d r v).arg -
    (((d : ℝ) - 1) / 2) * ((momentSum d r v).arg - (rowSum d r v).arg)

theorem continuous_logRadius_phase (n : ℕ) {d r : ℕ} (hr : 1 ≤ r) (hrd : r < d) :
    Continuous (fun x => phase n d r (Real.exp x)) := by
  have harg (w : ℕ → ℝ) (hpos : ∀ v > 0, 0 < (raySum d r w v).im) :
      Continuous (fun x => (raySum d r w (Real.exp x)).arg) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    change ContinuousAt (Complex.arg ∘ (raySum d r w ∘ Real.exp)) x
    have hInner : ContinuousAt (raySum d r w ∘ Real.exp) x :=
      ((continuous_raySum d r w).comp Real.continuous_exp).continuousAt
    have hOuter : ContinuousAt Complex.arg ((raySum d r w ∘ Real.exp) x) :=
      Complex.continuousAt_arg (Complex.mem_slitPlane_iff.mpr
        (Or.inr (hpos _ (Real.exp_pos x)).ne'))
    exact hOuter.comp hInner
  have hrow := harg (rowWeight d) (fun _ hv => rowSum_im_pos hr hrd hv)
  have hmoment := harg (momentWeight d) (fun _ hv => momentSum_im_pos hr hrd hv)
  exact (continuous_const.mul hrow).sub (continuous_const.mul (hmoment.sub hrow))

theorem direction_arg {d s : ℕ} (hd : 0 < d) (hs : s < d) :
    (direction d s).arg = s * angle d := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hs' : (s : ℝ) < d := by exact_mod_cast hs
  have ha : 0 < angle d := div_pos Real.pi_pos hd'
  rw [direction, Complex.exp_mul_I]
  exact Complex.arg_cos_add_sin_mul_I ⟨(neg_lt_zero.mpr Real.pi_pos).trans_le
    (mul_nonneg (Nat.cast_nonneg _) ha.le), (show (s : ℝ) * angle d < Real.pi by
      calc
        _ < (d : ℝ) * angle d := mul_lt_mul_of_pos_right hs' ha
        _ = Real.pi := by rw [angle, mul_div_cancel₀ _ hd'.ne']).le⟩

theorem direction_im_pos {d s : ℕ} (hs : 0 < s) (hsd : s < d) :
    0 < (direction d s).im := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast (hs.trans hsd)
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hsd' : (s : ℝ) < d := by exact_mod_cast hsd
  have ha : 0 < angle d := div_pos Real.pi_pos hd'
  rw [direction, Complex.exp_mul_I, ← Complex.ofReal_sin, ← Complex.ofReal_cos]
  simpa only [Complex.add_im, Complex.ofReal_im, Complex.ofReal_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, zero_mul, mul_zero, mul_one, add_zero, zero_add] using
    Real.sin_pos_of_pos_of_lt_pi (mul_pos hs' ha)
    (show (s : ℝ) * angle d < Real.pi by
      calc
        _ < (d : ℝ) * angle d := mul_lt_mul_of_pos_right hsd' ha
        _ = Real.pi := by rw [angle, mul_div_cancel₀ _ hd'.ne'])

theorem raySum_zero (d r : ℕ) (w : ℕ → ℝ) : raySum d r w 0 = (w 0 : ℂ) := by
  rw [raySum, Finset.sum_range_succ']
  simp [direction, pow_succ]

theorem momentShift_zero {d r : ℕ} (hr : 1 ≤ r) :
    momentShift d r 0 = (momentWeight d 1 : ℂ) * direction d 1 := by
  cases r with
  | zero => omega
  | succ r => rw [momentShift, Finset.sum_range_succ']; simp [pow_succ]

theorem momentWeight_one_pos {d : ℕ} (hd : 1 < d) : 0 < momentWeight d 1 := by
  unfold momentWeight rowWeight
  have hd' : 0 < d := by omega
  have hd1 : 0 < d - 1 := by omega
  rw [Nat.choose_one_right]
  positivity

theorem tendsto_phase_atBot (n : ℕ) {d r : ℕ} (hr : 1 ≤ r) (hrd : r < d) :
    Tendsto (fun x => phase n d r (Real.exp x)) atBot
      (𝓝 (-(((d : ℝ) - 1) / 2) * angle d)) := by
  have hrow0 : rowSum d r 0 = 1 := by
    change raySum d r (rowWeight d) 0 = 1
    rw [raySum_zero]
    simp [rowWeight]
  have hrow : Tendsto (fun x => (rowSum d r (Real.exp x)).arg) atBot (𝓝 0) := by
    have hlim := ((continuous_raySum d r (rowWeight d)).continuousAt.tendsto
      (x := (0 : ℝ))).comp Real.tendsto_exp_atBot
    change Tendsto (fun x => rowSum d r (Real.exp x)) atBot (𝓝 (rowSum d r 0)) at hlim
    rw [hrow0] at hlim
    simpa using (Complex.continuousAt_arg Complex.one_mem_slitPlane).tendsto.comp hlim
  have hd : 1 < d := hr.trans_lt hrd
  have hp := momentWeight_one_pos hd
  have hs : momentShift d r 0 ∈ Complex.slitPlane := by
    rw [momentShift_zero hr, Complex.mem_slitPlane_iff]
    right
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, add_zero]
    exact (mul_pos hp (direction_im_pos Nat.zero_lt_one hd)).ne'
  have hsarg : (momentShift d r 0).arg = angle d := by
    rw [momentShift_zero hr, Complex.arg_real_mul _ hp,
      direction_arg (by omega) hd, Nat.cast_one, one_mul]
  have hm : Tendsto (fun x => (momentSum d r (Real.exp x)).arg) atBot (𝓝 (angle d)) := by
    have hlim := (Complex.continuousAt_arg hs).tendsto.comp
      ((continuous_momentShift d r).continuousAt.tendsto.comp Real.tendsto_exp_atBot)
    rw [hsarg] at hlim
    refine hlim.congr (fun x => ?_)
    rw [momentSum_eq_mul_shift, Complex.arg_real_mul _ (Real.exp_pos x)]
    rfl
  simpa [phase, neg_mul] using
    ((tendsto_const_nhds.mul hrow).sub (tendsto_const_nhds.mul (hm.sub hrow)) :
      Tendsto (fun x => phase n d r (Real.exp x)) atBot
        (𝓝 ((n : ℝ) * 0 - (((d : ℝ) - 1) / 2) * (angle d - 0))))

def reverseRaySum (d r : ℕ) (w : ℕ → ℝ) (v : ℝ) : ℂ :=
  ∑ s ∈ range (r + 1), ((w s * v ^ (r - s) : ℝ) : ℂ) * direction d s

theorem continuous_reverseRaySum (d r : ℕ) (w : ℕ → ℝ) :
    Continuous (reverseRaySum d r w) := by
  unfold reverseRaySum
  fun_prop

theorem reverseRaySum_zero (d r : ℕ) (w : ℕ → ℝ) :
    reverseRaySum d r w 0 = (w r : ℂ) * direction d r := by
  rw [reverseRaySum, Finset.sum_range_succ]
  have hz : (∑ s ∈ range r, ((w s * (0 : ℝ) ^ (r - s) : ℝ) : ℂ) * direction d s) = 0 := by
    apply Finset.sum_eq_zero
    intro s hs
    simp [zero_pow (Nat.sub_ne_zero_of_lt (Finset.mem_range.mp hs))]
  simp only [hz, Nat.sub_self, pow_zero, mul_one, zero_add]

theorem raySum_eq_mul_reverse {v : ℝ} (hv : 0 < v) (d r : ℕ) (w : ℕ → ℝ) :
    raySum d r w v = ((v ^ r : ℝ) : ℂ) * reverseRaySum d r w v⁻¹ := by
  rw [raySum, reverseRaySum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have hs' : s ≤ r := Nat.le_of_lt_succ (Finset.mem_range.mp hs)
  have heq : v ^ r * v⁻¹ ^ (r - s) = v ^ s := by
    rw [← pow_sub_mul_pow v hs', inv_pow, ← div_eq_mul_inv]
    exact mul_div_cancel_left₀ _ (pow_ne_zero _ hv.ne')
  rw [← mul_assoc, ← Complex.ofReal_mul, mul_left_comm, heq]

theorem tendsto_raySum_arg_atTop {d r : ℕ} {w : ℕ → ℝ}
    (hr : 0 < r) (hrd : r < d) (hw : 0 < w r) :
    Tendsto (fun x => (raySum d r w (Real.exp x)).arg) atTop (𝓝 (r * angle d)) := by
  have hslit : reverseRaySum d r w 0 ∈ Complex.slitPlane := by
    rw [reverseRaySum_zero, Complex.mem_slitPlane_iff]
    right
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, add_zero]
    exact (mul_pos hw (direction_im_pos hr hrd)).ne'
  have harg : (reverseRaySum d r w 0).arg = r * angle d := by
    rw [reverseRaySum_zero, Complex.arg_real_mul _ hw, direction_arg (hr.trans hrd) hrd]
  have hlim := (Complex.continuousAt_arg hslit).tendsto.comp
    ((continuous_reverseRaySum d r w).continuousAt.tendsto.comp
      Real.tendsto_exp_neg_atTop_nhds_zero)
  rw [harg] at hlim
  refine hlim.congr (fun x => ?_)
  change (reverseRaySum d r w (Real.exp (-x))).arg = _
  rw [raySum_eq_mul_reverse (Real.exp_pos x), Complex.arg_real_mul _ (pow_pos (Real.exp_pos x) _),
    Real.exp_neg]

theorem tendsto_phase_atTop (n : ℕ) {d r : ℕ} (hr : 1 ≤ r) (hrd : r < d) :
    Tendsto (fun x => phase n d r (Real.exp x)) atTop (𝓝 (((n : ℝ) * r / d) * Real.pi)) := by
  have hrow : 0 < rowWeight d r := by
    unfold rowWeight
    exact_mod_cast Nat.choose_pos hrd.le
  have hmoment : 0 < momentWeight d r := by
    unfold momentWeight
    have hr' : 0 < r := hr
    have hd' : 0 < d - r := Nat.sub_pos_of_lt hrd
    positivity
  have hrowLim := tendsto_raySum_arg_atTop (w := rowWeight d) hr hrd hrow
  have hmomentLim := tendsto_raySum_arg_atTop (w := momentWeight d) hr hrd hmoment
  have hlim : Tendsto (fun x => phase n d r (Real.exp x)) atTop
      (𝓝 ((n : ℝ) * (r * angle d) - (((d : ℝ) - 1) / 2) * (r * angle d - r * angle d))) :=
    (tendsto_const_nhds.mul hrowLim).sub (tendsto_const_nhds.mul (hmomentLim.sub hrowLim))
  have heq : (n : ℝ) * (r * angle d) - (((d : ℝ) - 1) / 2) *
      (r * angle d - r * angle d) = ((n : ℝ) * r / d) * Real.pi := by
    simp only [sub_self, mul_zero, sub_zero, angle]
    ring
  rwa [heq] at hlim

/-- The actual phase reaches every required internal level at an ordered
least positive radius. -/
theorem exists_phase_radii (n : ℕ) {d r : ℕ} (hr : 1 ≤ r) (hrd : r < d) :
    ∃ radius : {k : ℕ // 1 ≤ k ∧ k < n * r / d} → ℝ,
      StrictMono radius ∧ (∀ k, 0 < radius k) ∧
        ∀ k, IsLeast {v | 0 < v ∧ phase n d r v = (k.val : ℝ) * Real.pi} (radius k) :=
  BalancedEventual.exists_balanced_phase_radii n d r (by omega)
    (continuous_logRadius_phase n hr hrd) (tendsto_phase_atBot n hr hrd)
    (tendsto_phase_atTop n hr hrd)

/-- The expanded ray sum is the finite polynomial evaluated on the ray. -/
theorem raySum_eq_polynomial_on_ray (d r : ℕ) (w : ℕ → ℝ) (v : ℝ) :
    raySum d r w v =
      ∑ s ∈ range (r + 1), (w s : ℂ) * ((v : ℂ) * direction d 1) ^ s := by
  unfold raySum
  apply Finset.sum_congr rfl
  intro s _
  have hdir : direction d s = direction d 1 ^ s := by
    rw [direction, direction, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hdir, mul_pow, Complex.ofReal_mul, Complex.ofReal_pow, mul_assoc]

/-- Both sums lie above the real axis. Their difference of arguments stays in
the principal interval and therefore equals the argument of their quotient. -/
theorem arg_moment_div_row {d r : ℕ} {v : ℝ}
    (hr : 1 ≤ r) (hrd : r < d) (hv : 0 < v) :
    (momentSum d r v / rowSum d r v).arg =
      (momentSum d r v).arg - (rowSum d r v).arg := by
  let X := momentSum d r v
  let Y := rowSum d r v
  have hx : 0 < X.im := momentSum_im_pos hr hrd hv
  have hy : 0 < Y.im := rowSum_im_pos hr hrd hv
  have hx0 : X ≠ 0 := by intro h; simp [h] at hx
  have hy0 : Y ≠ 0 := by intro h; simp [h] at hy
  have hxlo : 0 ≤ X.arg := Complex.arg_nonneg_iff.mpr hx.le
  have hylo : 0 ≤ Y.arg := Complex.arg_nonneg_iff.mpr hy.le
  have hxhi : X.arg < Real.pi := Complex.arg_lt_pi_iff.mpr (Or.inr hx.ne')
  have hyhi : Y.arg < Real.pi := Complex.arg_lt_pi_iff.mpr (Or.inr hy.ne')
  have hinv : Y⁻¹.arg = -Y.arg := by rw [Complex.arg_inv, if_neg hyhi.ne]
  have hsum : X.arg + Y⁻¹.arg ∈ Set.Ioc (-Real.pi) Real.pi := by
    rw [hinv]
    exact ⟨by linarith, by linarith⟩
  change (X / Y).arg = X.arg - Y.arg
  rw [div_eq_mul_inv, Complex.arg_mul hx0 (inv_ne_zero hy0) hsum, hinv, sub_eq_add_neg]

#print axioms raySum_eq_polynomial_on_ray
#print axioms arg_moment_div_row
#print axioms exists_phase_radii
#print axioms tendsto_phase_atTop
#print axioms tendsto_phase_atBot
#print axioms momentSum_eq_mul_shift
#print axioms rowSum_im_pos
#print axioms momentSum_im_pos
#print axioms continuous_logRadius_phase

end

end BalancedEventual.OccupiedPhase
