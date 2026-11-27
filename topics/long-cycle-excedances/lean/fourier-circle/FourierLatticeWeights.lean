import FourierComplexPoleBound
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real Filter

/-- A cofinite comparison with a summable majorant. -/
theorem summable_of_cofinite_norm_le {ι E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {f : ι → E} {g : ι → ℝ} (hs : Summable g)
    (h : ∀ᶠ i in cofinite, ‖f i‖ ≤ g i) : Summable f := by
  first
  | exact Summable.of_norm_bounded_eventually g hs h
  | exact Summable.of_norm_bounded_eventually g h hs
  | exact Summable.of_norm_bounded_eventually hs h
  | exact Summable.of_norm_bounded_eventually h hs

theorem odd_lattice_height_one_le (l : ℤ) : 1 ≤ |2*(l:ℝ)+1| := by
  by_cases h : 0 ≤ l
  · apply le_abs.mpr (Or.inl ?_)
    have : 0 ≤ (l:ℝ) := by exact_mod_cast h
    linarith
  · apply le_abs.mpr (Or.inr ?_)
    have : (l:ℝ) ≤ -1 := by exact_mod_cast (show l ≤ -1 by omega)
    linarith

private theorem odd_height_norm (P : ℤ → ℂ) (hP : ∀ l, (P l).im=(2*(l:ℝ)+1)*π) (l : ℤ) :
    |2*(l:ℝ)+1| ≤ ‖P l‖ := by
  have h := Complex.abs_im_le_norm (P l)
  rw [hP,abs_mul,abs_of_pos Real.pi_pos] at h
  exact (le_mul_of_one_le_right (abs_nonneg _) (by linarith [Real.one_le_pi_div_two] : 1 ≤ π)).trans h

theorem lattice_inverse_summable (P : ℤ → ℂ) (hP : ∀ l, (P l).im=(2*(l:ℝ)+1)*π)
    {m : ℕ} (hm : 2 ≤ m) : Summable (fun l => 1/‖P l‖^m) := by
  have hs : Summable (fun l : ℤ => 1/|(l:ℝ)+1/2|^m) := by
    simpa using (Real.summable_one_div_int_add_rpow (1/2) (m:ℝ)).mpr (by exact_mod_cast (show 1<m by omega))
  apply Summable.of_nonneg_of_le (fun l => by positivity) _ hs
  intro l
  have he : |2*(l:ℝ)+1| = 2*|(l:ℝ)+1/2| := by rw [show 2*(l:ℝ)+1 = 2*((l:ℝ)+1/2) by ring,abs_mul]; norm_num
  have hh := odd_lattice_height_one_le l
  have hb := odd_height_norm P hP l
  rw [he] at hh hb
  apply one_div_le_one_div_of_le (pow_pos (by linarith) _)
  exact pow_le_pow_left₀ (abs_nonneg _) (by linarith) _

theorem lattice_eventually_far (P : ℤ → ℂ) (hP : ∀ l, (P l).im=(2*(l:ℝ)+1)*π)
    {R : ℝ} (hR : 0 < R) : ∀ᶠ l in cofinite, 2*R ≤ ‖P l‖ := by
  have ht := (lattice_inverse_summable P hP (m := 2) (by decide)).tendsto_cofinite_zero
  filter_upwards [ht.eventually_lt_const (by positivity : (0:ℝ) < 1/(2*R)^2)] with l hl
  by_contra! hn
  have hpos : 0 < ‖P l‖ := zero_lt_one.trans_le ((odd_lattice_height_one_le l).trans (odd_height_norm P hP l))
  have he := one_div_le_one_div_of_le (sq_pos_of_pos hpos) (sq_le_sq' (by linarith) hn.le)
  exact (not_lt_of_ge he) hl

/-- The first signed-lattice absolute weight is summable already at k = 3.
All but finitely many poles have an inverse gap factor at most 2 / ‖P l‖. -/
theorem lattice_moment_weights (P : ℤ → ℂ) (hP : ∀ l, (P l).im=(2*(l:ℝ)+1)*π)
    {R : ℝ} (hR : 0 < R) {k : ℕ} (hk : 3 ≤ k) :
    Summable (fun l => poleWeight ((R:ℂ)^k / (P l)^(k-1)) (P l) R) ∧
    Summable (fun l : ℤ => |2*(l:ℝ)+1| * poleWeight ((R:ℂ)^k / (P l)^(k-1)) (P l) R) := by
  let W := fun l => poleWeight ((R:ℂ)^k / (P l)^(k-1)) (P l) R
  have hw l : 0 ≤ W l := div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
  have hs := lattice_inverse_summable P hP (m:=k-1) (by omega)
  have hfirst : Summable (fun l : ℤ => |2*(l:ℝ)+1| * W l) := by
    apply summable_of_cofinite_norm_le (hs.mul_left (2*R^k))
    filter_upwards [lattice_eventually_far P hP hR] with l hl
    have hn : 0 < ‖P l‖ := by linarith
    have hg : 0 < ‖P l‖^2-R^2 := sub_pos.mpr (sq_lt_sq' (by linarith) (by linarith))
    have hroot : ‖P l‖/2 ≤ √(poleGap (P l) R) := by
      apply Real.le_sqrt_of_sq_le
      rw [poleGap,abs_of_pos hg]
      nlinarith [mul_nonneg (by linarith : 0 ≤ ‖P l‖-2*R) (by linarith : 0 ≤ ‖P l‖+2*R)]
    have hr : 0 < √(poleGap (P l) R) := by linarith
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (abs_nonneg _) (hw l))]
    dsimp only [W,poleWeight]
    rw [norm_div,norm_pow,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hR]
    have hfrac : |2*(l:ℝ)+1| / √(poleGap (P l) R) ≤ 2 := (div_le_iff₀ hr).mpr
      ((odd_height_norm P hP l).trans (by linarith))
    calc
      _ = (|2*(l:ℝ)+1| / √(poleGap (P l) R))*(R^k/‖P l‖^(k-1)) := by ring
      _ ≤ 2*(R^k/‖P l‖^(k-1)) := mul_le_mul_of_nonneg_right hfrac (by positivity)
      _ = _ := by ring
  exact ⟨Summable.of_nonneg_of_le hw (fun l => le_mul_of_one_le_left (hw l) (odd_lattice_height_one_le l)) hfirst,hfirst⟩

#print axioms lattice_inverse_summable
#print axioms lattice_eventually_far
#print axioms lattice_moment_weights
end OpenMathResearch.LongCycleExcedances
