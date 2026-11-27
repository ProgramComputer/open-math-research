import RepositoryCoherentPoles
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

noncomputable section
open Finset
open scoped Real
namespace RepositoryQuotientAudit

theorem coherentPole_conj (x : ℝ) (l : ℤ) :
    coherentPole x (-(l+1)) = (starRingEnd ℂ) (coherentPole x l) := by
  unfold coherentPole
  push_cast
  rw [map_add, map_mul, map_mul, Complex.conj_I, Complex.conj_ofReal]
  simp [map_ofNat]
  ring

private theorem coherentPole_re (x : ℝ) (l : ℤ) : (coherentPole x l).re = x := by
  simp [coherentPole, Complex.add_re, Complex.mul_I_re, Complex.mul_im, Complex.add_im]

theorem coherentPole_im (x : ℝ) (l : ℤ) :
    (coherentPole x l).im = (2*(l:ℝ)+1)*π := by
  simp [coherentPole, Complex.add_im, Complex.mul_I_im, Complex.mul_re, Complex.add_re]

theorem coherentPole_near_pos (x : ℝ) : 0 < ‖coherentPole x 0‖ := by
  apply (mul_pos (by norm_num : (0:ℝ)<1) Real.pi_pos).trans_le
  have h := Complex.abs_im_le_norm (coherentPole x 0)
  rw [coherentPole_im] at h
  simpa [abs_of_pos Real.pi_pos] using h

theorem coherentPole_near_le (x : ℝ) (l : ℤ) : ‖coherentPole x 0‖ ≤ ‖coherentPole x l‖ := by
  have hh : 1 ≤ |2*(l:ℝ)+1| := by
    by_cases h : 0 ≤ l
    · have h' : 0 ≤ (l:ℝ) := by exact_mod_cast h
      rw [abs_of_nonneg (by linarith)]
      linarith
    · have h' : (l:ℝ) ≤ -1 := by exact_mod_cast (show l ≤ -1 by omega)
      rw [abs_of_nonpos (by linarith)]
      linarith
  have hq : (1:ℝ)^2 ≤ (2*(l:ℝ)+1)^2 := by
    rw [← sq_abs (2*(l:ℝ)+1)]
    exact pow_le_pow_left₀ (by norm_num) hh 2
  apply le_of_sq_le_sq _ (norm_nonneg _)
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply,
    coherentPole_re, coherentPole_re, coherentPole_im, coherentPole_im]
  push_cast
  nlinarith [mul_le_mul_of_nonneg_right hq (sq_nonneg Real.pi)]

theorem coherentPole_far_lower (x : ℝ) (j : ℕ) :
    (2*(j:ℝ)+3)*π ≤ ‖coherentPole x ((j+1:ℕ):ℤ)‖ := by
  have h := Complex.abs_im_le_norm (coherentPole x ((j+1:ℕ):ℤ))
  rw [coherentPole_im] at h
  push_cast at h
  rw [abs_of_nonneg (by positivity)] at h
  convert h using 1 <;> ring



def oddSquareMajorant (j : ℕ) : ℝ := 4 / (2 * (j:ℝ) + 3)^2

private theorem oddSquareMajorant_le (j : ℕ) :
    oddSquareMajorant j ≤ 1 / ((j:ℝ)+1) - 1 / ((j:ℝ)+2) := by
  have h₁ : 0 < (j:ℝ)+1 := by positivity
  have h₂ : 0 < (j:ℝ)+2 := by positivity
  have h₃ : 0 < (2 * (j:ℝ) + 3)^2 := by positivity
  rw [oddSquareMajorant, div_sub_div _ _ h₁.ne' h₂.ne']
  apply (div_le_div_iff₀ h₃ (mul_pos h₁ h₂)).2
  ring_nf
  nlinarith

private theorem oddSquarePartial (n : ℕ) :
    ∑ j ∈ range n, oddSquareMajorant j ≤ 1 - 1 / ((n:ℝ)+1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, Nat.cast_succ]
    rw [show (n:ℝ)+1+1 = (n:ℝ)+2 by ring]
    linarith [oddSquareMajorant_le n]

theorem oddSquareSummable :
    Summable oddSquareMajorant := by
  apply summable_of_sum_range_le (c := 1) (fun j => by unfold oddSquareMajorant; positivity)
  intro n
  exact (oddSquarePartial n).trans (by linarith [show 0 ≤ 1 / ((n:ℝ)+1) by positivity])

theorem oddSquareSum_le_one :
    ∑' j, oddSquareMajorant j ≤ 1 := by
  apply Real.tsum_le_of_sum_range_le (fun j => by unfold oddSquareMajorant; positivity)
  intro n
  exact (oddSquarePartial n).trans (by linarith [show 0 ≤ 1 / ((n:ℝ)+1) by positivity])



/-- For an odd pole farther than the nearest conjugate pair, the high-angle
hypothesis makes both the squared envelope and the contour gap uniform. -/
theorem high_angle_far_pole_geometry {r W k p : ℝ}
    (hr : 0 < r) (hk : 7 ≤ k) (hp : 3 ≤ p)
    (hangle : r ≤ 2*Real.pi) (hW : p*Real.pi ≤ W) :
    (r/W)^2 ≤ 4/p^2 ∧ r*(1+1/k)/W ≤ 16/21 := by
  have hp0 : 0 < p := by linarith
  have hk0 : 0 < k := by linarith
  have hW0 : 0 < W := (mul_pos hp0 Real.pi_pos).trans_le hW
  have hratio : r/W ≤ 2/p := by
    apply (div_le_div_iff₀ hW0 hp0).2
    linarith [mul_le_mul_of_nonneg_right hangle hp0.le, mul_le_mul_of_nonneg_left hW (by norm_num : (0:ℝ) ≤ 2)]
  have hl : 1/k ≤ 1/7 := one_div_le_one_div_of_le (by norm_num) hk
  constructor
  · calc
      (r/W)^2 ≤ (2/p)^2 := pow_le_pow_left₀ (div_nonneg hr.le hW0.le) hratio _
      _ = _ := by rw [div_pow]; norm_num
  · rw [mul_comm r, mul_div_assoc]
    calc
      (1+1/k)*(r/W) ≤ (1+1/7)*(2/p) := by
        apply mul_le_mul (by linarith) hratio (div_nonneg hr.le hW0.le) (by norm_num)
      _ ≤ 16/21 := by
        have hthird : 1/p ≤ 1/3 := one_div_le_one_div_of_le (by norm_num) hp
        rw [show 2/p = 2*(1/p) by ring]
        linarith

theorem conjugate_lattice_real (u : ℤ → ℂ)
    (hu : Summable fun j : ℕ => ‖u (j:ℤ)‖)
    (hconj : ∀ j : ℤ, u (-(j+1)) = (starRingEnd ℂ) (u j)) :
    (∑' l : ℤ, u l).re = 2*(u 0).re + 2*(∑' j : ℕ, u ((j+1:ℕ):ℤ)).re := by
  have hneg : Summable (fun j : ℕ => u (-((j:ℤ)+1))) := by
    apply Summable.of_norm
    simpa only [hconj, Complex.norm_conj] using hu
  rw [tsum_of_nat_of_neg_add_one hu.of_norm hneg, Complex.add_re]
  have he : (∑' j : ℕ, u (-((j:ℤ)+1))) =
      (starRingEnd ℂ) (∑' j : ℕ, u (j:ℤ)) := by
    simp_rw [hconj]
    exact (Complex.conjCLE.toContinuousLinearMap.map_tsum hu.of_norm).symm
  rw [he, Complex.conj_re, hu.of_norm.tsum_eq_zero_add, Complex.add_re]
  norm_num
  ring


private theorem scaledPoleNorm (x : ℝ) (l : ℤ) (d : ℕ) :
    ‖((‖coherentPole x 0‖ : ℝ) : ℂ)^d * (1/coherentPole x l^d)‖ =
      (‖coherentPole x 0‖/‖coherentPole x l‖)^d := by
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
    norm_div, norm_one, norm_pow, div_pow, mul_one_div]

theorem scaledPoleSum_re_bound (x : ℝ) (d : ℕ) (hd : 2 ≤ d)
    (hx : ‖coherentPole x 0‖ ≤ 2*π) :
    |((∑' l : ℤ, (1:ℂ)/coherentPole x l^d).re * ‖coherentPole x 0‖^d)| ≤ 4 := by
  let r := ‖coherentPole x 0‖
  let u (l : ℤ) := (r:ℂ)^d * (1/coherentPole x l^d)
  have hr : 0 < r := coherentPole_near_pos x
  have hnear : ‖u 0‖ = 1 := by
    dsimp only [u]
    rw [scaledPoleNorm, div_self hr.ne', one_pow]
  have hfar (i : ℕ) : ‖u ((i+1:ℕ):ℤ)‖ ≤ oddSquareMajorant i := by
    let W := ‖coherentPole x ((i+1:ℕ):ℤ)‖
    have hW := coherentPole_near_le x ((i+1:ℕ):ℤ)
    have hgeo := (high_angle_far_pole_geometry hr (by norm_num : (7:ℝ)≤7)
      (by linarith [Nat.cast_nonneg (α := ℝ) i] : (3:ℝ)≤2*(i:ℝ)+3) hx (coherentPole_far_lower x i)).1
    dsimp only [u]
    rw [scaledPoleNorm]
    exact (pow_le_pow_of_le_one (div_nonneg hr.le (norm_nonneg _))
      ((div_le_one (hr.trans_le hW)).2 hW) hd).trans hgeo
  have hf : Summable (fun i : ℕ => ‖u ((i+1:ℕ):ℤ)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hfar oddSquareSummable
  have hs : Summable (fun i : ℕ => ‖u (i:ℤ)‖) := (summable_nat_add_iff 1).mp hf
  have hc : ∀ l : ℤ, u (-(l+1)) = (starRingEnd ℂ) (u l) := by
    intro l
    dsimp only [u]
    rw [coherentPole_conj]
    simp
  have he := conjugate_lattice_real u hs hc
  have hfar' : ‖∑' i : ℕ, u ((i+1:ℕ):ℤ)‖ ≤ 1 :=
    (norm_tsum_le_tsum_norm hf).trans ((hf.tsum_le_tsum hfar oddSquareSummable).trans oddSquareSum_le_one)
  have hnear' := Complex.abs_re_le_norm (u 0)
  rw [hnear] at hnear'
  have hfar'' := (Complex.abs_re_le_norm (∑' i : ℕ, u ((i+1:ℕ):ℤ))).trans hfar'
  have hsum : |(∑' l : ℤ, u l).re| ≤ 4 := by
    rw [he]
    have hnorm := abs_add_le (2*(u 0).re) (2*(∑' i : ℕ, u ((i+1:ℕ):ℤ)).re)
    simp only [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)] at hnorm
    linarith
  unfold u at hsum
  rw [tsum_mul_left, ← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, mul_comm] at hsum
  exact hsum

end RepositoryQuotientAudit
