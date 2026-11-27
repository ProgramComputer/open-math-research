import LowMomentMass
import RadiusGeometry

noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real Finset

theorem shifted_moment_input {d : ℕ} (hd : 2 ≤ d) {x : ℝ} (hx : 0 < x) (m : ℝ)
    (mom : m = ∑' h : ℕ, (-1:ℝ)^h * (h:ℝ)^(d-1) * exp (-(x*(h:ℝ)))) :
    m = ∑' i : ℕ, (-1:ℝ)^(i+1)*((i+1:ℕ):ℝ)^(d-1)*exp (-x*(i+1:ℕ)) := by
  let v (h : ℕ) := (-1:ℝ)^h * (h:ℝ)^(d-1) * exp (-(x*(h:ℝ)))
  have hs : Summable v := by
    apply Summable.of_norm
    have hn (h : ℕ) : ‖v h‖ = (h:ℝ)^(d-1)* exp (-x*(h:ℝ)) := by
      dsimp [v]
      simp only [abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul,
        abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) h),abs_of_nonneg (exp_pos _).le, neg_mul]
    simpa only [hn] using (Real.summable_pow_mul_exp_neg_nat_mul (d-1) hx)
  change m = ∑' h, v h at mom
  rw [mom,hs.tsum_eq_zero_add]
  have hzero : v 0 = 0 := by simp [v,zero_pow (show d-1 ≠ 0 by omega)]
  rw [hzero,zero_add]
  apply tsum_congr
  intro i
  simp only [v,neg_mul]

def lowCut (k : ℕ) (x : ℝ) := min (k-1) ⌊x^2/16⌋₊

theorem lowCut_scale (k : ℕ) (x : ℝ) : 16*(lowCut k x:ℝ) ≤ x^2 := by
  have hnat : lowCut k x ≤ ⌊x^2/16⌋₊ := min_le_right _ _
  have h : (lowCut k x:ℝ) ≤ (⌊x^2/16⌋₊:ℝ) := by exact_mod_cast hnat
  linarith [Nat.floor_le (show (0:ℝ) ≤ x^2/16 by positivity)]

theorem above_lowCut {d k : ℕ} {x : ℝ} (hd : d < k) (hcut : lowCut k x < d) :
    x^2/16 < (d:ℝ) := by
  apply Nat.lt_of_floor_lt
  dsimp [lowCut] at hcut
  omega

#print axioms shifted_moment_input
#print axioms lowCut_scale
end OpenMathResearch.LongCycleExcedances
