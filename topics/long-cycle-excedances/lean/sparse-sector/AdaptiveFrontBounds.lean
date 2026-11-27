import FrontModulusJoin
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real Finset

/-- Algebraic ratio bound from the two normalized old-row coefficient envelopes. -/
theorem exterior_alpha_ratio {x r α β : ℝ} (hx : 0 < x) (hr : 0 ≤ r)
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (hαx : α ≤ 151/(100*x))
    (hβ : 99/(100*(1+(8/3:ℝ)*r*x)) ≤ β) :
    0 < β ∧ α/β ≤ (51/10:ℝ)*max 1 r := by
  let m := max 1 r
  have hm : 1 ≤ m := le_max_left _ _
  have hrm : r ≤ m := le_max_right _ _
  have hd : 0 < 100*(1+(8/3:ℝ)*r*x) := by positivity
  have hβ₀ := (div_pos (by norm_num) hd).trans_le hβ
  have hB := (div_le_iff₀ hd).mp hβ
  have hA := (le_div_iff₀ (by positivity : 0 < 100*x)).mp hαx
  have hAR := mul_le_mul_of_nonneg_left hA hr
  have hsum : (1+(8/3:ℝ)*r*x)*α ≤ (1+(8/3:ℝ)*(151/100))*m := by
    nlinarith only [hα1,hm,hAR,hrm]
  constructor
  · exact hβ₀
  · apply (div_le_iff₀ hβ₀).mpr
    have h₁ := mul_le_mul_of_nonneg_right hB hα
    have h₂ := mul_le_mul_of_nonneg_right hsum hβ₀.le
    have h₃ : (1+(8/3:ℝ)*(151/100))*m*β ≤ (99/100:ℝ)*((51/10)*m*β) := by
      nlinarith only [mul_nonneg (show 0 ≤ m by linarith only [hm]) hβ₀.le]
    nlinarith only [h₁,h₂,h₃]

/-- The common inverse adjacent growth of the two bare power scales. -/
def frontInverseGrowth (n h : ℕ) : ℝ := (1-1/((h:ℝ)+1)^2)^n

theorem front_inverse_growth_pos (n : ℕ) {h : ℕ} (hh : 0 < h) :
    0 < frontInverseGrowth n h := by
  have hh' : (1:ℝ) ≤ h := by exact_mod_cast hh
  have hs : (1:ℝ) < ((h:ℝ)+1)^2 := by nlinarith only [hh', sq_nonneg (h:ℝ)]
  unfold frontInverseGrowth
  exact pow_pos (sub_pos.mpr ((div_lt_one (by positivity)).mpr hs)) _

private theorem front_growth_exponential (n : ℕ) {h : ℕ} (hh : 0 < h) :
    frontInverseGrowth n h ≤ exp (-((n:ℝ)/((h:ℝ)+1)^2)) := by
  let v : ℝ := 1/((h:ℝ)+1)^2
  have hh' : (1:ℝ) ≤ h := by exact_mod_cast hh
  have hv : v ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    nlinarith only [hh', sq_nonneg (h:ℝ)]
  have hexp := add_one_le_exp (-v)
  unfold frontInverseGrowth
  calc
    _ ≤ (exp (-v))^n := pow_le_pow_left₀ (sub_nonneg.mpr hv) (by linarith only [hexp]) n
    _ = _ := by
      have he : (n:ℝ)*(-v) = -((n:ℝ)/((h:ℝ)+1)^2) := by dsimp [v]; ring
      rw [←exp_nat_mul, he]

private theorem front_exp_625_over_81 : (2200:ℝ) < exp (625/81) := by
  have h1 : (2718/1000:ℝ) ≤ exp 1 := by linarith only [exp_one_gt_d9]
  have hx : 0 ≤ (58/81:ℝ) := by norm_num
  have hT := sum_le_exp_of_nonneg hx 4
  norm_num [sum_range_succ, Nat.factorial] at hT
  have hh := mul_le_mul (pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2718/1000) h1 7)
    hT (by norm_num) (by positivity)
  have he : exp (625/81:ℝ) = exp 1^7*exp (58/81) := by
    rw [←exp_nat_mul,←exp_add]
    congr 1
    norm_num
  rw [he]
  exact (by norm_num : (2200:ℝ) < (2718/1000)^7 *
    ((58/81)^3/6+((58/81)^2/2+((58/81)+1)))).trans_le (by norm_num at hh ⊢; exact hh)

private theorem front_exp_nine : (4000:ℝ) < exp 9 := by
  have h1 : (27/10:ℝ) ≤ exp 1 := by linarith only [exp_one_gt_d9]
  have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 27/10) h1 9
  rw [←exp_nat_mul] at h
  exact (by norm_num : (4000:ℝ) < (27/10)^9).trans_le (by simpa using h)

theorem front_inverse_growth_bound {n h : ℕ} (hn : 10000 ≤ n)
    (hh : 0 < h) (hH : h ≤ ⌊(7/20:ℝ)*sqrt (n:ℝ)⌋₊) :
    frontInverseGrowth n h ≤ 1/2200 := by
  obtain ⟨_,hb⟩ := exterior_floor_budget hn
  let H : ℕ := ⌊(7/20:ℝ)*sqrt (n:ℝ)⌋₊
  have hcast : (h:ℝ) ≤ H := by exact_mod_cast hH
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ (h:ℝ)+1) (add_le_add hcast (le_refl (1:ℝ))) 2
  have ht : ((h:ℝ)+1)^2 ≤ (9/25:ℝ)^2*n := hs.trans hb
  have harg : (625/81:ℝ) ≤ (n:ℝ)/((h:ℝ)+1)^2 := by
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith only [ht]
  apply (front_growth_exponential n hh).trans
  rw [exp_neg, one_div]
  exact (inv_le_inv₀ (exp_pos _) (by norm_num : (0:ℝ) < 2200)).mpr
    (front_exp_625_over_81.le.trans (exp_le_exp.mpr harg))

theorem front_inverse_growth_small_rank {n h : ℕ} (hn : 10000 ≤ n)
    (hh : 0 < h) (h5 : h ≤ 5) :
    frontInverseGrowth n h ≤ 1/4000 := by
  have hn' : (10000:ℝ) ≤ n := by exact_mod_cast hn
  have hh' : (h:ℝ) ≤ 5 := by exact_mod_cast h5
  have hs : ((h:ℝ)+1)^2 ≤ 6^2 :=
    pow_le_pow_left₀ (by positivity) (by linarith only [hh']) 2
  have hv : (9:ℝ) ≤ (n:ℝ)/((h:ℝ)+1)^2 := by
    apply (le_div_iff₀ (by positivity)).mpr
    linarith only [hs,hn']
  apply (front_growth_exponential n hh).trans
  rw [exp_neg, one_div]
  exact (inv_le_inv₀ (exp_pos _) (by norm_num : (0:ℝ) < 4000)).mpr
    (front_exp_nine.le.trans (exp_le_exp.mpr hv))

/-- The left power ratio, before multiplying by the adaptive coefficient ratio. -/
theorem front_left_bare_ratio {h j : ℕ} (hh : 0 < h) (hj : j ≤ h) :
    ((j:ℝ)/h)*(((h:ℝ)+1)/h)^(h-j) ≤ (1-1/((h:ℝ)+1)^2)^(h-j) := by
  have hh' : (1:ℝ) ≤ h := by exact_mod_cast hh
  have hp : (0:ℝ) < h := by positivity
  have hi : 1/(h:ℝ) ≤ 1 := (div_le_one hp).mpr hh'
  have hB := one_add_mul_le_pow (show (-2:ℝ) ≤ -(1/(h:ℝ)) by linarith only [hi]) (h-j)
  have he : (j:ℝ)/h = 1+((h-j:ℕ):ℝ)*(-(1/(h:ℝ))) := by
    rw [Nat.cast_sub hj]
    field_simp [hp.ne'] <;> ring
  have hbase : (1+ -(1/(h:ℝ)))*(((h:ℝ)+1)/h) = 1-1/(h:ℝ)^2 := by
    field_simp [hp.ne'] <;> ring
  have hs : (1:ℝ) ≤ (h:ℝ)^2 := by
    simpa only [one_pow] using pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hh' 2
  have hq : 1-1/(h:ℝ)^2 ≤ 1-1/((h:ℝ)+1)^2 := by
    have hh2 : (h:ℝ)^2 ≤ ((h:ℝ)+1)^2 := pow_le_pow_left₀ hp.le (by linarith) 2
    have hrecip := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1) (by positivity) hh2
    linarith only [hrecip]
  rw [he]
  calc
    _ ≤ (1+ -(1/(h:ℝ)))^(h-j) * (((h:ℝ)+1)/h)^(h-j) :=
      mul_le_mul_of_nonneg_right hB (by positivity)
    _ = (1-1/(h:ℝ)^2)^(h-j) := by rw [←mul_pow,hbase]
    _ ≤ _ := pow_le_pow_left₀ (sub_nonneg.mpr ((div_le_one (by positivity)).mpr hs)) hq _

/-- The right power ratio uses the same inverse adjacent growth. -/
theorem front_right_bare_ratio {h j : ℕ} (hj : h+1 ≤ j) :
    ((j:ℝ)/((h:ℝ)+1))*((h:ℝ)/((h:ℝ)+1))^(j-(h+1)) ≤
      (1-1/((h:ℝ)+1)^2)^(j-(h+1)) := by
  let H : ℝ := (h:ℝ)+1
  have hH : 0 < H := by dsimp [H]; positivity
  have hB := one_add_mul_le_pow (show (-2:ℝ) ≤ 1/H by linarith only [show 0 ≤ 1/H by positivity]) (j-(h+1))
  have he : (j:ℝ)/H = 1+((j-(h+1):ℕ):ℝ)*(1/H) := by
    rw [Nat.cast_sub hj, Nat.cast_add, Nat.cast_one]
    change _ = 1+((j:ℝ)-H)*(1/H)
    field_simp [hH.ne'] <;> ring
  have hbase : (1+1/H)*((h:ℝ)/H) = 1-1/H^2 := by
    dsimp only [H]
    have hHp : (h:ℝ)+1 ≠ 0 := by positivity
    field_simp [hHp] <;> ring
  change ((j:ℝ)/H)*((h:ℝ)/H)^(j-(h+1)) ≤ (1-1/H^2)^(j-(h+1))
  rw [he]
  calc
    _ ≤ (1+1/H)^(j-(h+1))*((h:ℝ)/H)^(j-(h+1)) :=
      mul_le_mul_of_nonneg_right hB (by positivity)
    _ = _ := by rw [←mul_pow,hbase]

#print axioms exterior_alpha_ratio
#print axioms front_inverse_growth_bound
#print axioms front_inverse_growth_small_rank
#print axioms front_left_bare_ratio
#print axioms front_right_bare_ratio
end OpenMathResearch.LongCycleExcedances
