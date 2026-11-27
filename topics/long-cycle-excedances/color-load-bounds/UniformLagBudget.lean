import SmallLagGrid
import SparseLagBudget
import Mathlib.Analysis.Real.Sqrt

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset Real

theorem front_grid_scale {n p : ℕ} (hn : 10000 ≤ n) (hrank : 4*p^2 ≤ n) :
    200*p ≤ n := by
  by_cases hp : 50 ≤ p
  · have hpp : (50:ℝ) ≤ p := by exact_mod_cast hp
    have hrank' : 4*(p:ℝ)^2 ≤ n := by exact_mod_cast hrank
    have h := mul_nonneg (show (0:ℝ) ≤ p by positivity) (sub_nonneg.mpr hpp)
    exact_mod_cast (show 200*(p:ℝ) ≤ n by nlinarith only [hrank', h])
  · omega

/-- The grid and old coefficient estimates imply the relative lag bound.
The mode-bound input is needed only for k at least 150. -/
theorem uniform_front_lag_budget {n k p : ℕ} {L α : ℝ} (hn : 10000 ≤ n)
    (hk : 8 ≤ k) (hsector : 4000*k < n) (hp : 0 < p) (hrank : 4*p^2 ≤ n)
    (hL : L ≤ ∑ j ∈ range (p+1), colorLoad n (k-1) ((j:ℝ)/p))
    (hlarge : 150 ≤ k → (∑ j ∈ range (p+1), colorLoad n (k-1) ((j:ℝ)/p)) ≤
       (p:ℝ)/((n:ℝ)+1)+1/√((k-1:ℕ):ℝ))
    (hα : (99:ℝ)/(100*(1+(8/3)*((k:ℝ)*p/n))) ≤ α) :
    L < α/8 := by
  have hs := front_grid_scale hn hrank
  have hns : 0 < n := by omega
  have hkn : k ≤ n := by omega
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr hns
  have hpR : (0:ℝ) < p := Nat.cast_pos.mpr hp
  have hsR : 200*(p:ℝ) ≤ n := by exact_mod_cast hs
  let x := (p:ℝ)/(n:ℝ)
  let a := (k:ℝ)*x
  have hx : 0 ≤ x := div_nonneg hpR.le hnR.le
  have hxsmall : x ≤ 1/200 := by
    apply (div_le_iff₀ hnR).mpr
    linarith only [hsR]
  have ha : 0 ≤ a := mul_nonneg (Nat.cast_nonneg k) hx
  have haeq : (k:ℝ)*p/n = a := mul_div_assoc _ _ _
  rw [haeq] at hα
  have hden : 0 < 100*(1+(8/3:ℝ)*a) := by positivity
  have hα' : 99/100 ≤ α*(1+(8/3:ℝ)*a) := by
    have h := (div_le_iff₀ hden).mp hα
    nlinarith only [h]
  by_cases hbig : 150 ≤ k
  · let M := 1/√((k-1:ℕ):ℝ)
    have hscale : (4000:ℝ)*k ≤ n := by exact_mod_cast hsector.le
    have hbigR : (150:ℝ) ≤ k := by exact_mod_cast hbig
    have hrankR : 4*(p:ℝ)^2 ≤ n := by exact_mod_cast hrank
    have hgrid : 4*(n:ℝ)*x^2 ≤ 1 := by
      have he : 4*(n:ℝ)*x^2 = 4*(p:ℝ)^2/(n:ℝ) := by
        dsimp [x]
        field_simp [hnR.ne'] <;> ring
      rw [he]
      exact (div_le_one hnR).mpr hrankR
    have hk1 : 1 ≤ k := by omega
    have hdNat : 0 < k-1 := by omega
    have hdR : (0:ℝ) < ((k-1:ℕ):ℝ) := Nat.cast_pos.mpr hdNat
    have hdS : 0 < √((k-1:ℕ):ℝ) := sqrt_pos.mpr hdR
    have hmode : ((k:ℝ)-1)*M^2 ≤ 1 := by
      have he : ((k:ℝ)-1)*M^2 = 1 := by
        dsimp [M]
        rw [div_pow, one_pow, sq_sqrt hdR.le]
        rw [Nat.cast_sub hk1, Nat.cast_one, mul_one_div, div_self]
        simpa only [Nat.cast_sub hk1, Nat.cast_one] using hdR.ne'
      exact he.le
    have hsmall : (p:ℝ)/((n:ℝ)+1) ≤ x :=
      div_le_div_of_nonneg_left hpR.le hnR (by linarith)
    have hLM : L ≤ x+M :=
      hL.trans ((hlarge hbig).trans (add_le_add_right hsmall _))
    apply sparse_lag_large_budget hbigR hscale hx hxsmall hgrid hmode hLM
    simpa only [a, mul_assoc] using hα'
  · have hkle : (k:ℝ) ≤ 150 := by exact_mod_cast (le_of_lt (not_le.mp hbig))
    have haSmall : a ≤ 3/4 := by
      dsimp only [a]
      have he := mul_le_mul hkle hxsmall (by exact hx) (by norm_num : (0:ℝ) ≤ 150)
      norm_num at he
      exact he
    have hgrid := small_lag_grid_mass hp (by omega : 2 ≤ k) hkn hs (haeq ▸ haSmall)
    exact sparse_lag_small_budget ha haSmall (hL.trans hgrid) hα'

#print axioms front_grid_scale
#print axioms uniform_front_lag_budget
end OpenMathResearch.LongCycleExcedances
