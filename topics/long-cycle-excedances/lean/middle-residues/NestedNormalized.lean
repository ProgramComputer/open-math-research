import NestedSize
import Mathlib.Analysis.Real.Pi.Bounds

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real

theorem normalized_nested_budget {q n k : ℕ} (hn : 100 ≤ n) (hk : 7 ≤ k)
    (hkn : k ≤ n) (hnq : n ≤ q) {r U : ℝ} (hr : 0 < r)
    (hm : 1 ≤ (n:ℝ)*(π/r)^2) (hamp : exp (-(6+9*log (k:ℝ))) ≤ U)
    (hsize : 30*log (n:ℝ)+20 < (n:ℝ)/(200*(k:ℝ))) :
    let A := exp (6+9*log (k:ℝ))
    let ρ := (1+1/(100*(k:ℝ)))⁻¹
    let σ := (1+1/(50*(k:ℝ)))⁻¹
    (((200*k+3:ℝ)*A*ρ^(q-1)*(2+(n:ℝ)/2)+r*A*σ^q)/2)/U ≤ 1/(100*(n:ℝ)) := by
  let A := exp (6+9*log (k:ℝ))
  let ρ := (1+1/(100*(k:ℝ)))⁻¹
  let σ := (1+1/(50*(k:ℝ)))⁻¹
  have hn' : (100:ℝ) ≤ n := by exact_mod_cast hn
  have hk' : (7:ℝ) ≤ k := by exact_mod_cast hk
  have hkn' : (k:ℝ) ≤ n := by exact_mod_cast hkn
  have hnpos : 0 < (n:ℝ) := by linarith
  have hkpos : 0 < (k:ℝ) := by linarith
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hσ : 0 < σ := by dsimp [σ]; positivity
  have hρle : ρ ≤ 1 := inv_le_one_of_one_le₀ (le_add_of_nonneg_right (by positivity : 0 ≤ 1/(100*(k:ℝ))))
  have hσρ : σ ≤ ρ := by
    apply inv_anti₀ (by positivity)
    apply add_le_add (le_refl 1)
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hq : σ^q ≤ ρ^(q-1) :=
    (pow_le_pow_left₀ hσ.le hσρ q).trans (pow_le_pow_of_le_one hρ.le hρle (by omega))
  have hπ : π^2 ≤ 16 := (pow_le_pow_left₀ pi_pos.le pi_lt_four.le 2).trans (by norm_num)
  have hr2 : r^2 ≤ (n:ℝ)*π^2 := by
    rw [div_pow,←mul_div_assoc,le_div_iff₀ (sq_pos_of_pos hr)] at hm
    simpa only [one_mul] using hm
  have hrn : r ≤ 4*(n:ℝ) := by
    apply le_of_sq_le_sq _ (by positivity)
    nlinarith only [hr2,mul_le_mul_of_nonneg_left hπ hnpos.le,
      mul_nonneg (show 0 ≤ (n:ℝ)-1 by linarith) hnpos.le]
  have hc : (200*(k:ℝ)+3)*(2+(n:ℝ)/2)+r ≤ 400*(n:ℝ)^2 := by
    have h₁ : (200*(k:ℝ)+3) ≤ 201*n := by linarith
    have h₂ : 2+(n:ℝ)/2 ≤ n := by linarith
    nlinarith only [mul_le_mul h₁ h₂ (by positivity) (by positivity),hrn,
      mul_nonneg (show 0 ≤ (n:ℝ)-1 by linarith) hnpos.le]
  have hA : 0 < A := exp_pos _
  have hU : 0 < U := (exp_pos _).trans_le hamp
  have hinv : U⁻¹ ≤ A := by
    apply (inv_anti₀ (exp_pos _) hamp).trans_eq
    dsimp [A]; rw [exp_neg,inv_inv]
  have hraw : ((200*k+3:ℝ)*A*ρ^(q-1)*(2+(n:ℝ)/2)+r*A*σ^q)/2 ≤
      (400*(n:ℝ)^2)*(A*ρ^(q-1)) := by
    have ht := mul_le_mul_of_nonneg_left hq (mul_nonneg hr.le hA.le)
    have hc' := mul_le_mul_of_nonneg_right hc (mul_nonneg hA.le (pow_nonneg hρ.le (q-1)))
    have hz : 0 ≤ 400*(n:ℝ)^2*(A*ρ^(q-1)) := by positivity
    nlinarith only [ht,hc',hz]
  change _ / U ≤ _
  rw [div_eq_mul_inv]
  apply (mul_le_mul hraw hinv (inv_nonneg.mpr hU.le) (by positivity)).trans
  have HA : A*A = exp (2*(6+9*log (k:ℝ))) := by unfold A;rw [←exp_add,two_mul]
  calc
    _ = 400*(n:ℝ)^2*(A*A)*ρ^(q-1) := by ring
    _ ≤ _ := by rw [HA];exact nested_size_envelope hn hk hkn hnq hsize

#print axioms normalized_nested_budget
end OpenMathResearch.LongCycleExcedances
