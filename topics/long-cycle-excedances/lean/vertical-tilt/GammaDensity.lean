import UnimodalMesh
import UniformDiscreteTilt
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Pow

noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real Finset Set

def poissonTerm (m : ℕ) (t : ℝ) := exp (-t)*t^m/(m.factorial:ℝ)
def poissonRemainder (m : ℕ) (t : ℝ) := 1 - exp (-t)*expPrefix m t

private theorem expPrefix_succ (m : ℕ) (t : ℝ) :
    expPrefix (m+1) t = expPrefix m t + t^(m+1)/(m+1).factorial := sum_range_succ _ _

private theorem poissonTerm_succ_deriv (m : ℕ) (t : ℝ) :
    HasDerivAt (poissonTerm (m+1))
      (poissonTerm m t-poissonTerm (m+1) t) t := by
  have he : HasDerivAt (fun y : ℝ => exp (-y)) (-exp (-t)) t := by
    simpa only [Function.comp_def, mul_neg, mul_one] using
      (Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_id t).neg
  have hd := ((he.mul ((hasDerivAt_id t).pow (m+1))).div_const ((m+1).factorial:ℝ))
  change HasDerivAt (poissonTerm (m+1))
    ((-exp (-t)*t^(m+1)+exp (-t)*((m+1:ℕ)*(t^(m+1-1))*1))/(m+1).factorial) t at hd
  convert hd using 1
  unfold poissonTerm
  rw [Nat.factorial_succ]
  push_cast
  simp only [Nat.add_sub_cancel, mul_one]
  field_simp <;> ring

private theorem poissonRemainder_deriv (m : ℕ) (t : ℝ) :
    HasDerivAt (poissonRemainder m) (poissonTerm m t) t := by
  induction m with
  | zero =>
    have he : HasDerivAt (fun y : ℝ => exp (-y)) (-exp (-t)) t := by
      simpa only [Function.comp_def, mul_neg, mul_one] using
        (Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_id t).neg
    have h0 : poissonRemainder 0 = (fun y : ℝ => 1-exp (-y)) := by
      funext y
      simp [poissonRemainder,expPrefix]
    rw [h0]
    have hh : HasDerivAt (fun y : ℝ => 1-exp (-y)) (0- -exp (-t)) t := (hasDerivAt_const t (1:ℝ)).sub he
    simpa only [poissonTerm,pow_zero,mul_one,Nat.factorial_zero,Nat.cast_one,div_one,sub_neg_eq_add,zero_add] using hh
  | succ m ih =>
    have h := ih.sub (poissonTerm_succ_deriv m t)
    have he : poissonRemainder (m+1) = poissonRemainder m - poissonTerm (m+1) := by
      funext y
      simp only [Pi.sub_apply]
      unfold poissonRemainder poissonTerm
      rw [expPrefix_succ]
      ring
    rw [he]
    simpa only [sub_sub_cancel] using h

theorem gamma_mesh_peak {m : ℕ} (hm : 1 ≤ m) {x : ℝ} (hx : 0 < x) :
    (∑' i : ℕ, poissonTerm m (x*(i+1:ℕ))) ≤ 1/x+poissonTerm m m := by
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (show m≠0 by omega)
  have hd (t : ℝ) := poissonTerm_succ_deriv k t
  have hf (t : ℝ) (ht : 0 ≤ t) : poissonTerm k t-poissonTerm (k+1) t =
      exp (-t)*t^k/((k+1).factorial:ℝ)*((k+1:ℕ)-t) := by
    unfold poissonTerm
    rw [Nat.factorial_succ,pow_succ]
    push_cast
    field_simp <;> ring
  rw [hk]
  apply unimodal_density_mesh (F := poissonRemainder (k+1)) (m := (k+1:ℕ))
    (by positivity) hx
  · intro t ht; unfold poissonTerm; positivity
  · apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · intro t _
      exact (hd t).continuousAt.continuousWithinAt
    · exact fun t _ => (hd t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have ht0 : 0 ≤ t := ht.1.le
      rw [(hd t).deriv,hf t ht0]
      exact mul_nonneg (by positivity) (sub_nonneg.mpr ht.2.le)
  · apply antitoneOn_of_deriv_nonpos (convex_Ici _)
    · intro t _
      exact (hd t).continuousAt.continuousWithinAt
    · exact fun t _ => (hd t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      have ht' : 0 ≤ t := (Nat.cast_nonneg (k+1)).trans ht.le
      rw [(hd t).deriv,hf t ht']
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr ht.le)
  · exact le_rfl
  · intro t _
    exact poissonRemainder_deriv (k+1) t
  · intro t ht
    have h0 (d : ℕ) : expPrefix d 0 = 1 := by
      induction d with
      | zero => simp [expPrefix]
      | succ d ih => rw [expPrefix_succ,ih]; simp
    unfold poissonRemainder
    simp only [neg_zero,exp_zero,one_mul,h0,sub_self,sub_zero,sub_le_self_iff]
    exact mul_nonneg (exp_pos _).le (expPrefix_nonneg _ ht)

#print axioms gamma_mesh_peak
end OpenMathResearch.LongCycleExcedances
