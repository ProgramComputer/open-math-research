import FiniteUnimodalMesh
import BernsteinProbability
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false

noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Set Finset

/-- The finite interior binomial mesh costs at most one density peak above
p times the continuous mass. The mode is d/n. -/
theorem binomial_grid_mass {n d p : ℕ} {M : ℝ} (hp : 0 < p)
    (hd : 0 < d) (hnd : d < n)
    (hpeak : binomialDensity n d ((d:ℝ)/(n:ℝ)) ≤ M) :
    (∑ j ∈ Finset.Ico 1 p, (n.choose d : ℝ)*((j:ℝ)/(p:ℝ))^d*
        (1-(j:ℝ)/(p:ℝ))^(n-d)) ≤ (p:ℝ)/((n:ℝ)+1)+M := by
  let h := 1/(p:ℝ)
  let F := binomialPrimitive n d
  have hpR : (0:ℝ) < p := Nat.cast_pos.mpr hp
  have hnR : (0:ℝ) < (n:ℝ)+1 := by positivity
  have hh : 0 < h := one_div_pos.mpr hpR
  have hN : h*((p-1:ℕ):ℝ) ≤ 1 := by
    calc
      h*((p-1:ℕ):ℝ) ≤ h*(p:ℝ) :=
        mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Nat.sub_le _ _)) hh.le
      _ = 1 := one_div_mul_cancel hpR.ne'
  have hmono : MonotoneOn F (Icc (0:ℝ) 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact fun t ht => (hasDerivAt_binomialPrimitive n d t).continuousAt.continuousWithinAt
    · exact fun t ht => (hasDerivAt_binomialPrimitive n d t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hasDerivAt_binomialPrimitive n d t).deriv]
      exact binomialDensity_nonneg n d (interior_subset ht)
  have hm := binomialDensity_unimodal hd hnd
  have hprim : F (h*((p-1:ℕ):ℝ))-F 0 ≤ 1/((n:ℝ)+1) := by
    rw [← binomialPrimitive_mass hnd.le]
    exact sub_le_sub_right (hmono ⟨by positivity,hN⟩ ⟨by norm_num,le_rfl⟩ hN) _
  have hmesh := finite_unimodal_mesh (N := p-1) hm.1 hh hN
    (binomialDensity_nonneg n d ⟨le_rfl,by norm_num⟩) hm.2.1 hm.2.2 hpeak
    (fun t _ => hasDerivAt_binomialPrimitive n d t) hprim
  have hr : (1/((n:ℝ)+1))/h = (p:ℝ)/((n:ℝ)+1) := by
    dsimp [h]
    field_simp
  rw [hr] at hmesh
  rw [sum_Ico_eq_sum_range]
  have hsum : (∑ j ∈ range (p-1), (n.choose d : ℝ)*(((1+j:ℕ):ℝ)/(p:ℝ))^d*
        (1-((1+j:ℕ):ℝ)/(p:ℝ))^(n-d)) =
      ∑ i ∈ range (p-1), binomialDensity n d (h*((i+1:ℕ):ℝ)) := by
    apply sum_congr rfl
    intro i _
    have he : ((1+i:ℕ):ℝ)/(p:ℝ) = h*((i+1:ℕ):ℝ) := by
      dsimp [h]
      rw [Nat.add_comm 1 i, one_div_mul_eq_div]
    rw [he]
    rfl
  rw [hsum]
  exact hmesh

/-- The same bound when the residual grid numerator is written as a natural subtraction. -/
theorem binomial_grid_mass_complement {n d p : ℕ} {M : ℝ} (hp : 0 < p)
    (hd : 0 < d) (hnd : d < n)
    (hpeak : binomialDensity n d ((d:ℝ)/(n:ℝ)) ≤ M) :
    (∑ j ∈ Finset.Ico 1 p, (n.choose d : ℝ)*((j:ℝ)/(p:ℝ))^d*
        (((p-j:ℕ):ℝ)/(p:ℝ))^(n-d)) ≤ (p:ℝ)/((n:ℝ)+1)+M := by
  have heq (j : ℕ) (hj : j ∈ Finset.Ico 1 p) :
      ((p-j:ℕ):ℝ)/(p:ℝ) = 1-(j:ℝ)/(p:ℝ) := by
    rw [Nat.cast_sub (Finset.mem_Ico.mp hj).2.le, sub_div, div_self (by exact_mod_cast hp.ne')]
  have hs : (∑ j ∈ Finset.Ico 1 p, (n.choose d : ℝ)*((j:ℝ)/(p:ℝ))^d*
      (((p-j:ℕ):ℝ)/(p:ℝ))^(n-d)) =
      ∑ j ∈ Finset.Ico 1 p, (n.choose d : ℝ)*((j:ℝ)/(p:ℝ))^d*(1-(j:ℝ)/(p:ℝ))^(n-d) := by
    apply sum_congr rfl
    intro j hj
    rw [heq j hj]
  rw [hs]
  exact binomial_grid_mass hp hd hnd hpeak

#print axioms binomial_grid_mass
#print axioms binomial_grid_mass_complement
end OpenMathResearch.LongCycleExcedances
