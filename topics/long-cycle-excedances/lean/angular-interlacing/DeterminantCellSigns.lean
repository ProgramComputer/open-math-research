import CellReadout
import Batteries.Tactic.OpenPrivate

set_option autoImplicit false
namespace OpenMathResearch.LongCycleExcedances
open Set Real
open private exists_zero_of_signed_grid_endpoints from CellReadout

/-- At a sample and at every interior old zero, the sine determinant determines
the literal sign even when the two row normalizations differ. -/
theorem determinant_signed_cell {a b : ℝ} (hab : a < b) {n : ℕ} (hn : 0<n) (j : ℕ)
    {P Q V W : ℝ→ℝ} (hP : ContinuousOn P (Icc a b))
    (ha : (n:ℝ)*a=(j:ℝ)*π) (hb : (n:ℝ)*b=((j+1:ℕ):ℝ)*π)
    (hs : ∀ θ ∈ Icc a b, 0 < sin θ)
    (hV : ∀ θ ∈ Icc a b, 0 < V θ) (hW : ∀ θ ∈ Icc a b, 0 < W θ)
    (hD : ∀ θ ∈ Icc a b, 0 < sin ((n:ℝ)*θ+θ)*(V θ*P θ) -
      sin ((n:ℝ)*θ)*(W θ*Q θ)) :
    (∃ θ ∈ Ioo a b, P θ=0) ∧
      ∀ θ ∈ Ioo a b, P θ=0 → 0 < (-1:ℝ)^(j+1)*Q θ := by
  have sample (m : ℕ) {θ : ℝ} (hθ : θ ∈ Icc a b) (he : (n:ℝ)*θ=(m:ℝ)*π) :
      0 < (-1:ℝ)^m*P θ := by
    have h := hD θ hθ
    rw [he,add_comm ((m:ℝ)*π) θ,sin_add_nat_mul_pi,sin_nat_mul_pi,zero_mul,sub_zero] at h
    have hr : 0 < (sin θ*V θ)*((-1:ℝ)^m*P θ) := by
      rwa [show (sin θ*V θ)*((-1:ℝ)^m*P θ) = ((-1:ℝ)^m*sin θ)*(V θ*P θ) by ring]
    exact pos_of_mul_pos_right hr (mul_pos (hs θ hθ) (hV θ hθ)).le
  refine ⟨exists_zero_of_signed_grid_endpoints hab.le P hP j
    (sample j (left_mem_Icc.mpr hab.le) ha) (sample (j+1) (right_mem_Icc.mpr hab.le) hb), ?_⟩
  intro θ ht hz
  have hc : θ ∈ Icc a b := ⟨ht.1.le,ht.2.le⟩
  let v := (n:ℝ)*θ-(j:ℝ)*π
  have hp : (0:ℝ) < n := by exact_mod_cast hn
  have hv : 0 < v := by dsimp only [v]; rw [←ha]; exact sub_pos.mpr (mul_lt_mul_of_pos_left ht.1 hp)
  have hv' : v < π := by
    have h := mul_lt_mul_of_pos_left ht.2 hp
    rw [hb,Nat.cast_succ,add_mul,one_mul] at h
    dsimp only [v]; linarith only [h]
  have he : sin ((n:ℝ)*θ)=(-1:ℝ)^j*sin v := by
    simpa only [v,sub_add_cancel] using sin_add_nat_mul_pi v j
  have h := hD θ hc
  rw [hz,mul_zero,mul_zero,zero_sub,he] at h
  have h' : 0 < (sin v*W θ)*((-1:ℝ)^(j+1)*Q θ) := by
    rw [pow_succ]
    rwa [show (sin v*W θ)*((-1:ℝ)^j*(-1)*Q θ) = -(((-1:ℝ)^j*sin v)*(W θ*Q θ)) by ring]
  exact pos_of_mul_pos_right h' (mul_pos (sin_pos_of_pos_of_lt_pi hv hv') (hW θ hc)).le

#print axioms determinant_signed_cell
end OpenMathResearch.LongCycleExcedances
