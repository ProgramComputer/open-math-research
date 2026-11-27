import ColorLagGrid

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset

theorem binomial_residual_identity {N d : ℕ} (hd : d ≤ N) :
    ((N+1).choose d:ℝ)*((N-d+1:ℕ):ℝ)=((N+1:ℕ):ℝ)*(N.choose d:ℝ) := by
  exact_mod_cast (show (N+1).choose d*(N-d+1)=(N+1)*N.choose d by
    have h := Nat.succ_mul_choose_eq N (N-d)
    rw [Nat.choose_symm hd] at h
    rw [Nat.choose_symm_of_eq_add (show N+1 = (N-d).succ+d by omega)] at h
    exact h.symm)

/-- Dividing the residual acceptance bound by its positive number of
colors lowers the binomial grid size by one. No concentration estimate
or restriction on the position of a grid point is required. -/
theorem color_lag_residual_grid {N d p : ℕ} (hd : d ≤ N) (hp : 0 < p)
    (F : ℕ → ℝ) {L C : ℝ} (hC : 0 ≤ C)
    (hL : L ≤ ((N+1).choose d:ℝ)*∑ j ∈ range (p+1), (j:ℝ)^d*F (p-j))
    (hF : ∀ i ≤ p, F i ≤ C*((N-d+1:ℕ):ℝ)*(i:ℝ)^(N-d)) :
    L/(p:ℝ)^(N+1) ≤ (C*((N+1:ℕ):ℝ)/(p:ℝ))*
      ∑ j ∈ range (p+1), colorLoad N d ((j:ℝ)/p) := by
  let S := ∑ j ∈ range (p+1), (j:ℝ)^d*((p-j:ℕ):ℝ)^(N-d)
  have hsum : (∑ j ∈ range (p+1), (j:ℝ)^d*F (p-j)) ≤ C*((N-d+1:ℕ):ℝ)*S := by
    dsimp [S]
    rw [mul_sum]
    apply sum_le_sum
    intro j _
    exact (mul_le_mul_of_nonneg_left (hF (p-j) (Nat.sub_le _ _)) (by positivity)).trans_eq (by ring)
  have hscaled : L ≤ C*((N+1:ℕ):ℝ)*((N.choose d:ℝ)*S) := by
    apply (hL.trans (mul_le_mul_of_nonneg_left hsum (by positivity))).trans_eq
    calc
      _ = (C*S)*(((N+1).choose d:ℝ)*((N-d+1:ℕ):ℝ)) := by ring
      _ = _ := by rw [binomial_residual_identity hd]; ring
  have grid : ((N.choose d:ℝ)*S)/(p:ℝ)^N ≤
      ∑ j ∈ range (p+1), colorLoad N d ((j:ℝ)/p) :=
    color_lag_grid_upper hd hp (fun i => (i:ℝ)^(N-d)) ((N.choose d:ℝ)*S)
      (le_refl _) (fun _ => le_rfl)
  calc
    _ ≤ (C*((N+1:ℕ):ℝ)*((N.choose d:ℝ)*S))/(p:ℝ)^(N+1) :=
      div_le_div_of_nonneg_right hscaled (by positivity)
    _ = (C*((N+1:ℕ):ℝ)/(p:ℝ))*(((N.choose d:ℝ)*S)/(p:ℝ)^N) := by
      rw [div_mul_div_comm,pow_succ,mul_comm ((p:ℝ)^N) (p:ℝ)]
    _ ≤ _ := mul_le_mul_of_nonneg_left grid (by positivity)

#print axioms binomial_residual_identity
#print axioms color_lag_residual_grid
end OpenMathResearch.LongCycleExcedances
