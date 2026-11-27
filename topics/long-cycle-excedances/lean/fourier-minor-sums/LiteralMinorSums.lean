import FourierMinorGeometry
import NeighborPoleGeometry

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real Finset

/-- Combine the positive-height mass bounds and the literal odd-pole
contrast, including the central height where the minor window is empty. -/
theorem literal_minor_sums_of_positive_budgets {n k : ℕ} (hk : 100 ≤ k) {s R : ℝ} (hs : 0 ≤ s)
    (N : ℂ → ℂ) (I : Finset ℕ) :
    let p := numeratorPole s 0
    let r := ‖p‖
    let w := fun i : ℕ => numeratorPole s ((i+1:ℕ):ℤ)
    let S := π/r
    let C := s/r
    let f := fun i => (r/‖w i‖)^n*‖N (w i)/N p‖
    let u := fun i => (N (w i)/(‖N p‖:ℂ))*((r:ℂ)/w i)^(n+1)
    R^2 ≤ r^2*(1+2/(k:ℝ)) → (∀ i ∈ I, ‖w i‖ ≤ R) →
    (0 < s → (∑ i ∈ I, (2*(i+1:ℕ)+1:ℝ)*f i) ≤ 1/4 ∧ (∑ i ∈ I, f i) ≤ 1/12) →
    ‖∑ i ∈ I, u i‖ ≤ 1/12 ∧ ‖∑ i ∈ I, ((r:ℂ)/w i-(C:ℂ))*u i‖ ≤ S/4 := by
  intro p r w S C f u hcap henc hmass
  have hr2 : r^2=s^2+π^2 := by
    simpa only [Int.cast_zero,mul_zero,zero_add,one_mul] using literal_pole_norm_sq s 0
  have hr : 0 < r := by nlinarith [sq_nonneg s,norm_nonneg p,sq_pos_of_pos Real.pi_pos]
  have hc (i : ℕ) (_hi : i ∈ I) : ‖(r:ℂ)/w i-(C:ℂ)‖ ≤ (2*(i+1:ℕ)+1:ℝ)*S := by
    let m : ℝ := 2*(i+1:ℕ)+1
    have hw : w i=(s:ℂ)+((m*π:ℝ):ℂ)*Complex.I := by
      dsimp only [w,m,numeratorPole]; push_cast; ring
    have hm : 1 ≤ m := by
      dsimp [m]
      push_cast
      linarith [Nat.cast_nonneg (α:=ℝ) i]
    rw [hw]
    exact neighbor_pole_displacement Real.pi_pos hr hm hr2
  rcases hs.eq_or_lt with hs | hs
  · subst s
    have he := minor_window_at_zero hk hcap I henc
    simp only [he,Finset.sum_empty,norm_zero]
    exact ⟨by norm_num,by dsimp only [S]; positivity⟩
  · obtain ⟨h₁,h₀⟩ := hmass hs
    exact normalized_minor_residue_sums hr.le (div_pos Real.pi_pos hr).le C w (fun i => N (w i))
      (N p) I (fun i _ => principal_radius_le_minor s i)
      (fun i _ => hr.trans_le (principal_radius_le_minor s i)) hc h₀ h₁

#print axioms literal_minor_sums_of_positive_budgets
end OpenMathResearch.LongCycleExcedances
