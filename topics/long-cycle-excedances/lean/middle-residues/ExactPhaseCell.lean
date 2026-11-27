import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real Set

/-- Endpoints are defined by true phase levels. A monotone phase therefore
fixes the sign of the actual successor at every old root in the cell. -/
theorem signed_true_phase_cell {a b : ℝ} (hab : a < b) (j : ℕ)
    (P Q A φ : ℝ → ℝ) (hP : ContinuousOn P (Icc a b))
    (hφ : StrictMonoOn φ (Icc a b))
    (ha : φ a = (j:ℝ)*π) (hb : φ b = ((j+1:ℕ):ℝ)*π)
    (hA : ∀ θ ∈ Icc a b, 0 < A θ)
    (hE : ∀ θ ∈ Icc a b, |A θ*P θ-cos (φ θ)| ≤ 1/2)
    (hQ : ∀ θ ∈ Ioo a b, P θ = 0 → 0 < Q θ * (-sin (φ θ))) :
    (∃ θ ∈ Ioo a b, P θ = 0) ∧
    (∀ θ ∈ Ioo a b, P θ = 0 → 0 < (-1:ℝ)^(j+1)*Q θ) := by
  have sign (θ : ℝ) (hθ : θ ∈ Icc a b) (s : ℕ) (hφθ : φ θ = (s:ℝ)*π) :
      0 < (-1:ℝ)^s * P θ := by
    have h := hE θ hθ
    have hcos : cos ((s:ℝ)*π) = (-1:ℝ)^s := by simpa using cos_add_nat_mul_pi 0 s
    rw [hφθ,hcos] at h
    rcases Nat.even_or_odd s with he | ho
    · rw [he.neg_one_pow] at h ⊢
      have hp : 0 < A θ*P θ := by linarith only [(abs_le.mp h).1]
      simpa only [one_mul] using pos_of_mul_pos_right hp (hA θ hθ).le
    · rw [ho.neg_one_pow] at h ⊢
      have hp : A θ*P θ < 0 := by linarith only [(abs_le.mp h).2]
      simpa only [neg_one_mul,neg_pos] using neg_of_mul_neg_right hp (hA θ hθ).le
  have hA' := sign a (left_mem_Icc.mpr hab.le) j ha
  have hB' := sign b (right_mem_Icc.mpr hab.le) (j+1) hb
  have hane : P a ≠ 0 := by intro h; simp [h] at hA'
  have hbne : P b ≠ 0 := by intro h; simp [h] at hB'
  have hz : (0:ℝ) ∈ P '' Icc a b := by
    rw [pow_succ] at hB'
    rcases Nat.even_or_odd j with he | ho
    · rw [he.neg_one_pow] at hA' hB'
      exact intermediate_value_Icc' hab.le hP ⟨by linarith,by linarith⟩
    · rw [ho.neg_one_pow] at hA' hB'
      exact intermediate_value_Icc hab.le hP ⟨by linarith,by linarith⟩
  obtain ⟨y,hy,hy0⟩ := hz
  have hay : a < y := lt_of_le_of_ne hy.1 (by intro e; exact hane (e.symm ▸ hy0))
  have hyb : y < b := lt_of_le_of_ne hy.2 (by intro e; exact hbne (e ▸ hy0))
  refine ⟨⟨y,⟨hay,hyb⟩,hy0⟩,?_⟩
  intro θ hθ hθ0
  have lo := hφ (left_mem_Icc.mpr hab.le) ⟨hθ.1.le,hθ.2.le⟩ hθ.1
  have hi := hφ (show θ ∈ Icc a b from ⟨hθ.1.le,hθ.2.le⟩) (right_mem_Icc.mpr hab.le) hθ.2
  rw [ha] at lo; rw [hb,Nat.cast_succ,add_mul,one_mul] at hi
  let u := φ θ - (j:ℝ)*π
  have hs : 0 < sin u := sin_pos_of_pos_of_lt_pi (sub_pos.mpr lo) (by dsimp [u]; linarith only [hi])
  have eqn : sin (φ θ)=(-1:ℝ)^j*sin u := by
    simpa only [u,sub_add_cancel] using sin_add_nat_mul_pi u j
  have hq := hQ θ hθ hθ0
  rw [eqn] at hq
  apply pos_of_mul_pos_left (b:=sin u) _ hs.le
  rw [pow_succ]
  linarith only [hq,show (-1:ℝ)^j * (-1)*Q θ * sin u = Q θ*(-((-1)^j*sin u)) by ring]

/-- The logarithmic modulus variable runs in the opposite direction from
the pole angle. The signed conclusion is identical for the reversed cell. -/
theorem signed_true_phase_cell_anti {a b : ℝ} (hab : a < b) (j : ℕ)
    (P Q A φ : ℝ → ℝ) (hP : ContinuousOn P (Icc a b))
    (hφ : StrictAntiOn φ (Icc a b))
    (ha : φ a = ((j+1:ℕ):ℝ)*π) (hb : φ b = (j:ℝ)*π)
    (hA : ∀ x ∈ Icc a b, 0 < A x)
    (hE : ∀ x ∈ Icc a b, |A x*P x-cos (φ x)| ≤ 1/2)
    (hQ : ∀ x ∈ Ioo a b, P x = 0 → 0 < Q x * (-sin (φ x))) :
    (∃ x ∈ Ioo a b, P x = 0) ∧
    (∀ x ∈ Ioo a b, P x = 0 → 0 < (-1:ℝ)^(j+1)*Q x) := by
  have hc (y : ℝ) (h : y ∈ Icc (-b) (-a)) : -y ∈ Icc a b :=
    ⟨by linarith only [h.2],by linarith only [h.1]⟩
  have ho (y : ℝ) (h : y ∈ Ioo (-b) (-a)) : -y ∈ Ioo a b :=
    ⟨by linarith only [h.2],by linarith only [h.1]⟩
  have h := signed_true_phase_cell (neg_lt_neg hab) j
    (fun y => P (-y)) (fun y => Q (-y)) (fun y => A (-y)) (fun y => φ (-y))
    (hP.comp continuous_neg.continuousOn hc)
    (fun x hx y hy hxy => hφ (hc y hy) (hc x hx) (neg_lt_neg hxy))
    (by simpa only [neg_neg] using hb) (by simpa only [neg_neg] using ha)
    (fun y hy => hA (-y) (hc y hy)) (fun y hy => hE (-y) (hc y hy))
    (fun y hy => hQ (-y) (ho y hy))
  obtain ⟨⟨y,hy,hy0⟩,hv⟩ := h
  refine ⟨⟨-y,ho y hy,hy0⟩,?_⟩
  intro x hx h0
  have h' := hv (-x) ⟨neg_lt_neg hx.2,neg_lt_neg hx.1⟩
  simpa only [neg_neg] using h' (by simpa only [neg_neg] using h0)

#print axioms signed_true_phase_cell
#print axioms signed_true_phase_cell_anti
end OpenMathResearch.LongCycleExcedances
