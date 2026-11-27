import SimplePoleRemoval
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Filter Set Metric Complex Finset
open scoped Topology

private theorem integral_inv_outside {p : ℂ} {r : ℝ} (hr : 0 ≤ r) (hp : r < ‖p‖) :
    (∮ z in C((0:ℂ), r), (z-p)⁻¹) = 0 := by
  apply Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hr Set.countable_empty
  · apply ContinuousOn.inv₀ (continuous_id.sub continuous_const).continuousOn
    intro z hz hzero
    have he : z = p := sub_eq_zero.mp hzero
    subst z
    exact (not_le_of_gt hp) (by simpa [mem_closedBall, dist_zero_right] using hz)
  · intro z hz
    apply (differentiableAt_id.sub_const p).inv
    intro hzero
    have he : z = p := sub_eq_zero.mp hzero
    subst z
    exact (not_lt_of_ge hp.le) (by simpa [mem_ball, dist_zero_right] using hz.1)

private theorem integral_finset_principal_parts {ρ r R : ℝ} (hρ : 0 < ρ)
    (hrR : ρ ≤ R) (P : Finset ℂ) (a : ℂ → ℂ)
    (hP : ∀ p ∈ P, ρ < ‖p‖ ∧ ‖p‖ < R)
    (hcase : r = ρ ∨ r = R) :
    (∮ z in C((0:ℂ), r), ∑ p ∈ P, a p * (z-p)⁻¹) =
      if r = ρ then 0 else ((2:ℂ)*Real.pi*I) * ∑ p ∈ P, a p := by
  classical
  have hr : 0 ≤ r := hcase.elim (fun e => e.symm ▸ hρ.le) (fun e => e.symm ▸ hρ.le.trans hrR)
  have hcont (p : ℂ) (hp : p ∈ P) :
      ContinuousOn (fun z => a p * (z-p)⁻¹) (sphere 0 r) := by
    apply continuousOn_const.mul
    apply ContinuousOn.inv₀ (continuous_id.sub continuous_const).continuousOn
    intro z hz hz0
    have he : z = p := sub_eq_zero.mp hz0
    subst z
    have hnr : ‖p‖ = r := by simpa [mem_sphere,dist_zero_right] using hz
    rcases hcase with h | h
    · exact (hP p hp).1.ne' (hnr.trans h)
    · exact (hP p hp).2.ne (hnr.trans h)
  have hci (p : ℂ) (hp : p ∈ P) : CircleIntegrable (fun z => a p * (z-p)⁻¹) 0 r :=
    (hcont p hp).circleIntegrable hr
  have hsum :
      (∮ z in C((0:ℂ), r), ∑ p ∈ P, a p * (z-p)⁻¹) =
        ∑ p ∈ P, ∮ z in C((0:ℂ), r), a p * (z-p)⁻¹ := by
    clear hP hci
    induction P using Finset.induction_on with
    | empty => simp [circleIntegral]
    | @insert p P hp ih =>
      have hi := ih (fun q hq => hcont q (Finset.mem_insert_of_mem hq))
      simp only [sum_insert hp]
      rw [circleIntegral.integral_add ((hcont p (Finset.mem_insert_self _ _)).circleIntegrable hr) ?_, hi]
      exact (continuousOn_finset_sum _ fun q hq => hcont q (Finset.mem_insert_of_mem hq)).circleIntegrable hr
  rw [hsum]
  split_ifs with h
  · apply sum_eq_zero
    intro p hp
    rw [circleIntegral.integral_const_mul, h, integral_inv_outside hρ.le (hP p hp).1, mul_zero]
  · have hRr : r = R := hcase.resolve_left h
    rw [Finset.mul_sum]
    apply sum_congr rfl
    intro p hp
    rw [circleIntegral.integral_const_mul, hRr, circleIntegral.integral_sub_inv_of_mem_ball
      (by simpa [mem_ball, dist_zero_right] using (hP p hp).2)]
    ring

/-- Annular contour transfer for finitely many explicitly removed simple poles. -/
theorem annular_principal_parts {ρ R : ℝ} (hρ : 0 < ρ) (hle : ρ ≤ R)
    (P : Finset ℂ) (a : ℂ → ℂ) (f : ℂ → ℂ)
    (hP : ∀ p ∈ P, ρ < ‖p‖ ∧ ‖p‖ < R)
    (hoff : ∀ z ∈ closedBall (0:ℂ) R \ ball 0 ρ, z ∉ P → AnalyticAt ℂ f z)
    (hlocal : ∀ p ∈ P, ∃ g : ℂ → ℂ, AnalyticAt ℂ g p ∧
      ∀ᶠ z in 𝓝[≠] p, f z - a p * (z-p)⁻¹ = g z) :
    (∮ z in C((0:ℂ), R), f z) - (∮ z in C((0:ℂ), ρ), f z) =
      ((2:ℂ)*Real.pi*I) * ∑ p ∈ P, a p := by
  classical
  by_cases hEq : R = ρ
  · have he : P = ∅ := by
      ext p
      rw [show p ∈ (∅ : Finset ℂ) ↔ False by simp]
      refine ⟨?_, False.elim⟩
      intro hp
      exact lt_irrefl _ ((hP p hp).1.trans ((hP p hp).2.trans_eq hEq))
    simp [hEq, he]
  let Q (z : ℂ) := ∑ p ∈ P, a p * (z-p)⁻¹
  choose g hg he using hlocal
  let H (z : ℂ) := if hz : z ∈ P then
    g z hz z - ∑ q ∈ P.erase z, a q * (z-q)⁻¹ else f z - Q z
  have hQ (A : Finset ℂ) (z : ℂ) (hz : z ∉ A) :
      AnalyticAt ℂ (fun w => ∑ q ∈ A, a q * (w-q)⁻¹) z := by
    first | apply A.analyticAt_fun_sum | apply A.analyticAt_sum
    intro q hq
    have hne : z ≠ q := fun e => hz (e.symm ▸ hq)
    exact analyticAt_const.mul ((analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.mpr hne))
  have hHan (z : ℂ) (hz : z ∈ closedBall (0:ℂ) R \ ball 0 ρ) : AnalyticAt ℂ H z := by
    by_cases hp : z ∈ P
    · have hmore : ∀ᶠ w in 𝓝 z, w ∉ P.erase z :=
        ((P.erase z).finite_toSet.isClosed.isOpen_compl.mem_nhds (by simp))
      have hloc := (eventually_nhdsWithin_iff.mp (he z hp))
      apply ((hg z hp).sub (hQ (P.erase z) z (by simp))).congr
      filter_upwards [hmore, hloc] with w hw hwe
      by_cases e : w = z
      · subst w
        simp [H, hp]
      have hwP : w ∉ P := fun h => hw (Finset.mem_erase.mpr ⟨e,h⟩)
      have hpr := hwe (show w ∈ ({z}:Set ℂ)ᶜ from e)
      have hs := Finset.sum_erase_add _ (fun q => a q * (w-q)⁻¹) hp
      simp only [H, dif_neg hwP, Q]
      rw [←hs]
      change g z hp w - _ = _
      linear_combination -hpr
    · have hn : ∀ᶠ w in 𝓝 z, w ∉ P :=
        P.finite_toSet.isClosed.isOpen_compl.mem_nhds hp
      exact ((hoff z hz hp).sub (hQ P z hp)).congr
        (hn.mono fun w hw => by simp [H, hw, Q])
  have hAnn := Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable hρ hle
    (f := H) Set.countable_empty (fun z hz => (hHan z hz).continuousAt.continuousWithinAt)
    (fun z hz => (hHan z ⟨ball_subset_closedBall hz.1.1,
      fun h => hz.1.2 (ball_subset_closedBall h)⟩).differentiableAt)
  have hbd (r : ℝ) (hcase : r = ρ ∨ r = R) :
      (∮ z in C((0:ℂ), r), H z) =
      (∮ z in C((0:ℂ), r), f z) - (∮ z in C((0:ℂ), r), Q z) := by
    have hr : 0 ≤ r := hcase.elim (fun e => e.symm ▸ hρ.le) (fun e => e.symm ▸ hρ.le.trans hle)
    have hz (z : ℂ) (hz : z ∈ sphere 0 r) : z ∈ closedBall (0:ℂ) R \ ball 0 ρ ∧ z ∉ P := by
      have he : ‖z‖ = r := by simpa [mem_sphere, dist_zero_right] using hz
      have hl : ρ ≤ r := hcase.elim (fun e => e.symm ▸ le_rfl) (fun e => e.symm ▸ hle)
      have hu : r ≤ R := hcase.elim (fun e => e.symm ▸ hle) (fun e => e.symm ▸ le_rfl)
      refine ⟨⟨by simpa [mem_closedBall, dist_zero_right, he] using hu,
        by simpa [mem_ball, dist_zero_right, he] using not_lt_of_ge hl⟩, ?_⟩
      intro hm
      rcases hcase with h | h
      · exact (hP z hm).1.ne' (he.trans h)
      · exact (hP z hm).2.ne (he.trans h)
    rw [circleIntegral.integral_congr hr (g := fun z => f z - Q z)
      (fun z h => by simp [H, (hz z h).2])]
    have hf : ContinuousOn f (sphere 0 r) :=
      fun z h => (hoff z (hz z h).1 (hz z h).2).continuousAt.continuousWithinAt
    have hq : ContinuousOn Q (sphere 0 r) :=
      fun z h => (hQ P z (hz z h).2).continuousAt.continuousWithinAt
    exact circleIntegral.integral_sub (hf.circleIntegrable hr) (hq.circleIntegrable hr)
  rw [hbd R (Or.inr rfl), hbd ρ (Or.inl rfl)] at hAnn
  have hOut := integral_finset_principal_parts hρ hle P a hP (Or.inr (rfl : R = R))
  have hIn := integral_finset_principal_parts hρ hle P a hP (Or.inl (rfl : ρ = ρ))
  simp only [if_neg hEq, if_pos rfl] at hOut hIn
  change (∮ z in C((0:ℂ), R), Q z) = _ at hOut
  change (∮ z in C((0:ℂ), ρ), Q z) = _ at hIn
  rw [hOut, hIn] at hAnn
  simp only [if_true, sub_zero] at hAnn
  linear_combination hAnn

#print axioms annular_principal_parts

end OpenMathResearch.LongCycleExcedances
