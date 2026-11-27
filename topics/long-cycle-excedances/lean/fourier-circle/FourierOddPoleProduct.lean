import FourierLatticeWeights

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real MeasureTheory Filter

set_option maxHeartbeats 2000000 in
/-- The branch of odd poles runs over *all* integers. The first sum uses the
old-row residues; the second includes an arbitrary bounded contrast multiplier.
At k≥3 the odd-height and unweighted moment sums are both finite. -/
theorem odd_lattice_pole_product (P t : ℤ → ℂ)
    (hP : ∀ l, (P l).im = (2*(l:ℝ)+1)*π) {R S : ℝ} (hR : 0 < R)
    (hg : ∀ l, ‖P l‖ ≠ R) (ht : ∀ l : ℤ, ‖t l‖ ≤ |2*(l:ℝ)+1| * S)
    {k : ℕ} (hk : 3 ≤ k) :
    let c := fun l => (R:ℂ)^k/(P l)^(k-1)
    let a := fun l => poleWeight (c l) (P l) R
    (∫ x in (0:ℝ)..2*π, ‖(∑' l, c l/(P l-circleMap 0 R x))*
      (∑' l, (t l*c l)/(P l-circleMap 0 R x))‖) ≤
        2*π*(∑' l, a l)*((∑' l : ℤ, |2*(l:ℝ)+1| * a l)*S) := by
  dsimp only
  let c := fun l => (R:ℂ)^k/(P l)^(k-1)
  let a := fun l => poleWeight (c l) (P l) R
  let d := fun l => t l*c l
  let b := fun l => poleWeight (d l) (P l) R
  let e := Equiv.intEquivNat.symm
  have he : Tendsto e atTop cofinite := by rw [← Nat.cofinite_eq_atTop]; exact e.injective.tendsto_cofinite
  have hfar := he.eventually (lattice_eventually_far P hP hR)
  obtain ⟨hzero,hfirst⟩ := lattice_moment_weights P hP hR hk
  have ha l : 0 ≤ a l := div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
  have hb l : 0 ≤ b l := div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
  have hba (l : ℤ) : b l ≤ (|2*(l:ℝ)+1| * a l)*S := by
    have heq : b l = ‖t l‖*a l := by dsimp [b,d,a,poleWeight]; rw [norm_mul]; ring
    rw [heq]
    calc
      _ ≤ (|2*(l:ℝ)+1| * S)*a l := mul_le_mul_of_nonneg_right (ht l) (ha l)
      _ = _ := by ring
  have hs'a : Summable a := hzero
  have hs'b : Summable b := Summable.of_nonneg_of_le hb hba (hfirst.mul_right S)
  have B := complex_pole_product_bound (P ∘ e) (P ∘ e) (c ∘ e) (d ∘ e) hR
    (fun i => hg _) (fun i => hg _) hfar hfar (e.summable_iff.mpr hs'a) (e.summable_iff.mpr hs'b)
  have eq1 (g : ℤ → ℂ) (x : ℝ) : complexPoleKernel (P ∘ e) (g ∘ e) R x =
      ∑' l, g l/(P l-circleMap 0 R x) := e.tsum_eq (fun l => g l/(P l-circleMap 0 R x))
  simp_rw [eq1] at B
  change _ ≤ 2*π*(∑' i, a (e i))*(∑' i, b (e i)) at B
  rw [e.tsum_eq a,e.tsum_eq b] at B
  apply B.trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg Real.two_pi_pos.le (tsum_nonneg ha))
  have hc := hs'b.tsum_le_tsum hba (hfirst.mul_right S)
  simpa only [tsum_mul_right] using hc

#print axioms odd_lattice_pole_product
end OpenMathResearch.LongCycleExcedances
