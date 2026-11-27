import LiteralMinorSums
import RepositorySmallCutoffResidues

set_option autoImplicit false
noncomputable section
namespace RepositoryQuotientAudit
open OpenMathResearch.LongCycleExcedances Real Finset

/-- The normalized old row and its signed successor contrast on the enclosed
positive nonprincipal poles of the original permutation generating function.
The endpoint at height zero is included. -/
theorem original_small_cutoff_minor_sums {n k : ℕ} (hn : 10000 ≤ n) (hk : 8 ≤ k) (hk' : k ≤ 99) {s R : ℝ} (hs : 0 ≤ s)
    (hR : 0 ≤ R) (I : Finset ℕ) :
    let p := coherentPole s 0
    let r := ‖p‖
    let w := fun i : ℕ => coherentPole s ((i+1:ℕ):ℤ)
    let T := seriesValue (coherentTilt k (-Real.exp (-s)))
    let u := fun i => (T (w i)/(‖T p‖:ℂ))*((r:ℂ)/w i)^(n+1)
    R^2 ≤ r^2*(1+2/(k:ℝ)) → 1 ≤ (n:ℝ)*(π/r)^2 → (∀ i ∈ I, ‖w i‖ ≤ R) →
    ‖∑ i ∈ I, u i‖ ≤ 1/12 ∧ ‖∑ i ∈ I, ((r:ℂ)/w i-(s/r:ℝ))*u i‖ ≤ (π/r)/4 := by
  intro p r w T u hcap hm henc
  have hr2 : r^2=s^2+π^2 := by
    change ‖numeratorPole s 0‖^2 = s^2+π^2
    simpa only [Int.cast_zero,mul_zero,zero_add,one_mul] using literal_pole_norm_sq s 0
  have hr : 0 < r := by nlinarith [sq_nonneg s,norm_nonneg p,sq_pos_of_pos Real.pi_pos]
  have hc (i : ℕ) (_hi : i ∈ I) : ‖(r:ℂ)/w i-((s/r:ℝ):ℂ)‖ ≤ (2*(i+1:ℕ)+1:ℝ)*(π/r) := by
    let m : ℝ := 2*(i+1:ℕ)+1
    have hw : w i=(s:ℂ)+((m*π:ℝ):ℂ)*Complex.I := by
      dsimp only [w,m,coherentPole]; push_cast; ring
    have hm : 1 ≤ m := by
      dsimp [m]
      push_cast
      linarith [Nat.cast_nonneg (α:=ℝ) i]
    rw [hw]
    exact neighbor_pole_displacement Real.pi_pos hr hm hr2
  obtain ⟨hweighted,hplain⟩ := original_small_cutoff_enclosed_budgets hn hk hk' hs hR hcap hm I henc
  apply normalized_minor_residue_sums hr.le (div_pos Real.pi_pos hr).le (s/r:ℝ) w (fun i => T (w i))
    (T p) I (fun i _ => principal_radius_le_minor s i)
    (fun i _ => hr.trans_le (principal_radius_le_minor s i)) hc
  · exact hplain.trans (by norm_num)
  · exact hweighted.trans (by norm_num)

#print axioms original_small_cutoff_minor_sums
end RepositoryQuotientAudit
