import JoinAngle
import MiddleAssembly
import RepositoryPoleTransport

set_option autoImplicit false
noncomputable section
namespace RepositoryQuotientAudit
open OpenMathResearch.LongCycleExcedances Real

theorem poleAngle_uniform_join {n : ℕ} (hn : 10^4 ≤ n) :
    poleAngle (uniformJoinLog n) = uniformJoinAngle n := by
  rw [poleAngle, arctan_uniform_join hn]
  ring

theorem original_uniform_join_middle {n : ℕ} (hn : 10^4 ≤ n) :
    1 < (n:ℝ)*(π/‖coherentPole (uniformJoinLog n) 0‖)^2 := by
  let b := uniformJoinLog n
  let r := ‖coherentPole b 0‖
  have hr : 0 < r := coherentPole_near_pos b
  have hre : (coherentPole b 0).re = b := by
    simp [coherentPole,Complex.add_re,Complex.mul_I_re,Complex.mul_im,Complex.add_im]
  have him : (coherentPole b 0).im = π := by simpa using coherentPole_im b 0
  have hr2 : r^2 = b^2+π^2 := by
    dsimp only [r]
    rw [Complex.sq_norm,Complex.normSq_apply,hre,him,pow_two,pow_two]
  change 1 < (n:ℝ)*(π/r)^2
  rw [div_pow,←mul_div_assoc,lt_div_iff₀ (pow_pos hr 2),one_mul,hr2]
  exact uniform_join_radius_sq hn

/-- The actual exterior/middle phase junction for the uniform short-cycle
argument beyond the three smaller cutoffs. -/
theorem original_uniform_join_phase {n k : ℕ} (hn : 10^4 ≤ n) (hk : 7 ≤ k)
    (hcut : 30*log (n:ℝ)+20 < (n:ℝ)/(200*(k:ℝ))) :
    10*√(k:ℝ) < uniformJoinLog n ∧
    1 < (n:ℝ)*sin (uniformJoinAngle n)^2 ∧
    1 < (n:ℝ)*(π/‖coherentPole (uniformJoinLog n) 0‖)^2 ∧
    principalPhaseX n k (uniformJoinLog n) < ((uniformJoinRank n:ℝ)+1)*π := by
  have hx := uniform_join_cutoff_separation hn (show 0 < k by omega) hcut
  have him := principalLogTilt_im_bound hk hx.le
  refine ⟨hx,(uniform_join_geometry hn).2.2.1,original_uniform_join_middle hn,?_⟩
  rw [principalPhaseX, poleAngle_uniform_join hn]
  exact uniform_join_phase_from_imag hn him

#print axioms poleAngle_uniform_join
#print axioms original_uniform_join_middle
#print axioms original_uniform_join_phase
end RepositoryQuotientAudit
