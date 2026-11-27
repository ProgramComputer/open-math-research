import ActualHighAngleSign
import TiltDerivative
import SeventhMoment
import LongCycleBounds.DescentRows

noncomputable section
namespace RepositoryQuotientAudit
open Finset Polynomial LongCycles
open OpenMathResearch.LongCycleExcedances
open scoped Real

/-- The imaginary part of the very log tilt used in the normalized row estimate. -/
def principalLogTilt (k : ℕ) (x : ℝ) : ℂ :=
  ∑ j ∈ range (k-1), (cutoffLogCoefficient k (-Real.exp (-x)) (j+1) : ℂ) *
    (coherentPole x 0)^(j+1)

theorem principalLogTilt_eq (k : ℕ) (x : ℝ) :
    principalLogTilt k x = ∑ j ∈ range (k-1), (logarithmCoeff eulerian j x : ℂ) *
      ((x:ℂ)+(Real.pi:ℂ)*Complex.I)^(j+1) := by
  unfold principalLogTilt
  apply sum_congr rfl
  intro j hj
  have hlt := mem_range.mp hj
  have hw : coherentPole x 0 = (x:ℂ)+(Real.pi:ℂ)*Complex.I := by simp [coherentPole]
  rw [hw]
  congr 2
  cases j with
  | zero =>
    simp [cutoffLogCoefficient, logarithmCoeff, momentOf, LongCycleBounds.longEulerian_zero]
  | succ j =>
    have h1 : j+1+1 ≠ 1 := by omega
    have hd : 2 ≤ j+1+1 ∧ j+1+1 < k := by omega
    simp [cutoffLogCoefficient, h1, hd, logarithmCoeff, momentOf, LongCycleBounds.Band.moment]

/-- The derivative at the actual moving principal pole telescopes to just
the linear coefficient and the first omitted Eulerian moment. -/
theorem actual_principalLogTilt_derivative {k : ℕ} (hk : 2 ≤ k) (x : ℝ) (hx : 0 ≤ x) :
    HasDerivAt (principalLogTilt k)
      ((logarithmCoeff eulerian 0 x : ℂ) +
        LongCycleBounds.oddPoleSum k x * (coherentPole x 0)^(k-1)) x := by
  have H := finiteTilt_diagonal_hasDerivAt (logarithmCoeff eulerian) (k-1) x
    ((Real.pi:ℂ)*Complex.I) (fun j => logarithmCoeff_hasDerivAt eulerian j x
      (LongCycleBounds.longEulerian_succ j))
  have eqf : principalLogTilt k = _ := funext (principalLogTilt_eq k)
  rw [eqf]
  convert H using 1
  have hn : k-1+1 = k := by omega
  have hn' : ((k-1:ℕ):ℂ)+1 = (k:ℂ) := by exact_mod_cast hn
  have fac : k.factorial = k*(k-1).factorial := by
    conv_lhs => rw [← hn]
    rw [Nat.factorial_succ, hn]
  have hfac : ((k-1).factorial:ℂ) ≠ 0 := by exact_mod_cast (k-1).factorial_ne_zero
  have hkn : (k:ℂ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have he' : (k:ℂ) * (logarithmCoeff eulerian (k-1) x : ℂ) =
      -LongCycleBounds.oddPoleSum k x := by
    unfold logarithmCoeff momentOf
    rw [hn, Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_natCast]
    change (k:ℂ) * (-(LongCycleBounds.Band.moment k (-Real.exp (-x)) : ℂ) /
      (k.factorial:ℂ)) = _
    rw [LongCycleBounds.Band.moment_poles k hk x hx, fac, Nat.cast_mul]
    field_simp [hkn, hfac]
    <;> ring
  rw [hn', he']
  simp [coherentPole]

#print axioms actual_principalLogTilt_derivative
end RepositoryQuotientAudit
