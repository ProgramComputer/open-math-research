import FourierKernelScalars

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real

/-- Absorb both correction coefficients into the old-row kernel budget.
The next two old-row bounds are taken at the original shifted frequencies. -/
theorem absorb_adjacent_fourier_corrections {n k x S M O J A a f g H : ℝ}
    (hx : 48 ≤ x) (hk : 0 < k) (hn : n=x*k) (hS : 0 ≤ S)
    (hf : 0 ≤ f) (hg : 0 ≤ g)
    (hA : A ≤ (9/10)*n*S) (ha : a ≤ (1/50)*n*S)
    (hf₀ : (n+1-k)*(n+1-2*k)*f ≤ M*k*O)
    (hg₀ : (n+1)*(n+1-k)*g ≤ M*k*O)
    (hH : n*(n-k)*H ≤ M*S*k*J+(n-k)*A*f+(n-k)*a*g) :
    n*(n-k)*H ≤ M*S*k*(J+((9/10)*x/(x-2)+1/50)*O) := by
  have hx0 : 0 < x := by linarith
  have hxd : 0 < x-2 := by linarith
  have hn0 : 0 < n := hn ▸ mul_pos hx0 hk
  have hnk : 0 < n-2*k := by rw [hn]; nlinarith only [mul_le_mul_of_nonneg_right hx hk.le,hk]
  have hnk' : 0 ≤ n-k := by linarith
  have hf1 : (n-k)*(n-2*k)*f ≤ M*k*O := by
    apply le_trans _ hf₀
    apply mul_le_mul_of_nonneg_right _ hf
    apply mul_le_mul (by linarith) (by linarith) hnk.le (by linarith)
  have hg1 : n*(n-k)*g ≤ M*k*O := by
    apply le_trans _ hg₀
    apply mul_le_mul_of_nonneg_right _ hg
    apply mul_le_mul (by linarith) (by linarith) hnk' (by linarith)
  have hratio : n/(n-2*k)=x/(x-2) := by
    apply (div_eq_div_iff hnk.ne' hxd.ne').mpr
    rw [hn]; ring
  have hshift : (n-k)*A*f ≤ (9/10)*S*(x/(x-2))*(M*k*O) := by
    calc
      _ ≤ (n-k)*((9/10)*n*S)*f := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA hnk') hf
      _ = (9/10)*S*((n/(n-2*k))*(n-2*k))*((n-k)*f) := by
        rw [div_mul_cancel₀ _ hnk.ne']; ring
      _ = ((9/10)*S*(n/(n-2*k)))*((n-k)*(n-2*k)*f) := by ring
      _ ≤ ((9/10)*S*(n/(n-2*k)))*(M*k*O) := mul_le_mul_of_nonneg_left hf1 (by positivity)
      _ = _ := by rw [hratio]
  have hend : (n-k)*a*g ≤ (1/50)*S*(M*k*O) := by
    calc
      _ ≤ (n-k)*((1/50)*n*S)*g := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ha hnk') hg
      _ = ((1/50)*S)*(n*(n-k)*g) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hg1 (by positivity)
  apply hH.trans
  calc
    _ ≤ M*S*k*J+(9/10)*S*(x/(x-2))*(M*k*O)+(1/50)*S*(M*k*O) := by linarith only [hshift,hend]
    _ = _ := by ring

#print axioms absorb_adjacent_fourier_corrections
end OpenMathResearch.LongCycleExcedances
