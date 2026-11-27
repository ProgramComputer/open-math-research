import FourierAdjacentBudget

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real

/-- The original Fourier normalization cancels both factors of cutoff in
the amplitude and kernel estimates for either row error. -/
theorem normalized_circle_error {n k x r T M B C d f decay : ℝ} (hx : 48 ≤ x)
    (hk : 0 < k) (hn : n=x*k) (hr : 0 ≤ r) (hT : 0 < T) (hd : 0 < d)
    (hf : 0 ≤ f) (hC : 0 ≤ C)
    (hcoeff : n*(n-k)*f ≤ M*d*k*C)
    (hamp : r*M/T ≤ k*Real.exp (2997/100)*B)
    (hdec : decay ≤ Real.exp (-(19/20)*x))
    (hB₁ : x ≤ 100 → B ≤ 457) (hB₂ : 100 ≤ x → B ≤ (46/100)*x*Real.sqrt x)
    (hbudget : C ≤ x^2*(110*Real.sqrt x+80)) :
    (r/(2*T))*decay*f < d/25 := by
  have hx0 : 0 < x := by linarith
  have hxd : 0 < x-1 := by linarith
  have hn0 : 0 < n := hn ▸ mul_pos hx0 hk
  have hnk : 0 < n-k := by rw [hn]; nlinarith only [mul_pos hxd hk]
  have hconvert : (r/(2*T))*f ≤ (d*B*C/(2*x*(x-1)))*Real.exp (2997/100) := by
    have hv := (le_div_iff₀ (mul_pos hn0 hnk)).mpr (by linarith only [hcoeff] :
      f*(n*(n-k)) ≤ M*d*k*C)
    calc
      _ ≤ (r/(2*T))*(M*d*k*C/(n*(n-k))) :=
        mul_le_mul_of_nonneg_left hv (by positivity)
      _ = (r*M/T)*(d*k*C/(2*(n*(n-k)))) := by field_simp [hT.ne',hn0.ne',hnk.ne']; ring
      _ ≤ (k*Real.exp (2997/100)*B)*(d*k*C/(2*(n*(n-k)))) :=
        mul_le_mul_of_nonneg_right hamp (by positivity)
      _ = _ := by rw [hn]; field_simp [hk.ne',hx0.ne',hxd.ne',hn ▸ hnk.ne']; ring
  have hw := uniform_normalized_fourier_error hx hC hbudget hB₁ hB₂
  calc
    _ = (r/(2*T)*f)*decay := by ring
    _ ≤ (r/(2*T)*f)*Real.exp (-(19/20)*x) :=
      mul_le_mul_of_nonneg_left hdec (by positivity)
    _ ≤ ((d*B*C/(2*x*(x-1)))*Real.exp (2997/100))*Real.exp (-(19/20)*x) :=
      mul_le_mul_of_nonneg_right hconvert (Real.exp_pos _).le
    _ = d*((B*C/(2*x*(x-1)))*Real.exp (2997/100-(19/20)*x)) := by
      rw [mul_assoc,←Real.exp_add]; rw [show 2997/100+-(19/20)*x=2997/100-(19/20)*x by ring]; ring
    _ < _ := by simpa only [div_eq_mul_inv,one_mul] using mul_lt_mul_of_pos_left hw hd

#print axioms normalized_circle_error
end OpenMathResearch.LongCycleExcedances
