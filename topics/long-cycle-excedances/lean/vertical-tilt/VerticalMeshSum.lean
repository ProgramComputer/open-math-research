import VerticalTransport
import VerticalRadius

noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real Set

private theorem poisson_series_summable (m : ℕ) {x : ℝ} (hx : 0 < x) :
    Summable fun i : ℕ => poissonTerm m (x*(i+1:ℕ)) := by
  have he (i : ℕ) : poissonTerm m (x*(i+1:ℕ)) =
      (((i+1:ℕ):ℝ)^m*exp (-x*(i+1:ℕ)))*(x^m/(m.factorial:ℝ)) := by
    unfold poissonTerm
    rw [mul_pow,neg_mul]
    ring
  simp only [he]
  exact ((summable_nat_add_iff 1).mpr (Real.summable_pow_mul_exp_neg_nat_mul m hx)).mul_right _

/-- A vertical sum over all truncated exponential modes accumulates less
than 12/25 per unit of pole index on the common enlarged disk. -/
theorem coherent_vertical_transport {k : ℕ} (hk : 7 ≤ k) {x r l u : ℝ}
    (hx : 10*√(k:ℝ) ≤ x) (hr : 0 ≤ r) (hrsq : r^2=x^2+π^2) (hlu : l < u)
    (hseg : ∀ v ∈ Icc l u, ‖verticalArgument x v‖ ≤ r*(1+1/(50*(k:ℝ)))) :
    let d (i : ℕ) := verticalMode (k-1) (i+1) x u - verticalMode (k-1) (i+1) x l
    Summable d ∧ π*‖∑' i, d i‖ < (12/25)*(u-l) := by
  let m := k-1
  let C : ℝ := exp (7/100)
  let f (i : ℕ) := poissonTerm m (x*(i+1:ℕ))
  let d (i : ℕ) := verticalMode m (i+1) x u - verticalMode m (i+1) x l
  have hk' : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hx' : 0 < x := (mul_pos (by norm_num : (0:ℝ)<10) (Real.sqrt_pos.mpr hk')).trans_le hx
  have hb (i : ℕ) : ‖d i‖ ≤ C*f i*(u-l) := by
    have hrad (v : ℝ) (hv : v ∈ Icc l u) : ‖verticalArgument x v‖^m ≤ x^m*C :=
      (pow_le_pow_left₀ (norm_nonneg _) (hseg v hv) m).trans (vertical_radius_power hk hr hx hrsq)
    simpa only [f,d,m,mul_comm x] using
      vertical_mode_transport m (i+1) (Nat.succ_pos _) hx'.le hlu.le hrad
  have hs : Summable f := poisson_series_summable m hx'
  have hmaj : Summable fun i => C*f i*(u-l) := (hs.mul_left C).mul_right (u-l)
  have hd := Summable.of_nonneg_of_le (fun i => norm_nonneg (d i)) hb hmaj
  refine ⟨hd.of_norm,?_⟩
  change π*‖∑' i,d i‖ < _
  have h := (norm_tsum_le_tsum_norm hd).trans (hd.tsum_le_tsum hb hmaj)
  rw [tsum_mul_right,tsum_mul_left] at h
  have hC : π*C*(∑' i,f i) < 12/25 := all_cutoff_vertical_density_budget hk hx
  calc
    _ ≤ π*(C*(∑' i,f i)*(u-l)) := mul_le_mul_of_nonneg_left h pi_pos.le
    _ = (π*C*(∑' i,f i))*(u-l) := by ring
    _ < _ := mul_lt_mul_of_pos_right hC (sub_pos.mpr hlu)

#print axioms coherent_vertical_transport
end OpenMathResearch.LongCycleExcedances
