import WidePoleChord
import SmallResidueDensity

noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real Set

open private poisson_series_summable from WideVerticalTransport in
theorem small_vertical_transport {k : ℕ} {x l u D : ℝ}
    (hx : 0 < x)
    (hbnd : π*(31/10)*(∑' i : ℕ, poissonTerm (k-1) (x*(i+1:ℕ))) < D) (hlu : l < u)
    (hseg : ∀ v ∈ Icc l u, ‖verticalArgument x v‖^(k-1) ≤ x^(k-1)*(31/10)) :
    let d (i : ℕ) := verticalMode (k-1) (i+1) x u - verticalMode (k-1) (i+1) x l
    Summable d ∧ π*‖∑' i, d i‖ < D*(u-l) := by
  let m := k-1
  let C : ℝ := 31/10
  let f (i : ℕ) := poissonTerm m (x*(i+1:ℕ))
  let d (i : ℕ) := verticalMode m (i+1) x u - verticalMode m (i+1) x l
  have hb (i : ℕ) : ‖d i‖ ≤ C*f i*(u-l) := by
    have hrad (v : ℝ) (hv : v ∈ Icc l u) : ‖verticalArgument x v‖^m ≤ x^m*C := hseg v hv
    simpa only [f,d,m,mul_comm x] using
      vertical_mode_transport m (i+1) (Nat.succ_pos _) hx.le hlu.le hrad
  have hs : Summable f := poisson_series_summable m hx
  have hmaj : Summable fun i => C*f i*(u-l) := (hs.mul_left C).mul_right (u-l)
  have hd := Summable.of_nonneg_of_le (fun i => norm_nonneg (d i)) hb hmaj
  refine ⟨hd.of_norm,?_⟩
  change π*‖∑' i,d i‖ < _
  have h := (norm_tsum_le_tsum_norm hd).trans (hd.tsum_le_tsum hb hmaj)
  rw [tsum_mul_right,tsum_mul_left] at h
  have hC : π*C*(∑' i,f i) < D := hbnd
  calc
    _ ≤ π*(C*(∑' i,f i)*(u-l)) := mul_le_mul_of_nonneg_left h pi_pos.le
    _ = (π*C*(∑' i,f i))*(u-l) := by ring
    _ < _ := mul_lt_mul_of_pos_right hC (sub_pos.mpr hlu)

theorem small_log_chord_bound {k : ℕ} {x l u D : ℝ}
    (hx : 0 < x)
    (hbnd : π*(31/10)*(∑' i : ℕ, poissonTerm (k-1) (x*(i+1:ℕ))) < D) (hlu : l < u)
    (hseg : ∀ v ∈ Icc l u, ‖verticalArgument x v‖^(k-1) ≤ x^(k-1)*(31/10))
    (t : ℂ) (el : Complex.exp (-verticalArgument x l)=t) (eu : Complex.exp (-verticalArgument x u)=t)
    (g : ℕ → ℂ) (coeff : ∀ j ∈ Finset.range (k-1),
      HasSum (fun i : ℕ => t^(i+1)*((i+1:ℕ):ℂ)^j) (-g (j+1)*((j+1).factorial:ℂ))) :
    π*‖logPolyAt (k-1) g (verticalArgument x u)-logPolyAt (k-1) g (verticalArgument x l)‖ <
      D*(u-l) := by
  rw [log_difference_from_modes (k-1) g x l u t eu el coeff,norm_neg]
  exact (small_vertical_transport hx hbnd hlu hseg).2

#print axioms small_log_chord_bound
end OpenMathResearch.LongCycleExcedances
