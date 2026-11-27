import FourierPolePointwiseBudget
import FourierLatticeWeights
import FourierAnchoredLogistic
import LiteralDiscretePoleMoments
import Mathlib.Analysis.Normed.Group.InfiniteSum

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances

open scoped BigOperators Real

private theorem total_of_scaled_bound {g f : ℤ → ℝ} (hf : Summable f)
    (hg : ∀ l, 0 ≤ g l) {C M : ℝ} (hC : 0 ≤ C)
    (hpoint : ∀ l, g l ≤ C*f l) (hM : (∑' l, f l) ≤ M) :
    Summable g ∧ (∑' l, g l) ≤ C*M := by
  have hm := hf.mul_left C
  have hs := Summable.of_nonneg_of_le hg hpoint hm
  refine ⟨hs, (hs.tsum_le_tsum hpoint hm).trans ?_⟩
  rw [hf.tsum_mul_left]
  exact mul_le_mul_of_nonneg_left hM hC

private theorem literal_row_inverse_norm_le_one {s r : ℝ} (hr : 0 < r)
    (hr2 : r^2 = s^2+π^2) (l : ℤ) : ‖(r:ℂ)/fourierRowPole s l‖ ≤ 1 := by
  have hl := odd_lattice_height_one_le l
  have hsq := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hl 2
  rw [one_pow,sq_abs] at hsq
  have hsq' := mul_le_mul_of_nonneg_right hsq (sq_nonneg π)
  have h := literal_pole_norm_sq s l
  change ‖fourierRowPole s l‖^2 = s^2+((2*(l:ℝ)+1)*π)^2 at h
  have hp : r ≤ ‖fourierRowPole s l‖ := by
    apply le_of_sq_le_sq _ (norm_nonneg _)
    rw [hr2,h,mul_pow]
    linarith only [hsq']
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]
  exact (div_le_one (hr.trans_le hp)).2 hp

/-- Numerical sums for the exact original row kernels and their endpoint
correction, on an annulus satisfying the squared pole gap hypothesis. -/
theorem literal_fourier_kernel_budgets {n k : ℕ} (hk : 100 ≤ k) (hx : 48 ≤ (n:ℝ)/k)
    {s r R c : ℝ} (hr : 0 < r) (hr2 : r^2 = s^2+π^2)
    (hlo : r ≤ R) (hhi : R ≤ (1+1/(k:ℝ))*r)
    (hsize : 1 ≤ (n:ℝ)*(π/r)^2) (hc : 1/((n:ℝ)/k) ≤ c)
    (hgap : ∀ l : ℤ, c*r^2/(k:ℝ) ≤ poleGap (fourierRowPole s l) R) :
    let x := (n:ℝ)/k
    let P := fourierRowPole s
    let a := fun l => (R:ℂ)^k/(P l)^(k-1)
    let label := fun l : ℤ => |2*(l:ℝ)+1|
    let u := fun l => poleWeight (a l) (P l) R
    let v := fun l => squaredPoleWeight (a l) (P l) R
    let S₀ := ∑' l, u l
    let S₁ := ∑' l, label l*u l
    let T₀ := ∑' l, v l
    let T₁ := ∑' l, label l*v l
    let A := (∑' l, ((r:ℂ)/(P l))*a l)/(R:ℂ)
    Summable u ∧ Summable (fun l => label l*u l) ∧
      Summable v ∧ Summable (fun l => label l*v l) ∧
      Summable (fun l => ‖((r:ℂ)/(P l))*a l‖) ∧
      0 ≤ S₀ / Real.sqrt k ∧ 0 ≤ S₁ / Real.sqrt k ∧
      S₀ / Real.sqrt k ≤ 9*x ∧ S₁ / Real.sqrt k ≤ 12*x*Real.sqrt x ∧
      R*T₀/(k:ℝ) ≤ 10*x*Real.sqrt x ∧ R*T₁/(k:ℝ) ≤ 13*x^2 ∧
      ‖A‖ ≤ 9*Real.sqrt x := by
  let x := (n:ℝ)/k
  let P := fourierRowPole s
  let a := fun l => (R:ℂ)^k/(P l)^(k-1)
  let label := fun l : ℤ => |2*(l:ℝ)+1|
  let u := fun l => poleWeight (a l) (P l) R
  let v := fun l => squaredPoleWeight (a l) (P l) R
  let f := fun l => ‖(r:ℂ)/(P l)‖^(k-1)
  let F := fun l => label l*f l
  let z := fun l => ((r:ℂ)/(P l))*a l
  let K : ℝ := k
  let H : ℝ := Real.sqrt (K*x)
  have hkN : 0 < k := by omega
  have hkR : 0 < K := by
    change (0:ℝ) < (k:ℝ)
    exact_mod_cast hkN
  have hk100 : (100:ℝ) ≤ K := by
    change (100:ℝ) ≤ (k:ℝ)
    exact_mod_cast hk
  have hx48 : 48 ≤ x := hx
  have hx0 : 0 < x := by linarith only [hx48]
  have hR : 0 < R := hr.trans_le hlo
  have hH : 0 < H := Real.sqrt_pos.2 (mul_pos hkR hx0)
  have hsK : 0 < Real.sqrt K := Real.sqrt_pos.2 hkR
  have hratio : R/r ≤ (101/100:ℝ) := by
    have h := (div_le_iff₀ hr).2 hhi
    have he : (1:ℝ)/K ≤ 1/100 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hk100
    linarith only [h,he]
  have hraw := literal_discrete_pole_norm_moments hk (by linarith only [hx48]) hr hr2 hsize
  change Summable f ∧ Summable F ∧ (∑' l, f l) ≤ 3*Real.sqrt x ∧ (∑' l, F l) ≤ 4*x at hraw
  obtain ⟨hf,hF,hfmax,hFmax⟩ := hraw
  have hgap' (l : ℤ) : r^2/(K*x) ≤ poleGap (P l) R := by
    have h := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hc (sq_nonneg r)) hkR.le
    change (1/x)*r^2/K ≤ c*r^2/K at h
    have he : r^2/(K*x) = (1/x)*r^2/K := by simp only [div_eq_mul_inv,mul_inv_rev]; ring
    exact (he.trans_le h).trans (hgap l)
  have hInv (l : ℤ) : (Real.sqrt (poleGap (P l) R))⁻¹ ≤ H/r ∧
      (poleGap (P l) R)⁻¹ ≤ K*x/r^2 :=
    squared_gap_inverse_factors hx0 hkR hr (hgap' l)
  have ha (l : ℤ) : ‖a l‖ ≤ (3*r)*f l :=
    row_pole_coefficient_bound hkN hr hR hhi (P l)
  have hu (l : ℤ) : 0 ≤ u l := div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
  have hv (l : ℤ) : 0 ≤ v l := div_nonneg (norm_nonneg _) (abs_nonneg _)
  have hl (l : ℤ) : 0 ≤ label l := abs_nonneg _
  have hpU (l : ℤ) : u l ≤ (3*H)*f l := by
    dsimp only [u,poleWeight]
    rw [div_eq_mul_inv]
    calc
      _ ≤ ((3*r)*f l)*(H/r) :=
        mul_le_mul (ha l) (hInv l).1 (by positivity) (by positivity)
      _ = (3*H)*f l*(r/r) := by ring
      _ = _ := by rw [div_self hr.ne',mul_one]
  have hpV (l : ℤ) : v l ≤ (3*K*x/r)*f l := by
    dsimp only [v,squaredPoleWeight]
    rw [div_eq_mul_inv]
    calc
      _ ≤ ((3*r)*f l)*(K*x/r^2) :=
        mul_le_mul (ha l) (hInv l).2 (inv_nonneg.mpr (abs_nonneg _)) (by positivity)
      _ = (3*K*x)*f l*(r/r^2) := by ring
      _ = (3*K*x)*f l*(1/r) := by rw [pow_two,← div_div,div_self hr.ne']
      _ = _ := by ring
  have hpU' (l : ℤ) : label l*u l ≤ (3*H)*F l :=
    (mul_le_mul_of_nonneg_left (hpU l) (hl l)).trans_eq (by dsimp only [F]; ring)
  have hpV' (l : ℤ) : label l*v l ≤ (3*K*x/r)*F l :=
    (mul_le_mul_of_nonneg_left (hpV l) (hl l)).trans_eq (by dsimp only [F]; ring)
  have hpA (l : ℤ) : ‖z l‖ ≤ (3*r)*f l := by
    dsimp only [z]
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (literal_row_inverse_norm_le_one hr hr2 l)).trans (ha l)
  obtain ⟨hu0,hu0max⟩ := total_of_scaled_bound hf hu (by positivity) hpU hfmax
  obtain ⟨hu1,hu1max⟩ := total_of_scaled_bound hF (fun l => mul_nonneg (hl l) (hu l))
    (by positivity) hpU' hFmax
  obtain ⟨hv0,hv0max⟩ := total_of_scaled_bound hf hv (by positivity) hpV hfmax
  obtain ⟨hv1,hv1max⟩ := total_of_scaled_bound hF (fun l => mul_nonneg (hl l) (hv l))
    (by positivity) hpV' hFmax
  obtain ⟨hz,hzmax⟩ := total_of_scaled_bound hf (fun l => norm_nonneg (z l))
    (by positivity) hpA hfmax
  have hHe : H = Real.sqrt K*Real.sqrt x := Real.sqrt_mul hkR.le x
  have hU0 : (∑' l, u l) / Real.sqrt K ≤ 9*x := by
    apply (div_le_iff₀ hsK).2
    calc
      _ ≤ (3*H)*(3*Real.sqrt x) := hu0max
      _ = _ := by
        rw [hHe]
        ring_nf
        simp only [Real.sq_sqrt hx0.le]
  have hU1 : (∑' l, label l*u l) / Real.sqrt K ≤ 12*x*Real.sqrt x := by
    apply (div_le_iff₀ hsK).2
    calc
      _ ≤ (3*H)*(4*x) := hu1max
      _ = _ := by rw [hHe]; ring
  have hV0 : R*(∑' l, v l)/K ≤ 10*x*Real.sqrt x := by
    calc
      _ ≤ R*((3*K*x/r)*(3*Real.sqrt x))/K :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hv0max hR.le) hkR.le
      _ = (R/r)*(9*x*Real.sqrt x)*(K/K) := by ring
      _ = (R/r)*(9*x*Real.sqrt x) := by rw [div_self hkR.ne',mul_one]
      _ ≤ (101/100)*(9*x*Real.sqrt x) :=
        mul_le_mul_of_nonneg_right hratio (by positivity)
      _ ≤ _ := by nlinarith only [mul_nonneg hx0.le (Real.sqrt_nonneg x)]
  have hV1 : R*(∑' l, label l*v l)/K ≤ 13*x^2 := by
    calc
      _ ≤ R*((3*K*x/r)*(4*x))/K :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hv1max hR.le) hkR.le
      _ = (R/r)*(12*x^2)*(K/K) := by ring
      _ = (R/r)*(12*x^2) := by rw [div_self hkR.ne',mul_one]
      _ ≤ (101/100)*(12*x^2) := mul_le_mul_of_nonneg_right hratio (by positivity)
      _ ≤ _ := by nlinarith only [sq_nonneg x]
  have hAZ : ‖(∑' l, z l)/(R:ℂ)‖ ≤ 9*Real.sqrt x := by
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hR]
    apply (div_le_iff₀ hR).2
    calc
      _ ≤ ∑' l, ‖z l‖ := norm_tsum_le_tsum_norm hz
      _ ≤ (3*r)*(3*Real.sqrt x) := hzmax
      _ = (9*Real.sqrt x)*r := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlo (by positivity)
  exact ⟨hu0,hu1,hv0,hv1,hz,div_nonneg (tsum_nonneg hu) hsK.le,
    div_nonneg (tsum_nonneg (fun l => mul_nonneg (hl l) (hu l))) hsK.le,
    hU0,hU1,hV0,hV1,hAZ⟩

#print axioms literal_fourier_kernel_budgets
end OpenMathResearch.LongCycleExcedances
