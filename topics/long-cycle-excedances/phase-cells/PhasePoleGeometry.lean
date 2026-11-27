import HighAngleLattice
import PhaseRemainder

noncomputable section
namespace RepositoryQuotientAudit
open OpenMathResearch.LongCycleExcedances
open scoped Real

private theorem pole_real_coord (x : ℝ) (j : ℤ) : (coherentPole x j).re = x := by
  simp [coherentPole, Complex.add_re, Complex.mul_I_re, Complex.mul_im, Complex.add_im]

private theorem pole_square (x : ℝ) (j : ℤ) :
    ‖coherentPole x j‖^2 = x^2+((2*(j:ℝ)+1)*Real.pi)^2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, pole_real_coord, coherentPole_im]
  ring

theorem principal_far_geometry (x : ℝ) (j : ℕ) :
    let r := ‖coherentPole x 0‖
    r^2*(1+(2*(Real.pi/r)*(j+1:ℕ))^2) ≤ ‖coherentPole x ((j+1:ℕ):ℤ)‖^2 := by
  let r := ‖coherentPole x 0‖
  have hr := coherentPole_near_pos x
  have hr2 : r^2 = x^2+Real.pi^2 := by simpa [r] using pole_square x 0
  have hw := pole_square x ((j+1:ℕ):ℤ)
  change r^2*(1+(2*(Real.pi/r)*(j+1:ℕ))^2) ≤ _
  have hs (v : ℝ) : r^2*(1+(2*(Real.pi/r)*v)^2) = r^2+(2*Real.pi*v)^2 := by
    field_simp [show r ≠ 0 from hr.ne']
  rw [hs, hr2, hw]
  push_cast
  nlinarith [mul_nonneg (by positivity : 0 ≤ 4*((j:ℝ)+1)) (sq_nonneg Real.pi)]

private def dimensionlessPole (x : ℝ) (k : ℕ) (l : ℤ) : ℂ :=
  (coherentPole x 0 / coherentPole x l)^k

private theorem pole_norm_const (x : ℝ) (k : ℕ) (l : ℤ) :
    ‖dimensionlessPole x k l‖ = (‖coherentPole x 0‖/‖coherentPole x l‖)^k := by
  rw [dimensionlessPole, norm_pow, norm_div]

private theorem dimensionless_zero (x : ℝ) (k : ℕ) : dimensionlessPole x k 0 = 1 := by
  simp [dimensionlessPole, (norm_pos_iff.mp (coherentPole_near_pos x))]

theorem all_angle_far_lattice (x : ℝ) {k : ℕ} (hk : 7 ≤ k) :
    let w := coherentPole x 0
    let s := Real.pi/‖w‖
    ‖(∑' l : ℤ, dimensionlessPole x k l) - 1 -
        (w / (starRingEnd ℂ) w)^k‖ ≤ 8/(15*s) := by
  let w := coherentPole x 0
  let r := ‖w‖
  let s := Real.pi/r
  have hr : 0 < r := coherentPole_near_pos x
  have hs : 0 < s := div_pos Real.pi_pos hr
  let W (j : ℕ) := ‖coherentPole x ((j+1:ℕ):ℤ)‖
  have hW (j) : 0 < W j := hr.trans_le (coherentPole_near_le x _)
  obtain ⟨hsum, hbound⟩ := seventh_far_summable_bound hr hs W hW k hk
    (principal_far_geometry x)
  have hshift : Summable (fun j : ℕ => ‖dimensionlessPole x k ((j+1:ℕ):ℤ)‖) := by
    simpa only [pole_norm_const] using hsum
  have hpos : Summable (fun j : ℕ => ‖dimensionlessPole x k (j:ℤ)‖) :=
    (summable_nat_add_iff 1).mp hshift
  have hconj (j : ℕ) : ‖dimensionlessPole x k (-((j:ℤ)+1))‖ =
      ‖dimensionlessPole x k (j:ℤ)‖ := by
    rw [pole_norm_const, pole_norm_const, coherentPole_conj, Complex.norm_conj]
  have h := two_sided_far_remainder (dimensionlessPole x k) hpos hconj
  rw [dimensionless_zero] at h
  have he : dimensionlessPole x k (-1) = (w/(starRingEnd ℂ) w)^k := by
    dsimp [dimensionlessPole, w]
    rw [show (-1:ℤ) = -(0+1) by norm_num, coherentPole_conj]
  rw [he] at h
  exact h.trans (by simpa only [pole_norm_const] using hbound)

#print axioms principal_far_geometry
#print axioms all_angle_far_lattice
end RepositoryQuotientAudit

namespace RepositoryQuotientAudit
open OpenMathResearch.LongCycleExcedances
open scoped Real

theorem scaled_lattice_identity (x : ℝ) (k : ℕ) :
    (∑' l : ℤ, dimensionlessPole x k l) =
      (coherentPole x 0)^k * (∑' l : ℤ, (1:ℂ)/(coherentPole x l)^k) := by
  rw [← tsum_mul_left]
  apply tsum_congr
  intro l
  rw [dimensionlessPole, div_pow, one_div, div_eq_mul_inv]

private theorem high_far_ratio (x : ℝ) (j : ℕ) (hh : ‖coherentPole x 0‖ ≤ 2*Real.pi) :
    ‖coherentPole x 0‖/‖coherentPole x ((j+1:ℕ):ℤ)‖ ≤ 3/5 := by
  let r := ‖coherentPole x 0‖
  let W := ‖coherentPole x ((j+1:ℕ):ℤ)‖
  have hr : 0 < r := coherentPole_near_pos x
  have hW : 0 < W := hr.trans_le (coherentPole_near_le x _)
  have hR2 : r^2 ≤ (2*Real.pi)^2 := pow_le_pow_left₀ hr.le hh 2
  have gap : r^2+8*Real.pi^2 ≤ W^2 := by
    dsimp only [r, W]
    rw [pole_square, pole_square]
    push_cast
    nlinarith [mul_nonneg (by positivity : 0 ≤ 4*(j:ℝ)^2+12*j) (sq_nonneg Real.pi)]
  apply (div_le_iff₀ hW).mpr
  apply le_of_sq_le_sq _ (by positivity)
  nlinarith only [gap, hR2]

theorem high_angle_scaled_far_bound (x : ℝ) {k : ℕ} (hk : 7 ≤ k)
    (hh : ‖coherentPole x 0‖ ≤ 2*Real.pi) :
    let w := coherentPole x 0
    ‖w^k*(∑' l : ℤ, (1:ℂ)/(coherentPole x l)^k) - 1 -
        (w/(starRingEnd ℂ) w)^k‖ ≤ 2*(3/5:ℝ)^(k-2) := by
  let A := dimensionlessPole x k
  let c := (3/5:ℝ)^(k-2)
  have hr := coherentPole_near_pos x
  have hmajor (j : ℕ) : ‖A ((j+1:ℕ):ℤ)‖ ≤ c * oddSquareMajorant j := by
    let v := ‖coherentPole x 0‖/‖coherentPole x ((j+1:ℕ):ℤ)‖
    have hv : 0 ≤ v := div_nonneg hr.le (norm_nonneg _)
    have hb := high_angle_far_pole_geometry hr (by norm_num : (7:ℝ)≤7)
      (by linarith [Nat.cast_nonneg (α := ℝ) j] : (3:ℝ)≤2*(j:ℝ)+3) hh (coherentPole_far_lower x j)
    have h2 : v^2 ≤ oddSquareMajorant j := hb.1
    have ht := pow_le_pow_left₀ hv (high_far_ratio x j hh) (k-2)
    calc
      _ = v^k := pole_norm_const x k _
      _ = v^(k-2)*v^2 := by rw [← pow_add, Nat.sub_add_cancel (by omega : 2 ≤ k)]
      _ ≤ c*oddSquareMajorant j := mul_le_mul ht h2 (sq_nonneg v) (by dsimp [c]; positivity)
  have hmaj : Summable (fun j => c*oddSquareMajorant j) := oddSquareSummable.mul_left c
  have hshift := Summable.of_nonneg_of_le (fun j => norm_nonneg (A ((j+1:ℕ):ℤ))) hmajor hmaj
  have hpos : Summable (fun j : ℕ => ‖A (j:ℤ)‖) := (summable_nat_add_iff 1).mp hshift
  have hconj (j : ℕ) : ‖A (-((j:ℤ)+1))‖ = ‖A (j:ℤ)‖ := by
    dsimp [A]
    rw [pole_norm_const, pole_norm_const, coherentPole_conj, Complex.norm_conj]
  have h := two_sided_far_remainder A hpos hconj
  have hbound : (∑' j : ℕ, ‖A ((j+1:ℕ):ℤ)‖) ≤ c := by
    have H := hshift.tsum_le_tsum hmajor hmaj
    rw [tsum_mul_left] at H
    have hc0 : 0 ≤ c := by dsimp [c]; positivity
    exact H.trans (by simpa using mul_le_mul_of_nonneg_left oddSquareSum_le_one hc0)
  dsimp only [A] at h
  rw [scaled_lattice_identity, dimensionless_zero] at h
  have hc : dimensionlessPole x k (-1) =
      (coherentPole x 0/(starRingEnd ℂ) (coherentPole x 0))^k := by
    dsimp [dimensionlessPole]
    rw [show (-1:ℤ) = -(0+1) by norm_num, coherentPole_conj]
  rw [hc] at h
  exact h.trans (mul_le_mul_of_nonneg_left hbound (by norm_num))

theorem all_angle_scaled_remainder (x : ℝ) {k : ℕ} (hk : 7 ≤ k) :
    let w := coherentPole x 0
    let s := Real.pi/‖w‖
    ‖w^k*(∑' l : ℤ, (1:ℂ)/(coherentPole x l)^k) - 1‖ ≤ 1+8/(15*s) := by
  let w := coherentPole x 0
  let v := (w/(starRingEnd ℂ) w)^k
  have hr : 0 < ‖w‖ := coherentPole_near_pos x
  have hv : ‖v‖ = 1 := by simp [v, norm_pow, norm_div, Complex.norm_conj, hr.ne']
  have h := all_angle_far_lattice x hk
  dsimp only at h
  rw [scaled_lattice_identity] at h
  let B := w^k*(∑' l : ℤ, (1:ℂ)/(coherentPole x l)^k)
  change ‖B-1-v‖ ≤ _ at h
  have hadd := norm_add_le (B-1-v) v
  rw [sub_add_cancel, hv] at hadd
  change ‖B-1‖ ≤ _
  linarith

#print axioms all_angle_scaled_remainder
#print axioms high_angle_scaled_far_bound
end RepositoryQuotientAudit
