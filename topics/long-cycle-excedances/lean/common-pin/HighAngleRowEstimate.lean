import HighAngleActualInputs
import FarPoleTruncation


noncomputable section
namespace RepositoryQuotientAudit
open Finset PowerSeries LongCycles LongCycleBounds.CycleProfile
open OpenMathResearch.LongCycleExcedances
open scoped Real

def highAngleRow (q k : ℕ) (x : ℝ) : ℝ :=
  let t := -Real.exp (-x)
  ‖coherentPole x 0‖^(q+1) / 2 *
    ((enumerator q k).eval t / ((1-t)^(q+1)*q.factorial))

def highAngleUnit (x : ℝ) : ℂ :=
  (‖coherentPole x 0‖ : ℂ)/coherentPole x 0

def highAnglePrincipal (q k : ℕ) (x : ℝ) : ℂ :=
  seriesValue (coherentTilt k (-Real.exp (-x))) (coherentPole x 0) *
    highAngleUnit x^(q+1)

private def poleTrunc (T : PowerSeries ℝ) (q : ℕ) (x : ℝ) (l : ℤ) : ℂ :=
  ∑ j ∈ range q, ((coeff j T : ℝ) : ℂ) * (1 / coherentPole x l^(q-j+1))

private theorem poleTrunc_conj (T : PowerSeries ℝ) (q : ℕ) (x : ℝ) (l : ℤ) :
    poleTrunc T q x (-(l+1)) = (starRingEnd ℂ) (poleTrunc T q x l) := by
  unfold poleTrunc
  rw [map_sum, coherentPole_conj]
  simp

private theorem poleTrunc_principal (T : PowerSeries ℝ) (q : ℕ) (x : ℝ) :
    (‖coherentPole x 0‖ : ℂ)^(q+1) * poleTrunc T q x 0 =
      highAngleUnit x^(q+1) *
        ∑ j ∈ range q, ((coeff j T : ℝ) : ℂ) * coherentPole x 0^j := by
  have hw : coherentPole x 0 ≠ 0 := norm_pos_iff.mp (coherentPole_near_pos x)
  unfold poleTrunc highAngleUnit
  rw [mul_sum, mul_sum, div_pow]
  apply sum_congr rfl
  intro j hj
  have hq : q+1 = (q-j+1)+j := by have := mem_range.mp hj; omega
  rw [show coherentPole x 0^(q+1) =
    coherentPole x 0^(q-j+1)*coherentPole x 0^j by rw [← pow_add, ← hq]]
  field_simp [hw] <;> ring

/-- The raw normalized actual row differs from its coherent principal mode by
the three explicit truncation errors. -/
theorem actual_high_angle_row_error {q k : ℕ} (hq : 0 < q) (hk : 7 ≤ k)
    {x : ℝ} (hx : 0 ≤ x) (hangle : ‖coherentPole x 0‖ ≤ 2*π) :
    let r := ‖coherentPole x 0‖
    let R := highAngleRadius x k
    let A := Real.exp (5+18*Real.log k)
    let ρ := r/R
    |highAngleRow q k x - (highAnglePrincipal q k x).re| ≤
      A*((k+1)*ρ^q + 10*ρ^(q-1) + 4*ρ^q) := by
  dsimp only
  let w := coherentPole x 0
  let r := ‖w‖
  let R := highAngleRadius x k
  let ρ := r/R
  let A := Real.exp (5+18*Real.log k)
  let t := -Real.exp (-x)
  let T := coherentTilt k t
  let u := poleTrunc T q x
  have hr : 0 < r := coherentPole_near_pos x
  have hR : 0 < R := highAngleRadius_pos x k
  have hk' : 7 ≤ (k:ℝ) := by exact_mod_cast hk
  have hk0 : 0 < (k:ℝ) := by positivity
  have hA : 0 < A := Real.exp_pos _
  have hρ : 0 < ρ := div_pos hr hR
  have hρlt : ρ < 1 := (div_lt_one hR).2 (by
    change r < r*(1+1/(k:ℝ))
    nlinarith [mul_pos hr (one_div_pos.mpr hk0)])
  have hρeq : ρ = (1+1/(k:ℝ))⁻¹ := by
    dsimp [ρ,R,highAngleRadius,r,w]
    rw [div_mul_eq_div_div, div_self hr.ne', one_div]
  have hgeom : 1/(1-ρ) = (k:ℝ)+1 := by
    rw [hρeq]
    field_simp [hk0.ne', show (k:ℝ)+1 ≠ 0 by positivity] <;> ring
  have hT (j : ℕ) : |coeff j T| ≤ A/R^j := by
    apply (original_coherentTilt_coeff_bound (by omega) t R hR j).trans
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact Real.exp_le_exp.mpr (actual_high_angle_log_mass hk hx hangle)
  have hTw (j : ℕ) : ‖((coeff j T : ℝ):ℂ)*w^j‖ ≤ A*ρ^j := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow]
    calc
      _ ≤ A/R^j*r^j := mul_le_mul_of_nonneg_right (hT j) (by positivity)
      _ = _ := by rw [show ρ^j = r^j/R^j by exact div_pow r R j]; ring
  have hz : ‖highAngleUnit x‖ = 1 := by
    unfold highAngleUnit
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, div_self hr.ne']
  have hprincipal : |r^(q+1) * (u 0).re - (highAnglePrincipal q k x).re| ≤ A*((k:ℝ)+1)*ρ^q := by
    have hp := congrArg Complex.re (poleTrunc_principal T q x)
    rw [← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero] at hp
    change r^(q+1) * (u 0).re = _ at hp
    rw [hp, highAnglePrincipal]
    rw [mul_comm (seriesValue _ _)]
    rw [← Complex.sub_re, ← mul_sub]
    apply (Complex.abs_re_le_norm _).trans
    rw [norm_mul, norm_pow, hz, one_pow, one_mul, norm_sub_rev]
    have ht := (taylor_tail_majorant (fun j => ((coeff j T:ℝ):ℂ)*w^j)
      hA.le hρ.le hρlt hTw q).2
    rw [div_eq_mul_one_div, hgeom] at ht
    simpa only [seriesValue, mul_comm, mul_left_comm, mul_assoc] using ht
  let far (i : ℕ) := r^(q+1) * ‖u ((i+1:ℕ):ℤ)‖
  have hfar (i : ℕ) : far i ≤ (5*A*ρ^(q-1))*oddSquareMajorant i := by
    let l := ((i+1:ℕ):ℤ)
    let W := ‖coherentPole x l‖
    have hp : 3 ≤ 2*(i:ℝ)+3 := by linarith [Nat.cast_nonneg (α := ℝ) i]
    have hW : 0 < W := hr.trans_le (coherentPole_near_le x l)
    have hgeo := high_angle_far_pole_geometry hr hk' hp hangle (coherentPole_far_lower x i)
    have hgap : R/W ≤ 16/21 := hgeo.2
    have hRW : R < W := (div_lt_one hW).1 (hgap.trans_lt (by norm_num))
    have hper := norm_far_pole_truncation_le (fun j => ((coeff j T:ℝ):ℂ)) q hA.le hR hRW
      (fun j _ => by simpa [Complex.norm_real, Real.norm_eq_abs] using hT j)
    have hb : 1/(1-R/W) ≤ 5 := by
      apply (div_le_iff₀ (by linarith : 0 < 1-R/W)).2
      linarith
    calc
      far i ≤ r^(q+1) * ((A/(R^(q-1)*W^2))/(1-R/W)) :=
        mul_le_mul_of_nonneg_left hper (by positivity)
      _ = (A*ρ^(q-1)) * (r/W)^2 * (1/(1-R/W)) := by
        have he : q+1=(q-1)+2 := by omega
        rw [he, pow_add r, show ρ^(q-1) = r^(q-1)/R^(q-1) by exact div_pow r R _,
          div_pow]
        have hneq : 1-R/W ≠ 0 := by linarith
        field_simp [hR.ne', hW.ne', hneq] <;> ring
      _ ≤ (5*A*ρ^(q-1))*oddSquareMajorant i := by
        have hmul := mul_le_mul (show (r/W)^2 ≤ oddSquareMajorant i from hgeo.1)
          hb (div_nonneg zero_le_one (by linarith)) (by unfold oddSquareMajorant; positivity)
        have h := mul_le_mul_of_nonneg_left hmul (show 0 ≤ A*ρ^(q-1) by positivity)
        convert h using 1 <;> ring
  have hfarS : Summable far :=
    Summable.of_nonneg_of_le (fun _ => by dsimp [far]; positivity) hfar
      (oddSquareSummable.mul_left _)
  have htail : Summable (fun i : ℕ => ‖u ((i+1:ℕ):ℤ)‖) := by
    convert hfarS.mul_left (r^(q+1))⁻¹ using 1
    funext i
    dsimp only [far]
    rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hr.ne'), one_mul]
  have hs : Summable (fun i : ℕ => ‖u (i:ℤ)‖) := (summable_nat_add_iff 1).mp htail
  have hpair := conjugate_lattice_real u hs (poleTrunc_conj T q x)
  have htailSum : |r^(q+1) * (∑' i : ℕ, u ((i+1:ℕ):ℤ)).re| ≤ 5*A*ρ^(q-1) := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg hr.le _)]
    have h := (Complex.abs_re_le_norm (∑' i : ℕ, u ((i+1:ℕ):ℤ))).trans
      (norm_tsum_le_tsum_norm htail)
    apply (mul_le_mul_of_nonneg_left h (pow_nonneg hr.le _)).trans
    rw [← tsum_mul_left]
    apply (hfarS.tsum_le_tsum hfar (oddSquareSummable.mul_left _)).trans
    rw [tsum_mul_left]
    simpa using mul_le_mul_of_nonneg_left oddSquareSum_le_one
      (show 0 ≤ 5*A*ρ^(q-1) by positivity)
  have htpos : 0 < 1-t := by dsimp [t]; linarith [Real.exp_pos (-x)]
  have hzeroTerm : |r^(q+1)/2 * (coeff q T/(1-t))| ≤ 4*A*ρ^q := by
    have hr8 : r/2 ≤ 4 := by linarith [Real.pi_lt_four]
    have hdiv : 1/(1-t) ≤ 1 := by
      apply (div_le_iff₀ htpos).2
      dsimp [t]
      linarith [Real.exp_pos (-x)]
    rw [abs_mul, abs_of_pos (by positivity : 0 < r^(q+1)/2), abs_div, abs_of_pos htpos]
    calc
      _ ≤ r^(q+1)/2 * ((A/R^q)/(1-t)) := by
        apply mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (hT q) htpos.le) (by positivity)
      _ = (r/2) * (A*ρ^q) * (1/(1-t)) := by
        rw [pow_succ r, show ρ^q = r^q/R^q by exact div_pow r R _]
        ring
      _ ≤ 4*A*ρ^q := by
        have h := mul_le_mul hr8 (show A*ρ^q*(1/(1-t)) ≤ A*ρ^q from
          mul_le_of_le_one_right (by positivity) hdiv)
          (by positivity) (by norm_num : (0:ℝ) ≤ 4)
        convert h using 1 <;> ring
  have hcoef := (original_coherent_row_pair q k (by omega) x hx).1
  have hreal := congrArg Complex.re hcoef
  simp only [Complex.ofReal_re, Complex.add_re] at hreal
  rw [show 1 + Real.exp (-x) = 1-t by simp [t]] at hreal
  change (enumerator q k).eval t / ((1-t)^(q+1)*q.factorial) =
    coeff q T/(1-t) + (∑' l : ℤ, u l).re at hreal
  rw [hpair] at hreal
  have he : highAngleRow q k x - (highAnglePrincipal q k x).re =
      (r^(q+1)*(u 0).re - (highAnglePrincipal q k x).re) +
      r^(q+1)*(∑' i : ℕ, u ((i+1:ℕ):ℤ)).re + r^(q+1)/2 * (coeff q T/(1-t)) := by
    unfold highAngleRow
    change r^(q+1)/2 * ((enumerator q k).eval t / ((1-t)^(q+1)*q.factorial)) - _ = _
    rw [hreal]
    ring
  rw [he]
  have h₁ := abs_add_le (r^(q+1)*(u 0).re - (highAnglePrincipal q k x).re)
    (r^(q+1)*(∑' i : ℕ, u ((i+1:ℕ):ℤ)).re)
  have h₂ := abs_add_le
    ((r^(q+1)*(u 0).re - (highAnglePrincipal q k x).re) +
      r^(q+1)*(∑' i : ℕ, u ((i+1:ℕ):ℤ)).re) (r^(q+1)/2 * (coeff q T/(1-t)))
  have hmid : 0 ≤ 5*A*ρ^(q-1) := by positivity
  change _ ≤ A*(((k:ℝ)+1)*ρ^q + 10*ρ^(q-1) + 4*ρ^q)
  nlinarith only [h₁, h₂, hprincipal, htailSum, hmid, hzeroTerm]

#print axioms actual_high_angle_row_error
end RepositoryQuotientAudit
