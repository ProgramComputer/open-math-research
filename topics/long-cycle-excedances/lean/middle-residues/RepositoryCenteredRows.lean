import RepositoryEnclosedHalf
import NestedNormalized
import NeighborPoleGeometry
import CenteredPoleReadout

noncomputable section
namespace RepositoryQuotientAudit
open Finset LongCycles OpenMathResearch.LongCycleExcedances
open scoped Real

/-- Positive normalization of the literal row at the logarithmic parameter. -/
def nestedScaledRow (q k : ℕ) (x : ℝ) : ℝ :=
  let r := ‖coherentPole x 0‖
  let t := -Real.exp (-x)
  r^(q+1)/2 * ((enumerator q k).eval t/((1-t)^(q+1)*q.factorial)) /
    highAngleAmplitude k x

/-- The adjacent actual normalized rows, their centered comparison, and the
strict successor sign at every old zero in the uniform large-size region. -/
theorem original_middle_centered_rows {n k : ℕ} (hn : 100 ≤ n) (hk : 7 ≤ k)
    (hkn : k ≤ n) {x : ℝ} (hx : 0 ≤ x)
    (hm : 1 ≤ (n:ℝ)*(π/‖coherentPole x 0‖)^2)
    (hsize : 30*Real.log (n:ℝ)+20 < (n:ℝ)/(200*(k:ℝ))) :
    let r := ‖coherentPole x 0‖
    let S := π/r
    let C := x/r
    let U := highAngleAmplitude k x
    let a := highAnglePrincipal n k x / (U : ℂ)
    let Y₀ := nestedScaledRow n k x
    let Y₁ := nestedScaledRow (n+1) k x
    |Y₀-a.re| ≤ 1/4 ∧ |Y₁-C*Y₀-S*a.im| ≤ S/4 ∧
      ((enumerator n k).eval (-Real.exp (-x)) = 0 →
        0 < (enumerator (n+1) k).eval (-Real.exp (-x))*a.im) := by
  dsimp only
  let w := coherentPole x 0
  let r := ‖w‖
  let S := π/r
  let C := x/r
  let R₁ := r*(1+1/(100*(k:ℝ)))
  let R₀ := r*(1+3/(200*(k:ℝ)))
  let Rstar := r*(1+1/(50*(k:ℝ)))
  let A := Real.exp (6+9*Real.log k)
  let t := -Real.exp (-x)
  let T := coherentTilt k t
  let U := highAngleAmplitude k x
  let z (l : ℤ) : ℂ := (r:ℂ)/coherentPole x l
  let b (q : ℕ) (l : ℤ) : ℂ := z l^(q+1)*seriesValue T (coherentPole x l) / (U:ℂ)
  let s := positiveEnclosedPoles x R₀
  let p (i : ℕ) : ℝ := (2*(i+1:ℕ)+1:ℝ)
  let δ : ℝ := 1/(100*(n:ℝ))
  have hr : 0 < r := coherentPole_near_pos x
  have hS : 0 < S := div_pos Real.pi_pos hr
  have hn' : (100:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hn₀ : 0 < (n:ℝ) := by linarith
  have hrad : r ≤ R₀ := le_mul_of_one_le_right hr.le (le_add_of_nonneg_right (by positivity))
  have hradstar : r ≤ Rstar := le_mul_of_one_le_right hr.le (le_add_of_nonneg_right (by positivity))
  have hAmp : Real.exp (-(6+9*Real.log k)) ≤ U := (original_uniform_tilt_envelope hk hx).2 _ hradstar
  have hU : 0 < U := (Real.exp_pos _).trans_le hAmp
  have hU' : ‖seriesValue T w‖ = U := rfl
  have hr2 : r^2=x^2+π^2 := by
    change ‖coherentPole x 0‖^2 = _
    rw [Complex.sq_norm,Complex.normSq_apply,coherentPole_im]
    have hRe : (coherentPole x 0).re=x := by
      simp [coherentPole,Complex.add_re,Complex.mul_I_re,Complex.mul_im]
    rw [hRe]
    norm_num
    ring
  have hS1 : S ≤ 1 := (div_le_one hr).2 (by
    apply le_of_sq_le_sq _ hr.le
    rw [hr2]; nlinarith [sq_nonneg x])
  have hC : |C| ≤ 1 := by
    rw [abs_of_nonneg (div_nonneg hx hr.le)]
    exact (div_le_one hr).2 (by apply le_of_sq_le_sq _ hr.le; rw [hr2]; nlinarith [sq_nonneg π])
  have hδ : δ ≤ S/50 := by
    have hSin : (1:ℝ) ≤ (n:ℝ)*S := hm.trans
      (mul_le_mul_of_nonneg_left (by nlinarith [mul_nonneg hS.le (sub_nonneg.mpr hS1)] :
        S^2 ≤ S) hn₀.le)
    apply (div_le_iff₀ (by positivity : 0 < 100*(n:ℝ))).2
    nlinarith
  have hδ' : δ ≤ 1/20 := by
    apply (div_le_iff₀ (by positivity : 0 < 100*(n:ℝ))).2
    linarith
  have hzre : (z 0).re = C := by
    have he : w.normSq = r^2 := (Complex.sq_norm w).symm
    have hRe : w.re = x := by simp [w,coherentPole,Complex.mul_I_re,Complex.mul_im]
    change (((r:ℝ):ℂ)/w).re = C
    rw [Complex.div_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,zero_div,add_zero,he,hRe]
    dsimp only [C]
    field_simp [hr.ne'] <;> ring
  have hzim : (z 0).im = -S := by
    have he : w.normSq = r^2 := (Complex.sq_norm w).symm
    change (((r:ℝ):ℂ)/w).im = -S
    rw [Complex.div_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,zero_div,zero_sub,he,
      show w.im = π by simpa [w] using coherentPole_im x 0]
    dsimp only [S]
    field_simp [hr.ne'] <;> ring
  have hza : ‖z 0‖ = 1 := by
    dsimp only [z]
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr,div_self hr.ne']
  have ha : ‖b n 0‖ = 1 := by
    dsimp only [b]
    rw [norm_div,norm_mul,norm_pow,hza,one_pow,one_mul,hU',
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos hU,div_self hU.ne']
  have haid : b n 0 = highAnglePrincipal n k x/(U:ℂ) := by
    unfold highAnglePrincipal highAngleUnit
    dsimp only [b,z,T,t,r,w]
    ring
  have hbnext (l : ℤ) : b (n+1) l = b n l*z l := by
    dsimp only [b]
    rw [pow_succ (z l) (n+1)]
    ring
  have hMinor := nested_enclosed_minor_mode_mass hk hx hm
  have hmass : (∑ i ∈ s, p i*‖b n ((i+1:ℕ):ℤ)‖) ≤ 1/5 := by
    have he : (∑ i ∈ s, p i*‖b n ((i+1:ℕ):ℤ)‖) =
        (∑ i ∈ s, p i*‖z ((i+1:ℕ):ℤ)^(n+1)*seriesValue T (coherentPole x ((i+1:ℕ):ℤ))‖)/U := by
      rw [div_eq_mul_inv, sum_mul]
      apply sum_congr rfl
      intro i _
      simp only [b,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hU]
      ring
    rw [he]
    apply (div_le_iff₀ hU).2
    have hMinor' : (∑ i ∈ s, p i*‖z ((i+1:ℕ):ℤ)^(n+1)*seriesValue T (coherentPole x ((i+1:ℕ):ℤ))‖) ≤ U/5 := hMinor
    exact hMinor'.trans_eq (by ring)
  have hdisp (i : ℕ) (_ : i ∈ s) : ‖z ((i+1:ℕ):ℤ)-(C:ℂ)‖ ≤ p i*S := by
    have hp : 1 ≤ p i := by dsimp [p]; linarith [Nat.cast_nonneg (α:=ℝ) i]
    have hw : coherentPole x ((i+1:ℕ):ℤ) = (x:ℂ)+((p i*π:ℝ):ℂ)*Complex.I := by
      unfold coherentPole
      dsimp [p]
      push_cast
      rfl
    have h := neighbor_pole_displacement Real.pi_pos hr hp hr2
    simpa only [z,C,S,hw] using h
  have pairError (q : ℕ) (hnq : n ≤ q) :
      |nestedScaledRow q k x-((b q 0).re+∑ i ∈ s, (b q ((i+1:ℕ):ℤ)).re)| ≤ δ := by
    obtain ⟨hs,hsb⟩ := middle_coherent_square_sum x hm
    have hnq₀ : 0 < q := by omega
    have hRaw := (original_nested_row_error hnq₀ hk hx hs).2
    have hpair := nested_approximation_positive_half (by omega : 2 ≤ k) q x R₀ hrad
    rw [hpair] at hRaw
    let B := (200*(k:ℝ)+3)*(A*(r/R₁)^(q-1))
    have hB : 0 ≤ B := by dsimp [B,A,R₁]; positivity
    have hUp :
        (B*(∑' l : ℤ, (r/‖coherentPole x l‖)^2) + r*A*(r/Rstar)^q)/2 ≤
        (B*(2+(n:ℝ)/2)+r*A*(r/Rstar)^q)/2 := by
      exact div_le_div_of_nonneg_right (add_le_add (mul_le_mul_of_nonneg_left hsb hB) le_rfl) (by norm_num)
    have hBound := div_le_div_of_nonneg_right (hRaw.trans hUp) hU.le
    have hcheck := normalized_nested_budget hn hk hkn hnq hr hm hAmp hsize
    have hrat₁ : r/R₁ = (1+1/(100*(k:ℝ)))⁻¹ := by
      dsimp only [R₁]
      rw [div_mul_eq_div_div,div_self hr.ne',one_div]
    have hratstar : r/Rstar = (1+1/(50*(k:ℝ)))⁻¹ := by
      dsimp only [Rstar]
      rw [div_mul_eq_div_div,div_self hr.ne',one_div]
    have hBudget :
        (((200*(k:ℝ)+3)*(A*(r/R₁)^(q-1))*(2+(n:ℝ)/2) + r*A*(r/Rstar)^q)/2)/U ≤ δ := by
      rw [hrat₁,hratstar]
      simpa only [mul_assoc] using hcheck
    have hIdent :
        (b q 0).re+∑ i ∈ s, (b q ((i+1:ℕ):ℤ)).re =
        ((z 0^(q+1)*seriesValue T w).re +
          ∑ i ∈ s, (z ((i+1:ℕ):ℤ)^(q+1)*seriesValue T (coherentPole x ((i+1:ℕ):ℤ))).re)/U := by
      simp only [b,Complex.div_ofReal_re]
      simp only [div_eq_mul_inv,add_mul,sum_mul,w]
    rw [hIdent,nestedScaledRow,←sub_div,abs_div,abs_of_pos hU]
    exact hBound.trans hBudget
  have hNext := pairError (n+1) (Nat.le_succ n)
  have hP : (b (n+1) 0).re = C*(b n 0).re+S*(b n 0).im := by
    rw [hbnext,Complex.mul_re,hzre,hzim]
    ring
  rw [hP] at hNext
  have hbn (i : ℕ) : b (n+1) ((i+1:ℕ):ℤ) = b n ((i+1:ℕ):ℤ)*z ((i+1:ℕ):ℤ) :=
    hbnext _
  simp_rw [hbn] at hNext
  have h := centered_pole_readout s hS hC hδ hδ' (b n 0) ha
    (fun i => b n ((i+1:ℕ):ℤ)) (fun i => z ((i+1:ℕ):ℤ)) p
    (fun i _ => by dsimp [p]; linarith [Nat.cast_nonneg (α:=ℝ) i]) hmass hdisp
    (pairError n le_rfl) hNext
  rw [haid] at h
  refine ⟨h.1,h.2.1,?_⟩
  intro hz
  have hzero : nestedScaledRow n k x = 0 := by simp [nestedScaledRow,hz]
  have hsgn := h.2.2 hzero
  let P := (r^(n+1+1)/2)/((1-t)^(n+1+1)*(n+1).factorial)/U
  have hP₀ : 0 < P := by
    have ht : 0 < 1-t := by dsimp [t]; linarith [Real.exp_pos (-x)]
    dsimp only [P]
    positivity
  have he : nestedScaledRow (n+1) k x = P*((enumerator (n+1) k).eval t) := by
    unfold nestedScaledRow
    dsimp only [P,r,w,t,U]
    ring
  rw [he,mul_assoc] at hsgn
  exact pos_of_mul_pos_right hsgn hP₀.le

#print axioms original_middle_centered_rows
end RepositoryQuotientAudit
