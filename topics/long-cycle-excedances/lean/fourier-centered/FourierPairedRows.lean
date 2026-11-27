import FourierPrincipalAlgebra

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset Real RepositoryQuotientAudit

/-- Common-circle boundary and minor bounds imply real root-sign margins
for the actual coefficients of any real, conjugate-symmetric numerator. -/
theorem paired_rows_from_contour (n : ℕ) (s R : ℝ) (P : Finset ℂ)
    (N : ℂ → ℂ) (hN : ∀ w, N ((starRingEnd ℂ) w)=(starRingEnd ℂ) (N w))
    (old next : ℝ) (F G : ℂ) :
    let p := fourierRowPole s 0
    let r := ‖p‖
    let S := π/r
    let C := s/r
    let D := fun w : ℂ => (r:ℂ)/w-(C:ℂ)
    let U := ‖N p‖
    let b := fun w : ℂ => (N w/(U:ℂ))*((r:ℂ)/w)^(n+1)
    let a := b p
    let I := Finset.range (enclosedPositiveCount s R-1)
    let w := fun i : ℕ => fourierRowPole s ((i+1:ℕ):ℤ)
    let W := r/(2*U)*(r/R)^n
    let Y := r^(n+1)/(2*U)*old
    let Z := r^(n+2)/(2*U)*next
    r<R → (∀ w : ℂ, w ∈ P ↔ w ∈ Set.range (fourierRowPole s) ∧ ‖w‖ < R) →
    0 < U → (old:ℂ)=F/(R:ℂ)^n+∑ w ∈ P, N w/w^(n+1) →
    ((r*next-C*old:ℝ):ℂ)=G/(R:ℂ)^n+∑ w ∈ P, D w*(N w/w^(n+1)) →
    W*‖F‖<1/25 → W*‖G‖<S/25 →
    ‖∑ i ∈ I, b (w i)‖≤1/12 → ‖∑ i ∈ I, D (w i)*b (w i)‖≤S/4 →
    |Y-a.re| < 37/300 ∧ |Z-C*Y-S*a.im| < 29/100*S ∧
      (Y=0 → 99/100 < |a.im| ∧ 0 < Z*a.im) := by
  intro p r S C D U b a I w W Y Z hpr hP hU ho ha hF hG hv hv'
  have him : p.im=π := by simp [p,fourierRowPole]
  have hr : 0 < r := Real.pi_pos.trans_le (him ▸ (le_abs_self p.im).trans (Complex.abs_im_le_norm p))
  have hS : 0 < S := div_pos Real.pi_pos hr
  have hR := hr.trans hpr
  have hp (q : ℂ) := normalized_residue_conjugation N hN n r U C q
  have hpair := enclosed_poles_real_half P hpr hP b (fun q _ => (hp q).1)
  have hpair' := enclosed_poles_real_half P hpr hP (fun q => D q*b q) (fun q _ => (hp q).2)
  have hd : (D p*a).re=S*a.im := by
    have ht : D p= -(S:ℂ)*Complex.I := actual_principal_displacement s
    rw [ht]; simp [Complex.mul_re]
  have hunit : ‖a‖=1 := by
    dsimp only [a,b]
    rw [norm_mul,norm_div,norm_pow,norm_div,Complex.norm_real,Complex.norm_real,
      Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos hr,abs_of_pos hU]
    change U/U*(r/r)^(n+1)=1
    rw [div_self hU.ne',div_self hr.ne',one_pow,mul_one]
  exact signed_contour_readout n P N r R U C S old next hS F G _ _ p ho ha hpair
    (by change (∑ q ∈ P, D q*b q).re/2=(D p*a).re+_ at hpair'; rwa [hd] at hpair')
    (by positivity) hF hG hv hv' hunit

#print axioms paired_rows_from_contour
end OpenMathResearch.LongCycleExcedances
