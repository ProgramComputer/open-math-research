import FrontCoefficientNorm
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.IntermediateValue

noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real Polynomial Set

/-- The two central coefficients model an old row at the scale u. -/
def frontOldResidual (P : ℝ[X]) (h : ℕ) (a u : ℝ) : ℝ[X] :=
  P - C a*X^h*(1+C (1/u)*X)

/-- Subtracting a polynomial multiple of the old row leaves all its root
tests unchanged. The last term supplies a known successor sign. -/
def frontNextResidual (P Q G : ℝ[X]) (h : ℕ) (a : ℝ) : ℝ[X] :=
  Q - G*P + (1-X)*C a*X^h

/-- Two finite coefficient inequalities certify an actual old negative
root and the literal successor sign in its exterior box. -/
theorem signed_root_of_front_coefficients (P Q G : ℝ[X]) {h : ℕ} {a u : ℝ}
    (ha : 0 < a) (hu : 0 < u)
    (hP : frontCoefficientNorm (frontOldResidual P h a u) h (7/8*u) (9/8*u) < a/8)
    (hQ : frontCoefficientNorm (frontNextResidual P Q G h a) h (7/8*u) (9/8*u) < a) :
    ∃ w ∈ Ioo (7/8*u) (9/8*u), P.eval (-w) = 0 ∧
      0 < (-1:ℝ)^(h+1)*Q.eval (-w) := by
  let L := 7/8*u
  let U := 9/8*u
  let F (v : ℝ) := (-1:ℝ)^h*P.eval (-v)
  have hL : 0 < L := by dsimp [L]; positivity
  have hLU : L < U := by dsimp [L,U]; linarith
  have powSign (v : ℝ) : (-1:ℝ)^h*(-v)^h=v^h := by rw [←mul_pow]; simp
  have oldErr (v : ℝ) (hv : v ∈ Icc L U) :
      |F v-a*v^h*(1-v/u)| < a/8*v^h := by
    have hbnd := front_coefficient_bound (h:=h) (frontOldResidual P h a u) hL hv.1 hv.2
    have hvpos := hL.trans_le hv.1
    have e : F v-a*v^h*(1-v/u) = (-1:ℝ)^h*(frontOldResidual P h a u).eval (-v) := by
      simp only [F,frontOldResidual,eval_sub,eval_mul,eval_C,eval_pow,eval_X,eval_add,eval_one]
      linear_combination (a*(1-v/u))*(powSign v)
    rw [e,abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul]
    exact hbnd.trans_lt (mul_lt_mul_of_pos_right hP (pow_pos hvpos _))
  have left : 0 < F L := by
    have e : 1-L/u = 1/8 := by dsimp [L]; field_simp <;> ring
    have h := (abs_lt.mp (oldErr L ⟨le_rfl,hLU.le⟩)).1
    rw [e] at h
    linarith
  have right : F U < 0 := by
    have e : 1-U/u = -1/8 := by dsimp [U]; field_simp <;> ring
    have h := (abs_lt.mp (oldErr U ⟨hLU.le,le_rfl⟩)).2
    rw [e] at h
    linarith
  have hcont : ContinuousOn F (Icc L U) :=
    (continuous_const.mul (P.continuous.comp continuous_neg)).continuousOn
  obtain ⟨w,hw,hz⟩ := intermediate_value_Icc' hLU.le hcont
    (show (0:ℝ) ∈ Icc (F U) (F L) from ⟨right.le,left.le⟩)
  have hwpos := hL.trans_le hw.1
  have hwo : w ∈ Ioo L U := ⟨lt_of_le_of_ne hw.1 (fun e => by subst w; linarith),
    lt_of_le_of_ne hw.2 (fun e => by subst w; linarith)⟩
  have hPzero : P.eval (-w)=0 := (mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ (by norm_num))
  have habs := (front_coefficient_bound (h:=h) (frontNextResidual P Q G h a) hL hw.1 hw.2).trans_lt
    (mul_lt_mul_of_pos_right hQ (pow_pos hwpos h))
  have hid : (-1:ℝ)^h*(frontNextResidual P Q G h a).eval (-w) =
      (-1:ℝ)^h*Q.eval (-w)+(1+w)*a*w^h := by
    simp only [frontNextResidual,eval_add,eval_sub,eval_mul,eval_one,eval_X,eval_C,eval_pow,hPzero,
      mul_zero,sub_zero]
    linear_combination ((1+w)*a)*(powSign w)
  have bound : |(-1:ℝ)^h*(frontNextResidual P Q G h a).eval (-w)| < a*w^h := by
    simpa only [abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul] using habs
  rw [hid] at bound
  have hn := (abs_lt.mp bound).2
  have hpos := mul_pos (mul_pos hwpos ha) (pow_pos hwpos h)
  refine ⟨w,hwo,hPzero,?_⟩
  rw [pow_succ]
  linarith

#print axioms signed_root_of_front_coefficients
end OpenMathResearch.LongCycleExcedances
