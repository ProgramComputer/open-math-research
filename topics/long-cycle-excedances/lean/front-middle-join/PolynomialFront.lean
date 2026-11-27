import RealFront
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Topology.Algebra.Polynomial

set_option autoImplicit false

namespace OpenMathResearch.LongCycleExcedances
open Set Polynomial

/-- Polynomial input for the exterior estimates. The lag polynomial includes
the factor X, and the derivative expression equals the normalized zF'−F. -/
def FrontBounds (E L : ℝ[X]) (h : ℕ) (a u : ℝ) : Prop :=
  ∀ v ∈ Icc (7 / 8 : ℝ) (9 / 8),
    let x := -(u * v)
    let B := a * x ^ h
    |E.eval x / B - (1 - v)| < 1 / 10 ∧
    |(x * E.derivative.eval x - ((h : ℝ) + 1) * E.eval x) / B + 1| < 3 / 20 ∧
    |L.eval x| ≤ (18 / 25) * |B|

/-- The recurrence from inserting a label, in the unnormalized polynomial convention. -/
def FrontInsertion (E N L : ℝ[X]) (c : ℝ) : Prop :=
  N = C c * X * E + X * (1 - X) * E.derivative + L

theorem polynomial_front_singleton {E N L : ℝ[X]} {h : ℕ} {a u c : ℝ}
    (ha : 0 < a) (hu : 0 < u) (hb : FrontBounds E L h a u)
    (hi : FrontInsertion E N L c) :
    ∃ w ∈ Icc ((7 / 8 : ℝ) * u) ((9 / 8 : ℝ) * u),
      E.eval (-w) = 0 ∧ 0 < (-1 : ℝ) ^ (h + 1) * N.eval (-w) := by
  let x (v : ℝ) := -(u * v)
  let B (v : ℝ) := a * x v ^ h
  let F (v : ℝ) := E.eval (x v) / B v
  let D (v : ℝ) := (x v * E.derivative.eval (x v) - ((h : ℝ) + 1) * E.eval (x v)) / B v
  let lag (v : ℝ) := L.eval (x v) / ((1 - x v) * B v)
  have hxcont : Continuous x := by unfold x; fun_prop
  have hBcont : Continuous B := by unfold B; fun_prop
  have hx (v : ℝ) (hv : v ∈ Icc (7 / 8 : ℝ) (9 / 8)) : x v < 0 :=
    neg_neg_of_pos (mul_pos hu (lt_of_lt_of_le (by norm_num) hv.1))
  have hB (v : ℝ) (hv : v ∈ Icc (7 / 8 : ℝ) (9 / 8)) : B v ≠ 0 :=
    mul_ne_zero ha.ne' (pow_ne_zero _ (hx v hv).ne)
  have hF : ContinuousOn F (Icc (7 / 8 : ℝ) (9 / 8)) :=
    (E.continuous.comp hxcont).continuousOn.div hBcont.continuousOn hB
  have hzero (v : ℝ) (hv : v ∈ Icc (7 / 8 : ℝ) (9 / 8)) (hz : F v = 0) :
      E.eval (x v) = 0 := (div_eq_zero_iff.mp hz).resolve_right (hB v hv)
  have hlocal (v : ℝ) (hv : v ∈ Icc (7 / 8 : ℝ) (9 / 8)) (hz : F v = 0) :
      |lag v| ≤ 18 / 25 ∧ N.eval (x v) = ((1 - x v) * B v) * (D v + lag v) := by
    have hz' := hzero v hv hz
    have hD : B v * D v = x v * E.derivative.eval (x v) := by
      unfold D
      rw [hz', mul_zero, sub_zero, mul_comm, div_mul_cancel₀ _ (hB v hv)]
    have hrec : N.eval (x v) = ((1 - x v) * B v) * D v + L.eval (x v) := by
      change N = _ at hi
      rw [hi]
      simp only [eval_add, eval_mul, eval_C, eval_X, eval_sub, eval_one, hz', mul_zero, zero_add]
      rw [mul_assoc (1 - x v), hD]
      ring
    have hrec' : x v * (N.eval (x v) / x v) =
        ((1 - x v) * B v) * D v + L.eval (x v) := by
      rw [mul_comm (x v), div_mul_cancel₀ _ (hx v hv).ne]
      exact hrec
    have h := front_normalize_insertion ha (hx v hv) (hb v hv).2.2 hrec'
    exact ⟨h.1, hrec.trans (hrec'.symm.trans h.2)⟩
  obtain ⟨w, hw, hwzero, hwsgn⟩ :=
    front_singleton_witness F D lag E.eval (fun t => N.eval t / t) ha hu hF
      (fun v hv => (hb v hv).1) (fun v hv _ => (hb v hv).2.1)
      (fun v hv hz => (hlocal v hv hz).1) hzero (by
        intro v hv hz
        dsimp only
        change x v * (N.eval (x v) / x v) = _
        rw [mul_comm, div_mul_cancel₀ _ (hx v hv).ne]
        exact (hlocal v hv hz).2)
  refine ⟨w, hw, hwzero, ?_⟩
  have hwpos : 0 < w := lt_of_lt_of_le (mul_pos (by norm_num) hu) hw.1
  have hm : (-1 : ℝ)^h * N.eval (-w) / (-w) > 0 := by
    simpa only [mul_div_assoc] using hwsgn
  rw [pow_succ]
  have hneg : (-1 : ℝ)^h * N.eval (-w) < 0 :=
    (div_pos_iff.mp hm).resolve_left (fun hh => (not_lt_of_ge (neg_nonpos.mpr hwpos.le)) hh.2) |>.1
  linarith

/-- The ordered literal evaluational witnesses used by the exterior/middle join.
A common upper bound on the centers is propagated with the factor 9/8. -/
theorem polynomial_front_ordered {H : ℕ} {E N L : ℝ[X]} {c cap : ℝ}
    (a u : ℕ → ℝ) (ha : ∀ h < H, 0 < a h) (hu : ∀ h < H, 0 < u h)
    (hcap : ∀ h < H, u h ≤ cap)
    (hgap : ∀ h, h + 1 < H → 20 * u h < u (h + 1))
    (hb : ∀ h < H, FrontBounds E L (h + 1) (a h) (u h))
    (hi : FrontInsertion E N L c) :
    ∃ f : Fin H → ℝ, StrictMono f ∧
      ∀ i, 0 < f i ∧ f i ≤ (9 / 8 : ℝ) * cap ∧
        E.eval (-f i) = 0 ∧ 0 < (-1 : ℝ) ^ (i.val + 2) * N.eval (-f i) := by
  classical
  have hex (i : Fin H) := polynomial_front_singleton (ha i i.isLt)
    (hu i i.isLt) (hb i i.isLt) hi
  choose f hf hzero hsign using hex
  refine ⟨f, ?_, ?_⟩
  · intro i j hij
    exact (hf i).2.trans_lt ((front_boxes_ordered u hu hgap i j hij j.isLt).trans_le (hf j).1)
  · intro i
    exact ⟨(mul_pos (by norm_num) (hu i i.isLt)).trans_le (hf i).1,
      (hf i).2.trans (mul_le_mul_of_nonneg_left (hcap i i.isLt) (by norm_num)),
      hzero i, hsign i⟩

#print axioms polynomial_front_singleton
#print axioms polynomial_front_ordered
end OpenMathResearch.LongCycleExcedances
