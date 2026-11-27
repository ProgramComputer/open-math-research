import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real Set Finset

/-- A right-endpoint mesh for a nonnegative unimodal density costs at most
one copy of the maximum above the continuous mass divided by the spacing. -/
theorem finite_unimodal_mesh {f F : ℝ → ℝ} {m h M I : ℝ} {N : ℕ}
    (hm : m ∈ Icc (0 : ℝ) 1) (hh : 0 < h) (hN : h * N ≤ 1)
    (hbase : 0 ≤ f 0) (hinc : MonotoneOn f (Icc 0 m))
    (hdec : AntitoneOn f (Icc m 1)) (hpeak : f m ≤ M)
    (hder : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt F (f t) t)
    (hprim : F (h * N) - F 0 ≤ I) :
    (∑ i ∈ range N, f (h*(i+1:ℕ))) ≤ I/h+M := by
  let U (t : ℝ) := f (min t m)
  have up : MonotoneOn U (Ici 0) := by
    intro a ha b hb hab
    exact hinc ⟨le_min ha hm.1,min_le_right _ _⟩ ⟨le_min hb hm.1,min_le_right _ _⟩
      (min_le_min_right m hab)
  have down : AntitoneOn (fun t => f t-U t) (Icc 0 1) := by
    intro a ha b hb hab
    change f b-U b ≤ f a-U a
    by_cases hb' : b ≤ m
    · simp only [U,min_eq_left hb',min_eq_left (hab.trans hb'),sub_self,le_refl]
    · have hmb : m ≤ b := (lt_of_not_ge hb').le
      by_cases ha' : a ≤ m
      · rw [show U a=f a by simp [U,ha'],show U b=f m by simp [U,hmb],sub_self,sub_nonpos]
        exact hdec ⟨le_rfl, hm.2⟩ ⟨hmb, hb.2⟩ hmb
      · have hma : m ≤ a := (lt_of_not_ge ha').le
        simp only [U,min_eq_right hma,min_eq_right hmb]
        exact sub_le_sub_right (hdec ⟨hma, ha.2⟩ ⟨hmb, hb.2⟩ hab) _
  have step (a b : ℝ) (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a < b) (hstep : b-a=h) :
      h*(f b-U b+U a) ≤ F b-F a := by
    have hc : ContinuousOn F (Icc a b) := fun t ht =>
      (hder t ⟨ha.trans ht.1, ht.2.trans hb⟩).continuousAt.continuousWithinAt
    obtain ⟨c,hc',he⟩ := exists_hasDerivAt_eq_slope F f hab hc
      (fun c hc => hder c ⟨ha.trans hc.1.le, hc.2.le.trans hb⟩)
    have hca := up ha (ha.trans hc'.1.le) hc'.1.le
    have hbc := down ⟨ha.trans hc'.1.le, hc'.2.le.trans hb⟩ ⟨ha.trans hab.le, hb⟩ hc'.2.le
    change f b-U b ≤ f c-U c at hbc
    have hf : f b-U b+U a ≤ f c := by linarith
    rw [hstep] at he
    simpa only [mul_comm h] using (le_div_iff₀ hh).mp (hf.trans_eq he)
  have finite (N : ℕ) (hN : h * N ≤ 1) :
      h*(∑ i ∈ range N, f (h*(i+1:ℕ))) ≤ (F (h*N)-F 0)+h*(U (h*N)-U 0) := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [sum_range_succ]
      have hc : h*((N+1:ℕ):ℝ)-h*(N:ℝ)=h := by push_cast; ring
      have st := step (h*N) (h*(N+1:ℕ)) (by positivity) hN (by linarith) hc
      have hprev : h * (N:ℝ) ≤ 1 := by linarith
      linarith only [st, ih hprev]
  have hm' : U (h*N) ≤ M := by
    exact (hinc ⟨le_min (by positivity) hm.1,min_le_right _ _⟩
      ⟨hm.1,le_rfl⟩ (min_le_right _ _)).trans hpeak
  have h0 : 0 ≤ U 0 := by simpa [U, min_eq_left hm.1] using hbase
  have hU := mul_le_mul_of_nonneg_left (show U (h*N)-U 0 ≤ M by linarith) hh.le
  have hI : I/h*h = I := div_mul_cancel₀ _ hh.ne'
  apply le_of_mul_le_mul_left _ hh
  nlinarith only [finite N hN, hprim, hU, hI]

#print axioms finite_unimodal_mesh
end OpenMathResearch.LongCycleExcedances
