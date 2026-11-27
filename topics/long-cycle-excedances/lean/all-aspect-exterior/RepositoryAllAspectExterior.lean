import ExteriorIntegerSeam
import ExteriorScaleOrder
import RepositoryOldFrontTails
import FrontLagSum
import CoefficientFrontWindow
import PolynomialFront
import LongCycleBounds.UniversalRecurrence

set_option autoImplicit false
noncomputable section
namespace RepositoryQuotientAudit
open LongCycles Real Polynomial OpenMathResearch.LongCycleExcedances

/-- At every exterior rank, the literal lag ratio through the near range
suffices for the two finite coefficient tests for the old and actual next rows. -/
theorem original_exterior_coefficient_tests_all {n k h : ℕ}
    (hn : 10000 ≤ n) (hk : 2 ≤ k) (hkn : k ≤ n)
    (hh : 0 < h) (hH : h ≤ uniformJoinRank n)
    (hnear : ∀ j ≤ ⌊sqrt (n:ℝ)/2⌋₊,
      |(originalFrontLag n k).coeff j| ≤ (8/25)*|(enumerator n k).coeff j|) :
    let P := enumerator n k
    let Q := enumerator (n+1) k
    let a := P.coeff h
    let u := originalExteriorScale n k h
    let G := C (n:ℝ)*X+(1-X)*C ((h:ℝ)+1)
    (0 < a ∧ 0 < u) ∧
      frontCoefficientNorm (frontOldResidual P h a u) h (7/8*u) (9/8*u) < a/8 ∧
      frontCoefficientNorm (frontNextResidual P Q G h a) h (7/8*u) (9/8*u) < a := by
  let P := enumerator n k
  let Q := enumerator (n+1) k
  let V := originalFrontLag n k
  let a := P.coeff h
  let u := originalExteriorScale n k h
  let J := ⌊sqrt (n:ℝ)/2⌋₊
  obtain ⟨⟨ha,hb⟩,hleft,hright⟩ := original_old_front_weighted_tails_all hn hk hkn hh hH
  have hu : 0 < u := div_pos ha hb
  have hc : P.coeff (h+1) = a/u := by
    change P.coeff (h+1) = a/(a/P.coeff (h+1))
    have ha' : a ≠ 0 := ha.ne'
    rw [div_div_eq_mul_div, mul_comm a, mul_div_cancel_right₀ _ ha']
  have hrec : Q = C (n:ℝ)*X*P+(1-X)*(X*P.derivative)+V := by
    have hi := (LongCycleBounds.Insertion.enumerator_succ hk : FrontInsertion P Q V (n:ℝ))
    change Q = C (n:ℝ)*X*P+X*(1-X)*P.derivative+V at hi
    rw [hi]
    ring
  obtain ⟨hHp,hbudget⟩ := exterior_floor_budget hn
  have hs := original_front_scale_cap_all hn hk hkn hh hH
  have hcap' : (9/8:ℝ)*u ≤ (459/40:ℝ)*((uniformJoinRank n:ℝ)/((uniformJoinRank n:ℝ)+1))^n := by
    calc
      _ ≤ (9/8:ℝ)*((51/5:ℝ)*((uniformJoinRank n:ℝ)/((uniformJoinRank n:ℝ)+1))^n) :=
        mul_le_mul_of_nonneg_left hs (by norm_num)
      _ = _ := by ring
  have hsmall := hcap'.trans ((front_cap_lt_half hn hHp hbudget).le)
  have hgap : h+2 ≤ J := front_lag_cutoff_gap hn hH
  have hnearW (j : ℕ) (hj : j ≤ J) :
      |V.coeff j| * frontCoefficientWeight h (7/8*u) (9/8*u) j ≤
      (8/25)*(|P.coeff j| * frontCoefficientWeight h (7/8*u) (9/8*u) j) := by
    have hw : 0 ≤ frontCoefficientWeight h (7/8*u) (9/8*u) j := by
      unfold frontCoefficientWeight
      split <;> positivity
    rw [←mul_assoc]
    exact mul_le_mul_of_nonneg_right (hnear j hj) hw
  exact ⟨⟨ha,hu⟩,front_certificates_of_weighted_envelopes P Q V ha hu hsmall hgap rfl hc hrec
    hleft hright hnearW (fun j hj => original_far_front_weighted_lag_all hn hk hkn hh hH hj)⟩

/-- Each of H ordered, disjoint intervals contains a literal old root with the
required successor sign, conditional on the near-lag bound. -/
theorem original_exterior_root_witnesses_all {n k : ℕ}
    (hn : 10000 ≤ n) (hk : 2 ≤ k) (hkn : k ≤ n)
    (hnear : ∀ j ≤ ⌊sqrt (n:ℝ)/2⌋₊,
      |(originalFrontLag n k).coeff j| ≤ (8/25)*|(enumerator n k).coeff j|) :
    let H := uniformJoinRank n
    let u (i : Fin H) := originalExteriorScale n k (i.val+1)
    ∃ f : Fin H → ℝ, StrictMono f ∧ ∀ i,
      f i ∈ Set.Ioo ((7/8:ℝ)*u i) ((9/8:ℝ)*u i) ∧
      0 < f i ∧
      f i ≤ (459/40:ℝ)*((H:ℝ)/((H:ℝ)+1))^n ∧
      (enumerator n k).eval (-f i) = 0 ∧
      0 < (-1:ℝ)^(i.val+2)*(enumerator (n+1) k).eval (-f i) := by
  let H := uniformJoinRank n
  let P := enumerator n k
  let Q := enumerator (n+1) k
  let u (i : Fin H) := originalExteriorScale n k (i.val+1)
  have center_pos (h : ℕ) (hh : 0 < h) (hH : h ≤ H) : 0 < originalExteriorScale n k h := by
    have hpos := (original_old_front_weighted_tails_all hn hk hkn hh hH).1
    exact div_pos hpos.1 hpos.2
  have each (i : Fin H) : ∃ f ∈ Set.Ioo ((7/8:ℝ)*u i) ((9/8:ℝ)*u i),
      P.eval (-f) = 0 ∧ 0 < (-1:ℝ)^(i.val+2)*Q.eval (-f) := by
    let h := i.val+1
    let G := C (n:ℝ)*X+(1-X)*C ((h:ℝ)+1)
    have ht := original_exterior_coefficient_tests_all hn hk hkn (Nat.succ_pos i.val) i.isLt hnear
    exact signed_root_of_front_coefficients P Q G ht.1.1 ht.1.2 ht.2.1 ht.2.2
  choose f hf using each
  refine ⟨f, ?_, ?_⟩
  · intro i j hij
    have hord := exterior_scales_ordered (u:=originalExteriorScale n k) (H:=H)
      center_pos (fun _ hh hH => original_front_adjacent_gap_all hn hk hkn hh hH)
      (Nat.succ_pos i.val) (Nat.succ_lt_succ (show i.val < j.val from hij)) j.isLt
    exact (hf i).1.2.trans (hord.trans_lt (hf j).1.1)
  · intro i
    have hu := center_pos (i.val+1) (Nat.succ_pos _) i.isLt
    have hpos : 0 < (7/8:ℝ)*u i := mul_pos (by norm_num) hu
    have hs := original_front_scale_cap_all hn hk hkn (Nat.succ_pos i.val) i.isLt
    have hcap : (9/8:ℝ)*u i ≤ (459/40:ℝ)*((H:ℝ)/((H:ℝ)+1))^n := by
      have hc : (9/8:ℝ)*(51/5)=459/40 := by norm_num
      simpa only [←mul_assoc,hc] using mul_le_mul_of_nonneg_left hs (by norm_num : (0:ℝ) ≤ 9/8)
    exact ⟨(hf i).1,hpos.trans (hf i).1.1,(hf i).1.2.le.trans hcap,(hf i).2⟩

/-- Bounded-aspect middle signs start at integer sample H+1, strictly after
the final exterior root modulus. -/
theorem original_exterior_roots_before_integer_seam {n k : ℕ}
    (hn : 10000 ≤ n) (hk : 2 ≤ k) (hkn : k ≤ n)
    (hnear : ∀ j ≤ ⌊sqrt (n:ℝ)/2⌋₊,
      |(originalFrontLag n k).coeff j| ≤ (8/25)*|(enumerator n k).coeff j|) :
    ∃ f : Fin (uniformJoinRank n) → ℝ, StrictMono f ∧ ∀ i,
      0 < f i ∧ f i < exp (-exteriorIntegerSeamLog n) ∧
      (enumerator n k).eval (-f i) = 0 ∧
      0 < (-1:ℝ)^(i.val+2)*(enumerator (n+1) k).eval (-f i) := by
  obtain ⟨f,hmono,hf⟩ := original_exterior_root_witnesses_all hn hk hkn hnear
  refine ⟨f,hmono,?_⟩
  intro i
  obtain ⟨_,hp,hu,hzero,hsign⟩ := hf i
  exact ⟨hp,hu.trans_lt (exterior_cap_before_integer_seam hn),hzero,hsign⟩

#print axioms original_exterior_coefficient_tests_all
#print axioms original_exterior_root_witnesses_all
#print axioms original_exterior_roots_before_integer_seam
end RepositoryQuotientAudit
