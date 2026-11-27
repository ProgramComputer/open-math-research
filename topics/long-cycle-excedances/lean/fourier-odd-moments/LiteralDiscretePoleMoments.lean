import DiscretePoleEnvelope
import NumeratorLogDefinitions
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances

open scoped BigOperators Real

theorem literal_pole_norm_sq (s : ℝ) (l : ℤ) :
    ‖numeratorPole s l‖^2 = s^2+((2*(l:ℝ)+1)*π)^2 := by
  rw [Complex.sq_norm]
  dsimp only [numeratorPole]
  simp [Complex.normSq_apply,Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,pow_two]

private theorem principal_radius_positive (s : ℝ) : 0 < numeratorRadius s :=
  Real.sqrt_pos.2 (by positivity)

private theorem literal_pole_principal_norm (s : ℝ) :
    ‖numeratorPole s 0‖ = numeratorRadius s := by
  apply (pow_left_inj₀ (norm_nonneg _) (principal_radius_positive s).le (by norm_num : 2 ≠ 0)).mp
  rw [literal_pole_norm_sq,show (numeratorRadius s)^2 = s^2+π^2 from Real.sq_sqrt (by positivity)]
  norm_num

private theorem literal_pole_reflection (s : ℝ) (i : ℕ) :
    ‖numeratorPole s (-((i:ℤ)+1))‖ = ‖numeratorPole s i‖ := by
  apply (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) (by norm_num : 2 ≠ 0)).mp
  rw [literal_pole_norm_sq,literal_pole_norm_sq]
  push_cast
  ring

private theorem literal_normalized_pole_square (s : ℝ) (l : ℤ) :
    (numeratorRadius s/‖numeratorPole s l‖)^2 =
      (1+((2*(l:ℝ)+1)^2-1)*(π/numeratorRadius s)^2)⁻¹ := by
  have hr := principal_radius_positive s
  have hrs : (numeratorRadius s)^2 = s^2+π^2 := Real.sq_sqrt (by positivity)
  rw [← inv_div, inv_pow]
  congr 1
  rw [div_pow,literal_pole_norm_sq,div_pow]
  field_simp [hr.ne']
  linear_combination -hrs

/-- The positive pole with index i+1 has label 2i+3, and satisfies the
natural-power decay bound used in the two signed moments. -/
theorem literal_discrete_pole_decay {k : ℕ} (hk : 100 ≤ k) {x : ℝ}
    (hx : 44 ≤ x) (s : ℝ) (hsize : 1 ≤ x*(k:ℝ)*(π/numeratorRadius s)^2)
    (i : ℕ) :
    (numeratorRadius s/‖numeratorPole s ((i+1:ℕ):ℤ)‖)^(k-1) ≤
      discretePoleWeight (5*x) (discretePoleHeight i) := by
  have hp : 3 ≤ discretePoleHeight i := by
    unfold discretePoleHeight
    linarith only [Nat.cast_nonneg (α:=ℝ) i]
  refine discrete_pole_decay hk hx hsize hp
    (div_nonneg (principal_radius_positive s).le (norm_nonneg _)) ?_
  rw [literal_normalized_pole_square]
  have he : 2*(((i+1:ℕ):ℤ):ℝ)+1 = discretePoleHeight i := by
    unfold discretePoleHeight
    push_cast
    ring
  rw [he]

private theorem reflected_odd_sum {f : ℤ → ℝ} {M : ℝ}
    (hnon : ∀ l, 0 ≤ f l) (hzero : f 0 = 1)
    (hreflect : ∀ i : ℕ, f (-((i:ℤ)+1)) = f i)
    (hprefix : ∀ N : ℕ, (∑ i ∈ Finset.range N, f ((i+1:ℕ):ℤ)) ≤ M) :
    Summable f ∧ (∑' l, f l) ≤ 2+2*M := by
  have hnon' (i : ℕ) : 0 ≤ f ((i+1:ℕ):ℤ) := hnon _
  have hshift := summable_of_sum_range_le hnon' hprefix
  have hpos : Summable fun i : ℕ => f i := (summable_nat_add_iff 1).1 hshift
  have hneg : Summable fun i : ℕ => f (-((i:ℤ)+1)) := by
    simp_rw [hreflect]
    exact hpos
  refine ⟨hpos.of_nat_of_neg_add_one hneg, ?_⟩
  rw [tsum_of_nat_of_neg_add_one hpos hneg]
  simp_rw [hreflect]
  rw [hpos.tsum_eq_zero_add]
  simp only [Nat.cast_zero,hzero]
  have h := Real.tsum_le_of_sum_range_le hnon' hprefix
  linarith only [h]

/-- The two complete signed odd-pole moments at cutoff k-1. The principal
poles are included, and both series converge absolutely. -/
theorem literal_discrete_pole_moments {k : ℕ} (hk : 100 ≤ k) {x : ℝ}
    (hx : 44 ≤ x) (s : ℝ) (hsize : 1 ≤ x*(k:ℝ)*(π/numeratorRadius s)^2) :
    let f : ℤ → ℝ := fun l => (numeratorRadius s/‖numeratorPole s l‖)^(k-1)
    let g : ℤ → ℝ := fun l => |2*(l:ℝ)+1| * f l
    Summable f ∧ Summable g ∧ (∑' l, f l) ≤ 3*Real.sqrt x ∧ (∑' l, g l) ≤ 4*x := by
  let f : ℤ → ℝ := fun l => (numeratorRadius s/‖numeratorPole s l‖)^(k-1)
  let g : ℤ → ℝ := fun l => |2*(l:ℝ)+1| * f l
  let B := 5*x
  let L := Real.sqrt (B/3)
  have hx0 : 0 < x := by linarith
  have hB : 0 < B := by dsimp [B]; positivity
  have hL : 0 < L := Real.sqrt_pos.2 (by positivity)
  have hBL : B = 3*L^2 := by
    change B = 3*(Real.sqrt (B/3))^2
    rw [Real.sq_sqrt (by positivity)]
    ring
  have hL8 : 8 ≤ L := by
    apply Real.le_sqrt_of_sq_le
    change (8:ℝ)^2 ≤ 5*x/3
    linarith only [hx]
  have hnon (l : ℤ) : 0 ≤ f l :=
    pow_nonneg (div_nonneg (principal_radius_positive s).le (norm_nonneg _)) _
  have hgnon (l : ℤ) : 0 ≤ g l := mul_nonneg (abs_nonneg _) (hnon l)
  have hf0 : f 0 = 1 := by
    unfold f
    rw [literal_pole_principal_norm,div_self (principal_radius_positive s).ne',one_pow]
  have hg0 : g 0 = 1 := by norm_num [g,hf0]
  have hfreflect (i : ℕ) : f (-((i:ℤ)+1)) = f i := by
    unfold f
    rw [literal_pole_reflection]
  have hgreflect (i : ℕ) : g (-((i:ℤ)+1)) = g i := by
    unfold g
    rw [hfreflect]
    have he : 2*((-((i:ℤ)+1):ℤ):ℝ)+1 = -(2*(i:ℝ)+1) := by push_cast; ring
    rw [he,abs_neg,Int.cast_natCast]
  have hdom (i : ℕ) : f ((i+1:ℕ):ℤ) ≤ discretePoleWeight B (discretePoleHeight i) :=
    literal_discrete_pole_decay hk hx s hsize i
  have hgdom (i : ℕ) : g ((i+1:ℕ):ℤ) ≤ discretePoleHeight i*discretePoleWeight B (discretePoleHeight i) := by
    have hlabel : 2*(((i+1:ℕ):ℤ):ℝ)+1 = discretePoleHeight i := by
      unfold discretePoleHeight
      push_cast
      ring
    have hlabel0 : 0 ≤ discretePoleHeight i := by unfold discretePoleHeight; positivity
    unfold g
    rw [hlabel,abs_of_nonneg hlabel0]
    exact mul_le_mul_of_nonneg_left (hdom i) hlabel0
  have hfbound (N : ℕ) : (∑ i ∈ Finset.range N, f ((i+1:ℕ):ℤ)) ≤
      ((9/4)*L^2/(L+1))/2 := by
    have hh := discrete_pole_unweighted_prefix hL N
    rw [← hBL] at hh
    have h := Finset.sum_le_sum (s:=Finset.range N) (fun i _ => hdom i)
    linarith only [h,hh]
  have hgbound (N : ℕ) :
      (∑ i ∈ Finset.range N, g ((i+1:ℕ):ℤ)) ≤ (3/8)*B :=
    (Finset.sum_le_sum (fun i _ => hgdom i)).trans (discrete_pole_weighted_prefix hB N)
  have hf := reflected_odd_sum hnon hf0 hfreflect hfbound
  have hg := reflected_odd_sum hgnon hg0 hgreflect hgbound
  have hlast : 2+((9/4)*L^2/(L+1)) ≤ (9/4)*L := by
    apply (le_of_mul_le_mul_right _ (by positivity : 0 < L+1))
    rw [add_mul,div_mul_cancel₀ _ (by positivity : 0 < L+1).ne']
    nlinarith only [hL8]
  have hsqrt : (9/4)*L ≤ 3*Real.sqrt x := by
    apply le_of_sq_le_sq _ (by positivity)
    rw [mul_pow,mul_pow,Real.sq_sqrt hx0.le]
    dsimp only [B] at hBL
    linarith only [hBL,hx]
  refine ⟨hf.1,hg.1,?_,?_⟩
  · linarith only [hf.2,hlast,hsqrt]
  · dsimp only [B] at hg
    linarith only [hg.2,hx]

/-- The same signed budgets in row-size coordinates, with x=n/k. This is
the form used by the actual Fourier coefficient bounds. -/
theorem literal_discrete_pole_moments_of_size {n k : ℕ} (hk : 100 ≤ k)
    (hx : 44 ≤ (n:ℝ)/k) (s : ℝ) (hsize : 1 ≤ (n:ℝ)*(π/numeratorRadius s)^2) :
    let f : ℤ → ℝ := fun l => (numeratorRadius s/‖numeratorPole s l‖)^(k-1)
    let g : ℤ → ℝ := fun l => |2*(l:ℝ)+1| * f l
    Summable f ∧ Summable g ∧
      (∑' l, f l) ≤ 3*Real.sqrt ((n:ℝ)/k) ∧ (∑' l, g l) ≤ 4*((n:ℝ)/k) := by
  have hk0 : (k:ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  apply literal_discrete_pole_moments hk hx s
  rwa [div_mul_cancel₀ _ hk0]

/-- The form used for the original row kernel, with its externally supplied
principal radius and complex pole ratios. -/
theorem literal_discrete_pole_norm_moments {n k : ℕ} (hk : 100 ≤ k)
    (hx : 44 ≤ (n:ℝ)/k) {s r : ℝ} (hr : 0 < r) (hr2 : r^2 = s^2+π^2)
    (hsize : 1 ≤ (n:ℝ)*(π/r)^2) :
    let f : ℤ → ℝ := fun l => ‖(r:ℂ)/numeratorPole s l‖^(k-1)
    let g : ℤ → ℝ := fun l => |2*(l:ℝ)+1| * f l
    Summable f ∧ Summable g ∧
      (∑' l, f l) ≤ 3*Real.sqrt ((n:ℝ)/k) ∧ (∑' l, g l) ≤ 4*((n:ℝ)/k) := by
  have he : r = numeratorRadius s := by
    apply (pow_left_inj₀ hr.le (principal_radius_positive s).le (by norm_num : 2 ≠ 0)).mp
    exact hr2.trans (Real.sq_sqrt (show 0 ≤ s^2+π^2 by positivity)).symm
  have h := literal_discrete_pole_moments_of_size hk hx s (he ▸ hsize)
  rw [← he] at h
  simpa only [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr] using h

#print axioms literal_discrete_pole_norm_moments
#print axioms literal_pole_norm_sq
#print axioms literal_discrete_pole_decay
#print axioms literal_discrete_pole_moments
#print axioms literal_discrete_pole_moments_of_size
end OpenMathResearch.LongCycleExcedances
