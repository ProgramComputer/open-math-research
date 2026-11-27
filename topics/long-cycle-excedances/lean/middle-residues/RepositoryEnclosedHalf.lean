import RepositoryNestedRow
import HighAngleLattice
import Mathlib.Algebra.Order.Floor.Semiring

noncomputable section
namespace RepositoryQuotientAudit
open Finset OpenMathResearch.LongCycleExcedances
open scoped Real

/-- The finite positive nonprincipal part of the enclosed pole lattice.
The range bound is deliberately loose. The filter is the exact enclosure. -/
def positiveEnclosedPoles (x R₀ : ℝ) : Finset ℕ := by
  classical
  exact (range (⌈R₀/Real.pi⌉₊+1)).filter
    (fun i => ‖coherentPole x ((i+1:ℕ):ℤ)‖ ≤ R₀)

private theorem pole_not_enclosed_above_range (x R₀ : ℝ) {i : ℕ}
    (hi : i ∉ range (⌈R₀/Real.pi⌉₊+1)) : R₀ < ‖coherentPole x (i:ℤ)‖ := by
  have hceil := Nat.le_ceil (R₀/Real.pi)
  have hk : (⌈R₀/Real.pi⌉₊:ℕ) < i := by
    have : ¬ i < ⌈R₀/Real.pi⌉₊+1 := fun h => hi (mem_range.mpr h)
    omega
  have hki : ((⌈R₀/Real.pi⌉₊:ℕ):ℝ) < (i:ℝ) := by exact_mod_cast hk
  have hlo : R₀ < (i:ℝ)*Real.pi := (div_lt_iff₀ Real.pi_pos).mp (hceil.trans_lt hki)
  have h := Complex.abs_im_le_norm (coherentPole x (i:ℤ))
  rw [coherentPole_im,Int.cast_natCast,abs_of_nonneg (by positivity)] at h
  exact hlo.trans_le ((mul_le_mul_of_nonneg_right (by linarith [Nat.cast_nonneg (α := ℝ) i])
    Real.pi_pos.le).trans h)

theorem mem_positiveEnclosedPoles {x R₀ : ℝ} {i : ℕ} :
    i ∈ positiveEnclosedPoles x R₀ ↔ ‖coherentPole x ((i+1:ℕ):ℤ)‖ ≤ R₀ := by
  classical
  unfold positiveEnclosedPoles
  rw [mem_filter]
  constructor
  · exact And.right
  · intro h
    refine ⟨?_,h⟩
    by_contra hi
    have hi' : i+1 ∉ range (⌈R₀/Real.pi⌉₊+1) := by
      simp only [mem_range] at hi ⊢
      omega
    exact (not_le.mpr (pole_not_enclosed_above_range x R₀ hi')) h

/-- The real half of the signed-lattice approximant is exactly the principal
mode plus the finite sum over enclosed positive nonprincipal poles. -/
theorem nested_approximation_positive_half {k : ℕ} (hk : 2 ≤ k)
    (n : ℕ) (x R₀ : ℝ) (hR₀ : ‖coherentPole x 0‖ ≤ R₀) :
    let r := ‖coherentPole x 0‖
    let T := coherentTilt k (-Real.exp (-x))
    let b (l : ℤ) := ((r:ℂ)/coherentPole x l)^(n+1)*seriesValue T (coherentPole x l)
    let a (l : ℤ) := if ‖coherentPole x l‖ ≤ R₀ then b l else 0
    (∑' l, a l).re/2 = (b 0).re +
      ∑ i ∈ positiveEnclosedPoles x R₀, (b ((i+1:ℕ):ℤ)).re := by
  dsimp only
  let r := ‖coherentPole x 0‖
  let T := coherentTilt k (-Real.exp (-x))
  let b (l : ℤ) := ((r:ℂ)/coherentPole x l)^(n+1)*seriesValue T (coherentPole x l)
  let a (l : ℤ) := if ‖coherentPole x l‖ ≤ R₀ then b l else 0
  have hs : Summable fun i : ℕ => ‖a (i:ℤ)‖ := by
    apply summable_of_ne_finset_zero (s := range (⌈R₀/Real.pi⌉₊+1))
    intro i hi
    simp only [a,if_neg (not_le.mpr (pole_not_enclosed_above_range x R₀ hi)),norm_zero]
  have he (w : ℂ) : seriesValue T ((starRingEnd ℂ) w) = (starRingEnd ℂ) (seriesValue T w) := by
    rw [seriesValue_original_coherentTilt hk,seriesValue_original_coherentTilt hk, ←Complex.exp_conj]
    simp only [map_sum,map_mul,map_pow,Complex.conj_ofReal]
  have hconj (l : ℤ) : a (-(l+1)) = (starRingEnd ℂ) (a l) := by
    dsimp only [a,b]
    rw [coherentPole_conj,Complex.norm_conj]
    split_ifs
    · rw [map_mul,map_pow,map_div₀,Complex.conj_ofReal,he]
    · rw [map_zero]
  have hpair := conjugate_lattice_real a hs hconj
  have hts : (∑' i : ℕ, a ((i+1:ℕ):ℤ)) =
      ∑ i ∈ positiveEnclosedPoles x R₀, b ((i+1:ℕ):ℤ) := by
    calc
      _ = ∑ i ∈ positiveEnclosedPoles x R₀, a ((i+1:ℕ):ℤ) := by
        apply tsum_eq_sum
        intro i hi
        simp only [a,if_neg (fun h => hi (mem_positiveEnclosedPoles.mpr h))]
      _ = _ := by
        apply sum_congr rfl
        intro i hi
        exact if_pos (mem_positiveEnclosedPoles.mp hi)
  have hprincipal : a 0 = b 0 := if_pos hR₀
  change (∑' l, a l).re/2 = (b 0).re + _
  rw [hpair,hprincipal,hts,Complex.re_sum]
  ring

/-- The actual normalized middle row with one principal term and a finite
positive enclosed-pole sum. -/
theorem original_middle_nested_row_error_positive_half {n k : ℕ} (hk : 7 ≤ k)
    {x : ℝ} (hx : 0 ≤ x)
    (hm : 1 ≤ (n:ℝ)*(π/‖coherentPole x 0‖)^2) :
    let r := ‖coherentPole x 0‖
    let R₁ := r*(1+1/(100*(k:ℝ)))
    let R₀ := r*(1+3/(200*(k:ℝ)))
    let Rstar := r*(1+1/(50*(k:ℝ)))
    let A := Real.exp (6+9*Real.log k)
    let t := -Real.exp (-x)
    let T := coherentTilt k t
    let b (l : ℤ) := ((r:ℂ)/coherentPole x l)^(n+1)*seriesValue T (coherentPole x l)
    |r^(n+1)/2 * ((LongCycles.enumerator n k).eval t/((1-t)^(n+1)*n.factorial)) -
      ((b 0).re + ∑ i ∈ positiveEnclosedPoles x R₀, (b ((i+1:ℕ):ℤ)).re)| ≤
        ((200*(k:ℝ)+3)*(A*(r/R₁)^(n-1))*(2+(n:ℝ)/2) +
          r*A*(r/Rstar)^n)/2 := by
  dsimp only
  let r := ‖coherentPole x 0‖
  let R₀ := r*(1+3/(200*(k:ℝ)))
  have hr : 0 < r := coherentPole_near_pos x
  have hR₀ : r ≤ R₀ := by
    dsimp only [R₀]
    exact le_mul_of_one_le_right hr.le (le_add_of_nonneg_right (by positivity))
  have hp := nested_approximation_positive_half (by omega : 2 ≤ k) n x R₀ hR₀
  have he := (original_middle_nested_row_error hk hx hm).2
  rw [hp] at he
  exact he

/-- The finite positive minor approximants inherit the one-fifth bound
with the same pole weights used in the subsequent sign comparison. -/
theorem nested_enclosed_minor_mode_mass {n k : ℕ} (hk : 7 ≤ k)
    {x : ℝ} (hx : 0 ≤ x)
    (hm : 1 ≤ (n:ℝ)*(π/‖coherentPole x 0‖)^2) :
    let r := ‖coherentPole x 0‖
    let R₀ := r*(1+3/(200*(k:ℝ)))
    let T := coherentTilt k (-Real.exp (-x))
    let b (l : ℤ) := ((r:ℂ)/coherentPole x l)^(n+1)*seriesValue T (coherentPole x l)
    (∑ i ∈ positiveEnclosedPoles x R₀, (2*(i+1:ℕ)+1:ℝ)*‖b ((i+1:ℕ):ℤ)‖) ≤
      ‖seriesValue T (coherentPole x 0)‖/5 := by
  dsimp only
  let r := ‖coherentPole x 0‖
  let R₀ := r*(1+3/(200*(k:ℝ)))
  let T := coherentTilt k (-Real.exp (-x))
  let M := ‖seriesValue T (coherentPole x 0)‖
  let s := positiveEnclosedPoles x R₀
  have hr : 0 < r := coherentPole_near_pos x
  obtain ⟨_,_,hRs,_⟩ := fixed_nested_radius_budget hr (by omega : 0 < k)
  have hA : 0 < M := by
    have henc : r ≤ r*(1+1/(50*(k:ℝ))) :=
      le_mul_of_one_le_right hr.le (le_add_of_nonneg_right (by positivity))
    exact (Real.exp_pos _).trans_le ((original_uniform_tilt_envelope hk hx).2 _ henc)
  let f (i : ℕ) : ℝ :=
    let w := coherentPole x ((i+1:ℕ):ℤ)
    (2*(i+1:ℕ)+1:ℝ)*(r/‖w‖)^n*
      ‖seriesValue T w/seriesValue T (coherentPole x 0)‖
  have hMinor : (∑ i ∈ s, f i) ≤ 1/5 :=
    all_angle_enclosed_minor_poles_le_fifth hk hx hm s
      (fun i hi => (mem_positiveEnclosedPoles.mp hi).trans hRs.le)
  calc
    _ ≤ ∑ i ∈ s, f i*M := by
      apply sum_le_sum
      intro i _
      let w := coherentPole x ((i+1:ℕ):ℤ)
      let p : ℝ := (2*(i+1:ℕ)+1:ℝ)
      have hnear : r ≤ ‖w‖ := coherentPole_near_le x _
      have hW : 0 < ‖w‖ := hr.trans_le hnear
      have hpow := pow_le_pow_of_le_one (div_nonneg hr.le hW.le)
        ((div_le_one hW).2 hnear) (Nat.le_succ n)
      change p*‖((r:ℂ)/w)^(n+1)*seriesValue T w‖ ≤ f i*M
      rw [norm_mul,norm_pow,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]
      have he : f i*M = p*((r/‖w‖)^n*‖seriesValue T w‖) := by
        dsimp only [f, p]
        rw [norm_div,show ‖seriesValue T (coherentPole x 0)‖ = M by rfl]
        rw [mul_assoc, mul_assoc, div_mul_cancel₀ _ hA.ne']
      rw [he]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow (norm_nonneg _)) (by positivity)
    _ = (∑ i ∈ s, f i)*M := by rw [sum_mul]
    _ ≤ (1/5:ℝ)*M := mul_le_mul_of_nonneg_right hMinor hA.le
    _ = _ := by ring

#print axioms mem_positiveEnclosedPoles
#print axioms nested_approximation_positive_half
#print axioms original_middle_nested_row_error_positive_half
#print axioms nested_enclosed_minor_mode_mass
end RepositoryQuotientAudit
