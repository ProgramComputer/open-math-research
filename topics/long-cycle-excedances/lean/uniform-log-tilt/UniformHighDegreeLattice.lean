import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

noncomputable section

namespace OpenMathResearch.LongCycleExcedances
open Finset

private theorem bernoulli_nat (u : ℝ) (hu : 0 ≤ 1+u) (m : ℕ) :
    1 + (m : ℝ) * u ≤ (1 + u)^m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Nat.cast_succ]
    calc
      _ ≤ (1 + (m : ℝ)*u)*(1+u) := by
        nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) m) (sq_nonneg u)]
      _ ≤ _ := mul_le_mul_of_nonneg_right ih hu

private theorem high_degree_pole_entry {S q h : ℝ} {ell : ℕ}
    (hel : 7 ≤ ell) (hscale : (1 : ℝ)/2 ≤ ell*S^2)
    (hh : 0 < h) (hq : 0 ≤ q)
    (hgeometry : q^2*(1 + 4*h*(h+1)*S^2) ≤ 1) :
    q^ell ≤ (7/6)/(h*(h+1)) := by
  let m := ell/2
  let u : ℝ := 4*h*(h+1)*S^2
  have hu : 0 ≤ u := by positivity
  have hb : 0 < 1+u := by positivity
  have hsc : (3:ℝ)/14 ≤ (m:ℝ)*S^2 := by
    have hm : 3*(ell:ℝ) ≤ 7*(m:ℝ) := by
      exact_mod_cast (show 3*ell ≤ 7*(ell/2) by omega)
    nlinarith only [hscale, mul_le_mul_of_nonneg_right hm (sq_nonneg S)]
  have hs : q^2 ≤ 1/(1+u) := (le_div_iff₀ hb).2 hgeometry
  have hq₁ : q ≤ 1 := by
    have he : 1/(1+u) ≤ 1 := (div_le_iff₀ hb).2 (by linarith)
    exact le_of_sq_le_sq (by simpa using hs.trans he) (by norm_num)
  have hpow : q^ell ≤ ((1+u)^m)⁻¹ := by
    have h1 : q^ell ≤ q^(2*m) := by
      calc
        q^ell = q^(2*m)*q^(ell%2) := by
          rw [← pow_add]
          congr 1
          dsimp [m]
          omega
        _ ≤ _ := mul_le_of_le_one_right (pow_nonneg hq _) (pow_le_one₀ hq hq₁)
    rw [pow_mul] at h1
    have h2 := pow_le_pow_left₀ (sq_nonneg q) hs m
    rw [one_div_pow] at h2
    simpa only [one_div] using h1.trans h2
  have hhprod : 0 < h*(h+1) := by positivity
  have hmin : (6/7:ℝ)*(h*(h+1)) ≤ (1+u)^m := by
    apply le_trans _ (bernoulli_nat u hb.le m)
    have hv := mul_le_mul_of_nonneg_left hsc hhprod.le
    dsimp only [u]
    nlinarith only [hv]
  apply hpow.trans
  rw [← one_div]
  apply (div_le_div_iff₀ (pow_pos hb _) hhprod).2
  nlinarith only [hmin]

private theorem pole_majorant_eq (B : ℝ) (j : ℕ) :
    B/(((j:ℝ)+1)*((j:ℝ)+2)) =
      B*(1/((j:ℝ)+1) - 1/((j:ℝ)+2)) := by
  have h₁ : (j:ℝ)+1 ≠ 0 := (by positivity : 0 < (j:ℝ)+1).ne'
  have h₂ : (j:ℝ)+2 ≠ 0 := (by positivity : 0 < (j:ℝ)+2).ne'
  field_simp [h₁, h₂]
  ring

private theorem far_partial_bound (B : ℝ) (f : ℕ → ℝ)
    (hf : ∀ j : ℕ, f j ≤ B/(((j:ℝ)+1)*((j:ℝ)+2))) (N : ℕ) :
    (∑ j ∈ range N, f j) ≤ B*(1-1/((N:ℝ)+1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, Nat.cast_succ]
    have h := hf N
    rw [pole_majorant_eq] at h
    rw [show (N:ℝ)+1+1=(N:ℝ)+2 by ring]
    linarith

private theorem paired_pole_sum_bound {ell : ℕ} {B : ℝ} (hB : 0 ≤ B) (ρ : ℤ → ℝ)
    (hρ : ∀ l : ℤ, 0 ≤ ρ l) (hzero : ρ 0 = 1)
    (hsym : ∀ j : ℕ, ρ (-((j:ℤ)+1)) = ρ (j:ℤ))
    (hfar : ∀ j : ℕ, (ρ ((j+1:ℕ):ℤ))^ell ≤ B/(((j:ℝ)+1)*((j:ℝ)+2))) :
    Summable (fun l : ℤ => (ρ l)^ell) ∧
      (∑' l : ℤ, (ρ l)^ell) ≤ 2+2*B := by
  let a (j : ℕ) : ℝ := (ρ ((j:ℤ)+1))^ell
  have ha (j : ℕ) : 0 ≤ a j := pow_nonneg (hρ _) _
  have hb : ∀ j : ℕ, a j ≤ B/(((j:ℝ)+1)*((j:ℝ)+2)) := by
    simpa only [a, Nat.cast_succ] using hfar
  have hp (N : ℕ) : (∑ j ∈ range N, a j) ≤ B := by
    have h := far_partial_bound B a hb N
    exact h.trans (mul_le_of_le_one_right hB (sub_le_self _ (by positivity)))
  have hsum : Summable a := summable_of_sum_range_le ha hp
  have htot : (∑' j : ℕ, a j) ≤ B := Real.tsum_le_of_sum_range_le ha hp
  let b (j : ℕ) : ℝ := (ρ (j:ℤ))^ell
  have hpos : Summable b := (summable_nat_add_iff 1).mp (by
      simpa only [b, a, Nat.cast_add, Nat.cast_one] using hsum)
  have hneg : Summable fun j : ℕ => (ρ (-((j:ℤ)+1)))^ell := by simpa only [hsym] using hpos
  constructor
  · exact Summable.of_nat_of_neg_add_one (f := fun l : ℤ => (ρ l)^ell) hpos hneg
  · rw [tsum_of_nat_of_neg_add_one (f := fun l : ℤ => (ρ l)^ell) hpos hneg]
    simp only [hsym]
    change (∑' j : ℕ, b j)+(∑' j : ℕ, b j) ≤ _
    rw [hpos.tsum_eq_zero_add]
    have hfirst : b 0 = 1 := by simp [b, hzero]
    rw [hfirst]
    have htail : (∑' j : ℕ, b (j+1)) = ∑' j : ℕ, a j := by simp [a,b,Nat.cast_add]
    rw [htail]
    linarith

/-- The two nearest poles contribute two. The remaining two tails have total
mass at most 7/3 as soon as the degree exceeds six and ell*S² ≥ 1/2. -/
theorem uniform_high_degree_lattice {S : ℝ} {ell : ℕ} (hel : 7 ≤ ell)
    (hscale : (1:ℝ)/2 ≤ ell*S^2) (ρ : ℤ → ℝ)
    (hρ : ∀ l : ℤ, 0 ≤ ρ l) (hzero : ρ 0 = 1)
    (hsym : ∀ j : ℕ, ρ (-((j:ℤ)+1)) = ρ (j:ℤ))
    (hgeometry : ∀ j : ℕ,
      (ρ ((j+1:ℕ):ℤ))^2*(1+4*((j:ℝ)+1)*((j:ℝ)+2)*S^2) ≤ 1) :
    Summable (fun l : ℤ => (ρ l)^ell) ∧
      (∑' l : ℤ, (ρ l)^ell) ≤ 13/3 := by
  have hb (j : ℕ) : (ρ ((j+1:ℕ):ℤ))^ell ≤ (7/6:ℝ)/(((j:ℝ)+1)*((j:ℝ)+2)) := by
    have h := high_degree_pole_entry hel hscale (by positivity : 0 < (j:ℝ)+1)
      (hρ ((j+1:ℕ):ℤ)) (by rw [show (j:ℝ)+1+1=(j:ℝ)+2 by ring]; exact hgeometry j)
    rwa [show (j:ℝ)+1+1=(j:ℝ)+2 by ring] at h
  obtain ⟨hs,h⟩ := paired_pole_sum_bound (by norm_num) ρ hρ hzero hsym hb
  exact ⟨hs, h.trans (by norm_num)⟩

/-- For any degree at least two, the paired lattice is bounded by its square
majorant. This is effective when the real coordinate is bounded. -/
theorem square_majorized_lattice {S : ℝ} {ell : ℕ} (hS : 0 < S) (hel : 2 ≤ ell)
    (ρ : ℤ → ℝ) (hρ : ∀ l : ℤ, 0 ≤ ρ l) (hzero : ρ 0 = 1)
    (hsym : ∀ j : ℕ, ρ (-((j:ℤ)+1)) = ρ (j:ℤ))
    (hgeometry : ∀ j : ℕ,
      (ρ ((j+1:ℕ):ℤ))^2*(1+4*((j:ℝ)+1)*((j:ℝ)+2)*S^2) ≤ 1) :
    Summable (fun l : ℤ => (ρ l)^ell) ∧
      (∑' l : ℤ, (ρ l)^ell) ≤ 2+1/(2*S^2) := by
  let B : ℝ := 1/(4*S^2)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hfar (j : ℕ) : (ρ ((j+1:ℕ):ℤ))^ell ≤ B/(((j:ℝ)+1)*((j:ℝ)+2)) := by
    let q := ρ ((j+1:ℕ):ℤ)
    let v : ℝ := ((j:ℝ)+1)*((j:ℝ)+2)
    let u : ℝ := 4*v*S^2
    have hq : 0 ≤ q := hρ _
    have hv : 0 < v := by dsimp [v]; positivity
    have hu : 0 ≤ u := by dsimp only [u]; positivity
    have hg : q^2*(1+u) ≤ 1 := by
      convert hgeometry j using 1
      dsimp only [q,u,v]
      ring
    have hq₂ : q^2 ≤ 1 := by nlinarith only [hg, mul_nonneg (sq_nonneg q) hu]
    have hq₁ : q ≤ 1 := le_of_sq_le_sq (by simpa using hq₂) (by norm_num)
    have he : q^ell ≤ q^2 := by
      calc
        q^ell = q^2*q^(ell-2) := by rw [← pow_add, Nat.add_sub_of_le hel]
        _ ≤ _ := mul_le_of_le_one_right (sq_nonneg q) (pow_le_one₀ hq hq₁)
    have h := (show q^2*u ≤ 1 by linarith only [hg, sq_nonneg q])
    apply he.trans
    apply (le_div_iff₀ hv).2
    dsimp only [B]
    apply (le_div_iff₀ (by positivity : (0:ℝ)<4*S^2)).2
    dsimp only [u] at h
    nlinarith only [h]
  obtain ⟨hs, h⟩ := paired_pole_sum_bound hB ρ hρ hzero hsym hfar
  refine ⟨hs, h.trans (le_of_eq ?_)⟩
  dsimp only [B]
  field_simp [hS.ne']
  ring

/-- A uniform elementary bound for the inflation factor of the contour radius. -/
theorem uniform_contour_factor {k ell : ℕ} (hell : ell < k) :
    (1+1/(50*(k:ℝ)))^ell ≤ 50/49 := by
  let a : ℝ := 1/(50*(k:ℝ))
  have hk : 0 < (k:ℝ) := by exact_mod_cast (show 0<k by omega)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have ha' : a ≤ 1/50 := by
    have hk1 : 1 ≤ (k:ℝ) := by exact_mod_cast (show 1≤k by omega)
    dsimp [a]
    apply (div_le_div_iff₀ (by positivity : 0 < 50*(k:ℝ)) (by norm_num : (0:ℝ)<50)).2
    linarith
  have hsum : (ell:ℝ)*a ≤ 1/50 := by
    have hl : (ell:ℝ) ≤ k := by exact_mod_cast hell.le
    have hk' : (k:ℝ)*a = 1/50 := by dsimp [a]; field_simp; ring
    exact (mul_le_mul_of_nonneg_right hl ha).trans_eq hk'
  have hlocal : (1+a)^ell*(1-(ell:ℝ)*a) ≤ 1 := by
    have hB := bernoulli_nat (-a) (by linarith) ell
    have hpair : 0 ≤ (1+a)*(1+-a) := mul_nonneg (by positivity) (by linarith)
    have hpair' : (1+a)*(1+-a) ≤ 1 := by nlinarith [sq_nonneg a]
    calc
      _ ≤ (1+a)^ell*(1+-a)^ell := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa only [mul_neg, ← sub_eq_add_neg] using hB
      _ = ((1+a)*(1+-a))^ell := by rw [mul_pow]
      _ ≤ 1 := pow_le_one₀ hpair hpair'
  have hden : 0 < 1-(ell:ℝ)*a := by linarith
  exact ((le_div_iff₀ hden).2 hlocal).trans
    ((div_le_div_iff₀ hden (by norm_num : (0:ℝ)<49)).2 (by linarith))

/-- The inflated high-degree multiplier stays below the coefficient budget. -/
theorem uniform_high_degree_contour_factor {k ell : ℕ} (hell : ell < k)
    {M : ℝ} (hM : M ≤ 13/3) :
    (1+1/(50*(k:ℝ)))^ell * M ≤ 650/147 := by
  calc
    _ ≤ (1+1/(50*(k:ℝ)))^ell*(13/3) := mul_le_mul_of_nonneg_left hM (by positivity)
    _ ≤ (50/49)*(13/3) := mul_le_mul_of_nonneg_right (uniform_contour_factor hell) (by norm_num)
    _ = _ := by norm_num

#print axioms uniform_high_degree_lattice
#print axioms square_majorized_lattice
#print axioms uniform_contour_factor
#print axioms uniform_high_degree_contour_factor
end OpenMathResearch.LongCycleExcedances
