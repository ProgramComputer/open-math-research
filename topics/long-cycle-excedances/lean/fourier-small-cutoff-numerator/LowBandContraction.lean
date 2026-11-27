import LowBandRadial
import NumeratorTaylorContraction

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open scoped BigOperators Real

private theorem inverse_sqrt_prefix (n : ℕ) :
    (∑ i ∈ Finset.range n, 1 / Real.sqrt ((i+2:ℕ):ℝ)) ≤ 2*(Real.sqrt ((n+1:ℕ):ℝ)-1) := by
  induction n with
  | zero => simp
  | succ n hn =>
    rw [Finset.sum_range_succ]
    have h0 : 0 < Real.sqrt ((n+2:ℕ):ℝ) := Real.sqrt_pos.2 (by positivity)
    have hmono : Real.sqrt ((n+1:ℕ):ℝ) ≤ Real.sqrt ((n+2:ℕ):ℝ) :=
      Real.sqrt_le_sqrt (by exact_mod_cast (show n+1 ≤ n+2 by omega))
    have hsq := Real.sq_sqrt (show 0 ≤ ((n+2:ℕ):ℝ) by positivity)
    have hsq' := Real.sq_sqrt (show 0 ≤ ((n+1:ℕ):ℝ) by positivity)
    have hterm : 1 / Real.sqrt ((n+2:ℕ):ℝ) ≤
        2 * (Real.sqrt ((n+2:ℕ):ℝ) - Real.sqrt ((n+1:ℕ):ℝ)) := by
      apply (div_le_iff₀ h0).2
      push_cast at hsq hsq' ⊢
      nlinarith only [hsq,hsq',sq_nonneg
        (Real.sqrt ((n:ℝ)+2) - Real.sqrt ((n:ℝ)+1))]
    change _ ≤ 2*(Real.sqrt ((n+2:ℕ):ℝ)-1)
    linarith only [hn,hterm]

private theorem moment_prefix {k : ℕ} (hk : 2 ≤ k) {S : ℝ} (hS : 0 < S) :
    (∑ i ∈ Finset.range (k-2), (2+9/(4*S*Real.sqrt ((i+2:ℕ):ℝ)))) ≤
      (k:ℝ)*(2+9/(2*S*Real.sqrt k)) := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hsqrt0 : 0 < Real.sqrt (k:ℝ) := Real.sqrt_pos.2 hk0
  have hsum := inverse_sqrt_prefix (k-2)
  have hsum' : (∑ i ∈ Finset.range (k-2), 1/Real.sqrt ((i+2:ℕ):ℝ)) ≤
      2 * Real.sqrt (k:ℝ) := by
    have hmono : Real.sqrt ((k-2+1:ℕ):ℝ) ≤ Real.sqrt (k:ℝ) :=
      Real.sqrt_le_sqrt (by exact_mod_cast (show k-2+1 ≤ k by omega))
    linarith only [hsum,hmono]
  have hcount : ((k-2:ℕ):ℝ) ≤ (k:ℝ) := by exact_mod_cast Nat.sub_le k 2
  calc
    _ = (2:ℝ)*((k-2:ℕ):ℝ) + (9/(4*S)) *
      (∑ i ∈ Finset.range (k-2), 1/Real.sqrt ((i+2:ℕ):ℝ)) := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        congr 1
        · ring
        · apply Finset.sum_congr rfl
          intro i _
          ring
    _ ≤ 2*(k:ℝ) + (9/(4*S)) * (2*Real.sqrt (k:ℝ)) :=
      add_le_add (mul_le_mul_of_nonneg_left hcount (by norm_num))
        (mul_le_mul_of_nonneg_left hsum' (by positivity))
    _ = _ := by
      field_simp [ne_of_gt hS, ne_of_gt hsqrt0]
      linear_combination (36*S) * Real.sq_sqrt hk0.le

private theorem low_band_radial_prefix {k : ℕ} (hk : 10 ≤ k)
    (c : ℕ → ℂ) {S R A : ℝ} (hS : 0 < S) (hA : 0 ≤ A)
    (hR : 1 ≤ R) {ξ : ℂ} (hξ : ‖ξ‖ = 1)
    (hc1 : ‖c 1‖ ≤ 4)
    (hc : ∀ j : ℕ, 2 ≤ j → ‖c j‖ ≤ (2+9/(4*S*Real.sqrt j))/(j:ℝ))
    (hA' : ∀ j : ℕ, j < k →
      R^j - (1-1/(k:ℝ))^j ≤ A*((j:ℝ)/k)) :
    ‖numeratorTaylor k c ((R:ℂ)*ξ) -
      numeratorTaylor k c (((1-1/(k:ℝ):ℝ):ℂ)*ξ)‖ ≤
      4*(R-(1-1/(k:ℝ))) + A*(2+9/(2*S*Real.sqrt k)) := by
  let ρ : ℝ := 1-1/(k:ℝ)
  have hk0 : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hkR : (10:ℝ) ≤ k := by exact_mod_cast hk
  have hu : 0 ≤ 1/(k:ℝ) := by positivity
  have hρ : 0 ≤ ρ := sub_nonneg.mpr ((div_le_one hk0).2 (by linarith))
  have hρR : ρ ≤ R := by dsimp only [ρ]; linarith only [hu,hR]
  let f : ℕ → ℂ := fun j => c j * (((R:ℂ)*ξ)^j-((ρ:ℂ)*ξ)^j)
  have hf (j : ℕ) : ‖f j‖ = ‖c j‖ * (R^j-ρ^j) := by
    have hpow : ρ^j ≤ R^j := pow_le_pow_left₀ hρ hρR j
    dsimp only [f]
    rw [norm_mul,mul_pow,mul_pow,← sub_mul,norm_mul,norm_pow,hξ,one_pow,mul_one,
      ← Complex.ofReal_pow,← Complex.ofReal_pow, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hpow)]
  have h2 : 2+(k-2) = k := by omega
  have heq : numeratorTaylor k c ((R:ℂ)*ξ)-numeratorTaylor k c ((ρ:ℂ)*ξ) =
      ∑ j ∈ Finset.range k, f j := by
    unfold numeratorTaylor
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    simp only [f, mul_sub]
  rw [heq]
  have hf1 : ‖f 1‖ ≤ 4*(R-ρ) := by
    rw [hf,pow_one,pow_one]
    exact mul_le_mul_of_nonneg_right hc1 (sub_nonneg.mpr hρR)
  have htail :
      (∑ i ∈ Finset.range (k-2), ‖f (2+i)‖) ≤ A*(2+9/(2*S*Real.sqrt k)) := by
    calc
      _ ≤ ∑ i ∈ Finset.range (k-2),
        (A/(k:ℝ))*(2+9/(4*S*Real.sqrt ((i+2:ℕ):ℝ))) := by
          apply Finset.sum_le_sum
          intro i hi
          have hj : 2+i < k := by have := Finset.mem_range.mp hi; omega
          have hj0 : (0:ℝ) < ((2+i:ℕ):ℝ) := by positivity
          rw [hf]
          change ‖c (2+i)‖ * (R^(2+i) - (1-1/(k:ℝ))^(2+i)) ≤ _
          have h := mul_le_mul (hc (2+i) (by omega)) (hA' (2+i) hj)
            (sub_nonneg.mpr (pow_le_pow_left₀ hρ hρR (2+i))) (by positivity)
          refine h.trans_eq ?_
          rw [Nat.add_comm 2 i]
          field_simp [ne_of_gt hj0, ne_of_gt hk0]
          ring
      _ = (A/(k:ℝ)) * (∑ i ∈ Finset.range (k-2),
        (2+9/(4*S*Real.sqrt ((i+2:ℕ):ℝ)))) := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := by
        calc
          _ ≤ (A/(k:ℝ))*((k:ℝ)*(2+9/(2*S*Real.sqrt k))) :=
            mul_le_mul_of_nonneg_left (moment_prefix (by omega) hS) (by positivity)
          _ = _ := by field_simp [ne_of_gt hk0]; ring
  calc
    ‖∑ j ∈ Finset.range k, f j‖ ≤ ∑ j ∈ Finset.range k, ‖f j‖ := norm_sum_le _ _
    _ = ‖f 1‖ + (∑ i ∈ Finset.range (k-2), ‖f (2+i)‖) := by
      conv_lhs => rw [← h2, Finset.sum_range_add]
      have hf0 : f 0 = 0 := by simp [f]
      simp [Finset.sum_range_succ', hf0]
    _ ≤ _ := add_le_add hf1 htail

private theorem low_band_taylor_tail {k : ℕ} (hk : 10 ≤ k)
    (c : ℕ → ℂ) {S : ℝ} (hS : 0 < S) {ξ : ℂ} (hξ : ‖ξ‖ = 1)
    (hc : ∀ j : ℕ, 2 ≤ j → ‖c j‖ ≤ (2+9/(4*S*Real.sqrt j))/(j:ℝ)) :
    let z : ℂ := ((1-1/(k:ℝ):ℝ):ℂ)*ξ
    ‖(∑' j, c j * z^j) - numeratorTaylor k c z‖ ≤
      (3/8)*(2+9/(4*S*Real.sqrt k)) := by
  let ρ : ℝ := 1-1/(k:ℝ)
  let z : ℂ := (ρ:ℂ)*ξ
  let q : ℝ := ρ
  let C : ℝ := 2+9/(4*S*Real.sqrt k)
  have hk0 : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hkR : (10:ℝ) ≤ k := by exact_mod_cast hk
  have hsqrt : 0 < Real.sqrt (k:ℝ) := Real.sqrt_pos.2 hk0
  have hρ : 0 ≤ ρ := sub_nonneg.mpr ((div_le_one hk0).2 (by linarith))
  have hq1 : q < 1 := by
    dsimp only [q,ρ]
    linarith [show (0:ℝ) < 1/(k:ℝ) by positivity]
  have hq0 : 0 ≤ q := hρ
  have hρq : ρ ≤ q := le_rfl
  have hz : ‖z‖ = ρ := by simp [z,norm_mul,hξ, Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hρ]
  have hqk : q^k ≤ Real.exp (-1) := by
    have ha : q ≤ Real.exp (-(1/(k:ℝ))) := by
      simpa only [q,ρ,sub_eq_add_neg,add_comm] using Real.add_one_le_exp (-(1/(k:ℝ)))
    have hh := pow_le_pow_left₀ hq0 ha k
    rw [← Real.exp_nat_mul] at hh
    have he : (k:ℝ)*(-(1/(k:ℝ))) = -1 := by field_simp [hk0.ne']
    rwa [he] at hh
  let f : ℕ → ℂ := fun j => c j * z^j
  let major : ℕ → ℝ := fun i => ((C/(k:ℝ))*Real.exp (-1)) * q^i
  have hm : Summable major := (summable_geometric_of_lt_one hq0 hq1).mul_left _
  have hdom (i : ℕ) : ‖f (i+k)‖ ≤ major i := by
    have hki : k ≤ i+k := by omega
    have hkiR : (k:ℝ) ≤ ((i+k:ℕ):ℝ) := by exact_mod_cast hki
    have hC : 0 ≤ C := by dsimp [C]; positivity
    have hbi : 0 < (4*S*Real.sqrt ((i+k:ℕ):ℝ)) := by positivity
    have hBs : Real.sqrt (k:ℝ) ≤ Real.sqrt ((i+k:ℕ):ℝ) := Real.sqrt_le_sqrt hkiR
    have hc' : ‖c (i+k)‖ ≤ C/(k:ℝ) := by
      apply (hc (i+k) (by omega)).trans
      have hdec : (9:ℝ)/(4*S*Real.sqrt ((i+k:ℕ):ℝ)) ≤ 9/(4*S*Real.sqrt k) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity)
          (mul_le_mul_of_nonneg_left hBs (by positivity))
      exact div_le_div₀ hC (add_le_add_left hdec 2) hk0 hkiR
    have hpow := pow_le_pow_left₀ hρ hρq (i+k)
    dsimp only [f,major]
    rw [norm_mul,norm_pow,hz]
    calc
      _ ≤ (C/(k:ℝ))*q^(i+k) := mul_le_mul hc' hpow (by positivity) (by positivity)
      _ ≤ _ := by
        rw [pow_add,mul_assoc]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [mul_comm (q^i)]
        exact mul_le_mul_of_nonneg_right hqk (pow_nonneg hq0 _)
  have hnorm : Summable (fun i => ‖f (i+k)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hdom hm
  have hSuf : Summable (fun i => f (i+k)) := hnorm.of_norm
  have hA : Summable f := (summable_nat_add_iff k).1 hSuf
  have hDecomp := hA.sum_add_tsum_nat_add k
  have hTsum :
      (∑' i, f i) - numeratorTaylor k c z = ∑' i, f (i+k) := by
    unfold numeratorTaylor
    change (∑' i, f i) - (∑ i ∈ Finset.range k, f i) = _
    rw [← hDecomp]
    abel
  change ‖(∑' j, f j) - numeratorTaylor k c z‖ ≤ (3/8)*C
  rw [hTsum]
  calc
    _ ≤ ∑' i, ‖f (i+k)‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' i, major i := hnorm.tsum_le_tsum hdom hm
    _ = C*Real.exp (-1) := by
      unfold major
      rw [(summable_geometric_of_lt_one hq0 hq1).tsum_mul_left,
        tsum_geometric_of_lt_one hq0 hq1]
      dsimp only [q,ρ]
      rw [show (1:ℝ)-(1-1/(k:ℝ)) = 1/(k:ℝ) by ring, one_div, inv_inv]
      field_simp [hk0.ne'] <;> ring
    _ ≤ _ := by
      rw [mul_comm (3/8:ℝ)]
      have he : Real.exp (-1) ≤ (3/8:ℝ) := by linarith only [Real.exp_neg_one_lt_d9]
      exact mul_le_mul_of_nonneg_left he (by dsimp [C]; positivity)

/-- The simultaneous radial comparison at an outer normalized point and at
a principal normalized point, from an all-degree odd-pole coefficient envelope. -/
theorem low_band_contraction {k : ℕ} (hk : 10 ≤ k)
    (c : ℕ → ℂ) {S R : ℝ} (hS : 0 < S)
    (hR : 1 ≤ R) (hRu : R ≤ 1+1/(k:ℝ))
    {ξ η : ℂ} (hξ : ‖ξ‖ = 1) (hη : ‖η‖ = 1)
    (hc1 : ‖c 1‖ ≤ 4)
    (hc : ∀ j : ℕ, 2 ≤ j → ‖c j‖ ≤ (2+9/(4*S*Real.sqrt j))/(j:ℝ)) :
    let ρ : ℂ := ((1-1/(k:ℝ):ℝ):ℂ)
    ‖numeratorTaylor k c ((R:ℂ)*ξ) - (∑' j, c j * (ρ*ξ)^j)‖ +
    ‖numeratorTaylor k c η - (∑' j, c j * (ρ*η)^j)‖ ≤ 12/(k:ℝ)+(5/2+1)*(2+9/(2*S*Real.sqrt k))+
          2*(3/8)*(2+9/(4*S*Real.sqrt k)) := by
  let ρ : ℝ := 1-1/(k:ℝ)
  dsimp only
  have hRpow (j : ℕ) (hj : j < k) : R^j - (1-1/(k:ℝ))^j ≤ (5/2)*((j:ℝ)/k) :=
    (sub_le_sub_right (pow_le_pow_left₀ (by linarith) hRu j) _).trans
      (small_band_radial_power hk hj).1
  have h1pow (j : ℕ) (hj : j < k) :
      (1:ℝ)^j - (1-1/(k:ℝ))^j ≤ (1:ℝ)*((j:ℝ)/k) := by
    simpa only [one_pow,one_mul] using (small_band_radial_power hk hj).2
  have hpre := low_band_radial_prefix hk c hS (show 0 ≤ (5:ℝ)/2 by norm_num) hR hξ hc1 hc hRpow
  have hpri := low_band_radial_prefix hk c hS (show 0 ≤ (1:ℝ) by norm_num) le_rfl hη hc1 hc h1pow
  simp only [Complex.ofReal_one,one_mul] at hpri
  have htail := low_band_taylor_tail hk c hS hξ hc
  have htail' := low_band_taylor_tail hk c hS hη hc
  dsimp only at htail htail'
  rw [norm_sub_rev] at htail htail'
  have triangle (a b d : ℂ) : ‖a-d‖ ≤ ‖a-b‖+‖b-d‖ := by
    simpa only [dist_eq_norm] using dist_triangle a b d
  have h1 := (triangle (numeratorTaylor k c ((R:ℂ)*ξ))
    (numeratorTaylor k c ((ρ:ℂ)*ξ)) (∑' j, c j*((ρ:ℂ)*ξ)^j)).trans (add_le_add hpre htail)
  have h2 := (triangle (numeratorTaylor k c η)
    (numeratorTaylor k c ((ρ:ℂ)*η)) (∑' j, c j*((ρ:ℂ)*η)^j)).trans (add_le_add hpri htail')
  have hlin : 4*(R-ρ) + 4*(1-ρ) ≤ 12/(k:ℝ) := by
    dsimp only [ρ]
    rw [show (12:ℝ)/(k:ℝ) = 12*(1/(k:ℝ)) by ring]
    linarith only [hRu]
  apply (add_le_add h1 h2).trans
  dsimp only [ρ] at hlin
  nlinarith only [hlin]

#print axioms low_band_contraction
end OpenMathResearch.LongCycleExcedances
