import AdaptiveFrontGap
import RepositoryColorAlpha
import RepositoryExteriorEnvelopes
import RepositoryExteriorLag

set_option autoImplicit false
noncomputable section
namespace RepositoryQuotientAudit
open LongCycles Real OpenMathResearch.LongCycleExcedances

/-- Normalized coefficient of the literal old row. -/
def oldFrontAlpha (n k p : ℕ) : ℝ := (enumerator n k).coeff p/(p:ℝ)^n

private theorem front_near_rank_range {n p : ℕ} (hn : 10000 ≤ n)
    (hp : p ≤ ⌊sqrt (n:ℝ)/2⌋₊) : 4*p^2 ≤ n ∧ 100*p ≤ n := by
  let y := sqrt (n:ℝ)
  have h100 : (100:ℝ) ≤ y := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).2
    norm_num
    exact_mod_cast hn
  have hy : 0 ≤ y := sqrt_nonneg _
  have hy2 : y^2 = n := sq_sqrt (by positivity)
  have hp' : (p:ℝ) ≤ y/2 :=
    (show (p:ℝ) ≤ ((⌊y/2⌋₊:ℕ):ℝ) by exact_mod_cast hp).trans (Nat.floor_le (by positivity))
  have hh := pow_le_pow_left₀ (show (0:ℝ) ≤ p by positivity) hp' 2
  rw [div_pow,hy2] at hh
  constructor
  · exact_mod_cast (show 4*(p:ℝ)^2 ≤ n by nlinarith only [hh])
  · have hp100 := mul_nonneg hy (sub_nonneg.mpr h100)
    exact_mod_cast (show 100*(p:ℝ) ≤ n by nlinarith only [hp',hp100,hy2])

private theorem front_alpha_near_lower {n p k : ℕ} (hn : 10000 ≤ n) (hk : 2 ≤ k)
    (hkn : k ≤ n) (hp : 0 < p) (hJ : p ≤ ⌊sqrt (n:ℝ)/2⌋₊) :
    99/(100*(1+(8/3:ℝ)*((k:ℝ)*p/n))) ≤ oldFrontAlpha n k p :=
  original_front_alpha_lower_all hn hk hkn hp (front_near_rank_range hn hJ).1

private theorem front_alpha_near_pos {n p k : ℕ} (hn : 10000 ≤ n) (hk : 2 ≤ k)
    (hkn : k ≤ n) (hp : 0 < p) (hJ : p ≤ ⌊sqrt (n:ℝ)/2⌋₊) :
    0 < oldFrontAlpha n k p :=
  (show 0 < 99/(100*(1+(8/3:ℝ)*((k:ℝ)*p/n))) by positivity).trans_le
    (front_alpha_near_lower hn hk hkn hp hJ)

theorem original_front_alpha_ratio_all {n k i j : ℕ} (hn : 10000 ≤ n) (hk : 2 ≤ k)
    (hkn : k ≤ n) (hi : 0 < i) (hj : 0 < j)
    (hiJ : i ≤ ⌊sqrt (n:ℝ)/2⌋₊) (hjJ : j ≤ ⌊sqrt (n:ℝ)/2⌋₊) :
    oldFrontAlpha n k j / oldFrontAlpha n k i ≤ (51/10:ℝ)*max 1 ((i:ℝ)/j) := by
  have hu := original_front_alpha_upper hj hk hkn (front_near_rank_range hn hjJ).2
  have he : ((i:ℝ)/j)*((k:ℝ)*j/n) = (k:ℝ)*i/n := by
    field_simp [show (j:ℝ) ≠ 0 by positivity, show (n:ℝ) ≠ 0 by positivity] <;> ring
  have hlo := front_alpha_near_lower hn hk hkn hi hiJ
  rw [←he] at hlo
  exact (exterior_alpha_ratio (by positivity) (by positivity)
    (front_alpha_near_pos hn hk hkn hj hjJ).le hu.1 hu.2 (by simpa only [mul_assoc] using hlo)).2

private theorem original_front_alpha_eq_coeff (n k p : ℕ) (hp : 0 < p) :
    oldFrontAlpha n k p*(p:ℝ)^n = (enumerator n k).coeff p := by
  unfold oldFrontAlpha
  rw [div_mul_cancel₀ _ (by positivity)]

theorem original_adaptive_front_scale {n k h : ℕ} (hh : 0 < h) :
    originalExteriorScale n k h =
      (oldFrontAlpha n k h/oldFrontAlpha n k (h+1))*((h:ℝ)/((h:ℝ)+1))^n := by
  unfold originalExteriorScale
  rw [←original_front_alpha_eq_coeff n k (h+1) (by omega),
    ←original_front_alpha_eq_coeff n k h hh, div_pow, div_mul_div_comm, Nat.cast_add, Nat.cast_one]

private theorem original_front_central_ratios {n k h : ℕ} (hn : 10000 ≤ n) (hk : 2 ≤ k)
    (hkn : k ≤ n) (hh : 0 < h) (hJ : h+1 ≤ ⌊sqrt (n:ℝ)/2⌋₊) :
    let ρ := oldFrontAlpha n k h/oldFrontAlpha n k (h+1)
    0 < ρ ∧ ρ ≤ (51/10)*(((h:ℝ)+1)/h) ∧ 1/ρ ≤ 51/10 := by
  have hhJ : h ≤ ⌊sqrt (n:ℝ)/2⌋₊ := by omega
  have hα := front_alpha_near_pos hn hk hkn hh hhJ
  have hβ := front_alpha_near_pos hn hk hkn (by omega : 0 < h+1) hJ
  have hp : (0:ℝ) < h := by positivity
  have hf : (h:ℝ)/((h:ℝ)+1) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
  have hg : 1 ≤ ((h:ℝ)+1)/h := (le_div_iff₀ hp).2 (by linarith)
  have hu := original_front_alpha_ratio_all hn hk hkn (by omega : 0 < h+1) hh hJ hhJ
  have hi := original_front_alpha_ratio_all hn hk hkn hh (by omega : 0 < h+1) hhJ hJ
  simp only [Nat.cast_add, Nat.cast_one, max_eq_right hg] at hu
  simp only [Nat.cast_add, Nat.cast_one, max_eq_left hf, mul_one] at hi
  exact ⟨div_pos hα hβ,hu,by rw [one_div_div]; exact hi⟩

private theorem original_front_far_inverse {n k h j : ℕ} (hn : 10000 ≤ n) (hk : 2 ≤ k)
    (hkn : k ≤ n) (hH : h ≤ uniformJoinRank n)
    (hJ : h+1 ≤ ⌊sqrt (n:ℝ)/2⌋₊) (hj : ⌊sqrt (n:ℝ)/2⌋₊ < j) :
    1/oldFrontAlpha n k (h+1) ≤ 8*(((j-(h+1):ℕ):ℝ)+1) := by
  have hgeo := front_far_rank_geometry hn hH hj
  have hlo := front_alpha_near_lower hn hk hkn (by omega : 0 < h+1) hJ
  have hn0 : (0:ℝ) < n := by positivity
  have hk' : (k:ℝ) ≤ n := by exact_mod_cast hkn
  have ha : (k:ℝ)*((h+1:ℕ):ℝ)/n ≤ (h:ℝ)+1 := by
    apply (div_le_iff₀ hn0).2
    rw [Nat.cast_add, Nat.cast_one]
    simpa only [mul_comm ((h:ℝ)+1) (n:ℝ)] using
      mul_le_mul_of_nonneg_right hk' (show (0:ℝ) ≤ (h:ℝ)+1 by positivity)
  exact front_far_reciprocal (by positivity) (by positivity) (ha.trans hgeo.2.1.le) hlo

/-- The two old-row coefficient hypotheses of the exterior-envelope theorem,
at the actual adaptive endpoints. -/
theorem original_old_front_weighted_tails_all {n k h : ℕ} (hn : 10000 ≤ n) (hk : 2 ≤ k)
    (hkn : k ≤ n) (hh : 0 < h) (hH : h ≤ uniformJoinRank n) :
    let P := enumerator n k
    let c := P.coeff h
    let u := originalExteriorScale n k h
    let w := frontCoefficientWeight h ((7/8:ℝ)*u) ((9/8:ℝ)*u)
    (0 < c ∧ 0 < P.coeff (h+1)) ∧
    (∀ j < h, |P.coeff j| * w j ≤ (51/10*c)*(((h-j:ℕ):ℝ)+1)*(1/300)^(h-j)) ∧
    (∀ j, h+1 < j → |P.coeff j| * w j ≤ (9*c)*(((j-(h+1):ℕ):ℝ)+1)*(1/300)^(j-(h+1))) := by
  let P := enumerator n k
  let c := P.coeff h
  let u := originalExteriorScale n k h
  let J := ⌊sqrt (n:ℝ)/2⌋₊
  have hgap : h+2 ≤ J := front_lag_cutoff_gap hn hH
  have hJh : h ≤ J := by omega
  have hJt : h+1 ≤ J := by omega
  have hα := front_alpha_near_pos hn hk hkn hh hJh
  have hβ := front_alpha_near_pos hn hk hkn (by omega : 0 < h+1) hJt
  have hc : 0 < c := by
    change 0 < (enumerator n k).coeff h
    rw [←original_front_alpha_eq_coeff n k h hh]
    exact mul_pos hα (by positivity)
  have ht : 0 < P.coeff (h+1) := by
    change 0 < (enumerator n k).coeff (h+1)
    rw [←original_front_alpha_eq_coeff n k (h+1) (by omega)]
    exact mul_pos hβ (by positivity)
  have hu : 0 < u := div_pos hc ht
  have hscale := original_adaptive_front_scale (n:=n) (k:=k) hh
  have hr := original_front_central_ratios hn hk hkn hh hJt
  dsimp only at hr
  obtain ⟨hmL,hmU⟩ := front_adaptive_multipliers hn hh hH hr.2.1 hr.2.2
  have hcoefficient (p : ℕ) : 0 ≤ (enumerator n k).coeff p ∧
      (enumerator n k).coeff p ≤ (p:ℝ)^n := RunColors.original_coeff_envelope n k p hk
  refine ⟨⟨hc,ht⟩, ?_, ?_⟩
  · intro j hj
    rw [frontCoefficientWeight,if_neg (not_le_of_gt hj),abs_of_nonneg (hcoefficient j).1]
    by_cases hzero : j = 0
    · subst j
      have hz := (hcoefficient 0).2
      simp only [Nat.cast_zero, zero_pow (by omega : n ≠ 0)] at hz
      have hz' := le_antisymm hz (hcoefficient 0).1
      rw [hz', zero_mul]
      positivity
    have hj0 : 0 < j := by omega
    have hjJ : j ≤ J := by omega
    have hrank : (h:ℝ)/j ≤ ((h-j:ℕ):ℝ)+1 := by
      have hj1 : (1:ℝ) ≤ j := by exact_mod_cast hj0
      have hp : (0:ℝ) < j := by positivity
      rw [Nat.cast_sub hj.le]
      apply (div_le_iff₀ hp).2
      nlinarith only [mul_nonneg (sub_nonneg.mpr hj1)
        (show (0:ℝ) ≤ (h:ℝ)-(j:ℝ) from sub_nonneg.mpr (by exact_mod_cast hj.le))]
    have hr1 : (1:ℝ) ≤ (h:ℝ)/j := by
      apply (le_div_iff₀ (by positivity)).2
      simpa only [one_mul] using (show (j:ℝ) ≤ h by exact_mod_cast hj.le)
    have hRatio := original_front_alpha_ratio_all hn hk hkn hh hj0 hJh hjJ
    rw [max_eq_right hr1] at hRatio
    have hαbound := (div_le_iff₀ hα).mp (hRatio.trans (mul_le_mul_of_nonneg_left hrank (by norm_num)))
    have hb := front_bare_left_weight hh hj.le hr.1 hmL
    dsimp only at hb
    rw [←hscale] at hb
    rw [←original_front_alpha_eq_coeff n k j hj0,
      ←original_front_alpha_eq_coeff n k h hh]
    calc
      _ = oldFrontAlpha n k j*((j:ℝ)^n/((7/8:ℝ)*u)^(h-j)) := by ring
      _ ≤ oldFrontAlpha n k j*((h:ℝ)^n*(1/300)^(h-j)) :=
        mul_le_mul_of_nonneg_left hb (front_alpha_near_pos hn hk hkn hj0 hjJ).le
      _ ≤ ((51/10:ℝ)*(((h-j:ℕ):ℝ)+1)*oldFrontAlpha n k h)
          *((h:ℝ)^n*(1/300)^(h-j)) :=
        mul_le_mul_of_nonneg_right hαbound (by positivity)
      _ = _ := by ring
  · intro j hj
    let l := j-(h+1)
    let U := (9/8:ℝ)*u
    have hj0 : 0 < j := by omega
    have hm : 0 ≤ oldFrontAlpha n k j := div_nonneg (hcoefficient j).1 (by positivity)
    have hRatio : oldFrontAlpha n k j/oldFrontAlpha n k (h+1) ≤ 8*((l:ℝ)+1) := by
      by_cases hjJ : j ≤ J
      · have hratio := original_front_alpha_ratio_all hn hk hkn (by omega : 0 < h+1) hj0 hJt hjJ
        have hb : ((h+1:ℕ):ℝ)/j ≤ 1 := (div_le_one (by positivity)).2 (by exact_mod_cast hj.le)
        rw [max_eq_left hb] at hratio
        exact hratio.trans (by linarith only [Nat.cast_nonneg (α:=ℝ) l])
      · have hinv := original_front_far_inverse hn hk hkn hH hJt (by omega : J < j)
        have h1 : oldFrontAlpha n k j ≤ 1 := (div_le_one (by positivity)).2 (hcoefficient j).2
        exact (div_le_div_of_nonneg_right h1 hβ.le).trans hinv
    have hαbound := (div_le_iff₀ hβ).mp hRatio
    have hb := front_bare_right_weight hh hj.le hr.1 hmU
    dsimp only at hb
    have hs : ((h+1:ℕ):ℝ) = (h:ℝ)+1 := by rw [Nat.cast_add, Nat.cast_one]
    rw [←hscale,←hs] at hb
    have hcenter : P.coeff (h+1)*U = (9/8)*c := by
      dsimp [U,u,c,originalExteriorScale,P]
      rw [mul_left_comm, mul_div_cancel₀ _ ht.ne']
    have hjpow : j-h = l+1 := by dsimp [l]; omega
    rw [frontCoefficientWeight,if_pos (by omega : h ≤ j),abs_of_nonneg (hcoefficient j).1,hjpow,pow_succ]
    rw [←original_front_alpha_eq_coeff n k j hj0]
    calc
      _ = (oldFrontAlpha n k j*((j:ℝ)^n*U^l))*U := by ring
      _ ≤ (oldFrontAlpha n k j*(((h+1:ℕ):ℝ)^n*(1/300)^l))*U :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb hm) (by positivity)
      _ = oldFrontAlpha n k j*(((h+1:ℕ):ℝ)^n*(1/300)^l*U) := by ring
      _ ≤ (8*((l:ℝ)+1)*oldFrontAlpha n k (h+1))*(((h+1:ℕ):ℝ)^n*(1/300)^l*U) :=
        mul_le_mul_of_nonneg_right hαbound (by positivity)
      _ = (8*((l:ℝ)+1))*((oldFrontAlpha n k (h+1)*((h+1:ℕ):ℝ)^n)*U)*(1/300)^l := by ring
      _ = _ := by rw [original_front_alpha_eq_coeff _ _ _ (by omega),hcenter] <;> ring

theorem original_front_adjacent_gap_all {n k h : ℕ} (hn : 10000 ≤ n) (hk : 2 ≤ k)
    (hkn : k ≤ n) (hh : 0 < h) (hH : h+1 ≤ uniformJoinRank n) :
    20*originalExteriorScale n k h < originalExteriorScale n k (h+1) := by
  have hJ := front_lag_cutoff_gap hn hH
  have r := original_front_central_ratios (n:=n) (k:=k) (h:=h) hn hk hkn hh (by omega)
  have s := original_front_central_ratios (n:=n) (k:=k) (h:=h+1) hn hk hkn (by omega) (by omega)
  dsimp only at r s
  have hh' : (1:ℝ) ≤ h := by exact_mod_cast hh
  have hratio : ((h:ℝ)+1)/h ≤ 2 := (div_le_iff₀ (by positivity)).2 (by linarith only [hh'])
  have hr := r.2.1.trans (show (51/10:ℝ)*(((h:ℝ)+1)/h) ≤ 51/5 by linarith only [hratio])
  have hs := (div_le_iff₀ s.1).mp s.2.2
  have hs' : 1 ≤ (51/5:ℝ)*(oldFrontAlpha n k (h+1)/oldFrontAlpha n k (h+1+1)) := by
    linarith only [hs,s.1]
  have hgap := adaptive_front_adjacent_gap hn hh (show h ≤ uniformJoinRank n by omega)
    r.1 hr hs'
  rw [original_adaptive_front_scale hh, original_adaptive_front_scale (h:=h+1) (by omega)]
  simpa only [Nat.cast_add, Nat.cast_one,add_assoc,one_add_one_eq_two] using hgap

theorem original_far_front_weighted_lag_all {n k h j : ℕ} (hn : 10000 ≤ n) (hk : 2 ≤ k)
    (hkn : k ≤ n) (hh : 0 < h) (hH : h ≤ uniformJoinRank n)
    (hj : ⌊sqrt (n:ℝ)/2⌋₊ < j) :
    let c := (enumerator n k).coeff h
    let u := originalExteriorScale n k h
    let w := frontCoefficientWeight h ((7/8:ℝ)*u) ((9/8:ℝ)*u)
    let l := j-(h+1)
    |(originalFrontLag n k).coeff j| * w j ≤ (36*c)*(l:ℝ)*((l:ℝ)+1)*(1/300)^l := by
  let c := (enumerator n k).coeff h
  let u := originalExteriorScale n k h
  let U := (9/8:ℝ)*u
  have hgeo := front_far_rank_geometry hn hH hj
  have hgap := front_lag_cutoff_gap hn hH
  have hJt : h+1 ≤ ⌊sqrt (n:ℝ)/2⌋₊ := by omega
  have hβ := front_alpha_near_pos hn hk hkn (by omega : 0 < h+1) hJt
  have hcpos := (original_old_front_weighted_tails_all hn hk hkn hh hH).1
  have hu : 0 < u := div_pos hcpos.1 hcpos.2
  have hscale := original_adaptive_front_scale (n:=n) (k:=k) hh
  have hr := original_front_central_ratios hn hk hkn hh hJt
  dsimp only at hr
  have hm := (front_adaptive_multipliers hn hh hH hr.2.1 hr.2.2).2
  have hb := front_bare_right_weight hh hgeo.1.le hr.1 hm
  dsimp only at hb
  have hs : ((h+1:ℕ):ℝ) = (h:ℝ)+1 := by rw [Nat.cast_add, Nat.cast_one]
  rw [←hscale,←hs] at hb
  have hrec := original_front_far_inverse hn hk hkn hH hJt hj
  have hcenter : oldFrontAlpha n k (h+1)*((h+1:ℕ):ℝ)^n*U = (9/8)*c := by
    rw [original_front_alpha_eq_coeff _ _ _ (by omega)]
    dsimp [U,u,c,originalExteriorScale]
    rw [mul_left_comm,mul_div_cancel₀ _ hcpos.2.ne']
  have hidx : j-h = j-(h+1)+1 := by omega
  have hV : 0 ≤ (originalFrontLag n k).coeff j ∧
      (originalFrontLag n k).coeff j ≤ (j:ℝ)^(n+1) :=
    original_global_lag_bound (n:=n) (k:=k) (by omega) hk j
  dsimp only
  rw [frontCoefficientWeight,if_pos (by omega : h ≤ j),hidx]
  exact front_far_weighted_lag (by positivity : 0 ≤ U) (by positivity) hβ
    hV.1 hV.2 hb hgeo.2.2.le hrec hcenter

#print axioms original_front_alpha_ratio_all
#print axioms original_adaptive_front_scale
#print axioms original_old_front_weighted_tails_all
#print axioms original_front_adjacent_gap_all
#print axioms original_far_front_weighted_lag_all
/-- A uniform cap on the literal centers. Multiplying by 9/8 gives the
upper edge used by the phase-to-exterior join. -/
theorem original_front_scale_cap_all {n k h : ℕ} (hn : 10000 ≤ n) (hk : 2 ≤ k)
    (hs : k ≤ n) (hh : 0 < h) (hH : h ≤ uniformJoinRank n) :
    originalExteriorScale n k h ≤ (51/5:ℝ)*
      ((uniformJoinRank n:ℝ)/((uniformJoinRank n:ℝ)+1))^n := by
  have hJ := front_lag_cutoff_gap hn hH
  have r := original_front_central_ratios (h:=h) hn hk hs hh (by omega)
  dsimp only at r
  have hh' : (1:ℝ) ≤ h := by exact_mod_cast hh
  have h2 : ((h:ℝ)+1)/h ≤ 2 := (div_le_iff₀ (by positivity)).mpr (by linarith)
  have hr := r.2.1.trans (show (51/10:ℝ)*(((h:ℝ)+1)/h) ≤ 51/5 by linarith only [h2])
  have hH' : (h:ℝ) ≤ (uniformJoinRank n:ℝ) := Nat.cast_le.mpr hH
  have hb : (h:ℝ)/((h:ℝ)+1) ≤ (uniformJoinRank n:ℝ)/((uniformJoinRank n:ℝ)+1) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith only [hH']
  rw [original_adaptive_front_scale hh]
  exact mul_le_mul hr (pow_le_pow_left₀ (by positivity) hb n) (by positivity) (by norm_num)

#print axioms original_front_scale_cap_all
/- The sparse-sector signatures remain available to existing callers. -/
theorem original_front_alpha_ratio {n k i j : ℕ} (hn : 10000 ≤ n) (hk : 2 ≤ k)
    (hkn : 4000*k < n) (hi : 0 < i) (hj : 0 < j)
    (hiJ : i ≤ ⌊sqrt (n:ℝ)/2⌋₊) (hjJ : j ≤ ⌊sqrt (n:ℝ)/2⌋₊) :
    oldFrontAlpha n k j / oldFrontAlpha n k i ≤ (51/10:ℝ)*max 1 ((i:ℝ)/j) :=
  original_front_alpha_ratio_all hn hk (by omega) hi hj hiJ hjJ

theorem original_old_front_weighted_tails {n k h : ℕ} (hn : 10000 ≤ n) (hk : 2 ≤ k)
    (hkn : 4000*k < n) (hh : 0 < h) (hH : h ≤ uniformJoinRank n) :
    let P := enumerator n k
    let c := P.coeff h
    let u := originalExteriorScale n k h
    let w := frontCoefficientWeight h ((7/8:ℝ)*u) ((9/8:ℝ)*u)
    (0 < c ∧ 0 < P.coeff (h+1)) ∧
    (∀ j < h, |P.coeff j| * w j ≤ (51/10*c)*(((h-j:ℕ):ℝ)+1)*(1/300)^(h-j)) ∧
    (∀ j, h+1 < j → |P.coeff j| * w j ≤ (9*c)*(((j-(h+1):ℕ):ℝ)+1)*(1/300)^(j-(h+1))) :=
  original_old_front_weighted_tails_all hn hk (by omega) hh hH

theorem original_front_adjacent_gap {n k h : ℕ} (hn : 10000 ≤ n) (hk : 2 ≤ k)
    (hkn : 4000*k < n) (hh : 0 < h) (hH : h+1 ≤ uniformJoinRank n) :
    20*originalExteriorScale n k h < originalExteriorScale n k (h+1) :=
  original_front_adjacent_gap_all hn hk (by omega) hh hH

theorem original_far_front_weighted_lag {n k h j : ℕ} (hn : 10000 ≤ n) (hk : 2 ≤ k)
    (hkn : 4000*k < n) (hh : 0 < h) (hH : h ≤ uniformJoinRank n)
    (hj : ⌊sqrt (n:ℝ)/2⌋₊ < j) :
    let c := (enumerator n k).coeff h
    let u := originalExteriorScale n k h
    let w := frontCoefficientWeight h ((7/8:ℝ)*u) ((9/8:ℝ)*u)
    let l := j-(h+1)
    |(originalFrontLag n k).coeff j| * w j ≤ (36*c)*(l:ℝ)*((l:ℝ)+1)*(1/300)^l :=
  original_far_front_weighted_lag_all hn hk (by omega) hh hH hj

theorem original_front_scale_cap {n k h : ℕ} (hn : 10000 ≤ n) (hk : 2 ≤ k)
    (hs : 4000*k < n) (hh : 0 < h) (hH : h ≤ uniformJoinRank n) :
    originalExteriorScale n k h ≤ (51/5:ℝ)*
      ((uniformJoinRank n:ℝ)/((uniformJoinRank n:ℝ)+1))^n :=
  original_front_scale_cap_all hn hk (by omega) hh hH

#print axioms original_far_front_weighted_lag
#print axioms original_front_adjacent_gap
#print axioms original_front_alpha_ratio
#print axioms original_front_scale_cap
#print axioms original_old_front_weighted_tails
end RepositoryQuotientAudit
