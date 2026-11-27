import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances

/-- If projected poles are 4c-separated, two points 2c apart cannot each
lie at distance strictly less than c from a pole. The closed gap includes
the equality case when adjacent poles are exactly 4c apart. -/
theorem two_candidate_gap {T : Set ℝ} (b c : ℝ)
    (hsep : ∀ p ∈ T, ∀ q ∈ T, p ≠ q → 4*c ≤ |p-q|) :
    ∃ a ∈ ({b-2*c,b} : Set ℝ), ∀ p ∈ T, c ≤ |a-p| := by
  classical
  by_cases h : ∀ p ∈ T, c ≤ |b-p|
  · exact ⟨b,by simp,h⟩
  push_neg at h
  obtain ⟨p,hp,hnear⟩ := h
  refine ⟨b-2*c,by simp,?_⟩
  intro q hq
  by_contra! hc
  obtain ⟨hl,hu⟩ := abs_lt.mp hnear
  obtain ⟨hl',hu'⟩ := abs_lt.mp hc
  by_cases he : p=q
  · subst q
    linarith
  · have hs := hsep p hp q hq he
    exact (not_lt_of_ge hs) (abs_lt.mpr ⟨by linarith,by linarith⟩)

/-- The positive nonprincipal odd heights are 2j+3 for j a natural number. -/
def oddProjectedPole (u : ℝ) (j : ℕ) : ℝ := u*((2*(j:ℝ)+3)^2-1)

private theorem odd_projected_spacing {u : ℝ} (hu : 0 ≤ u) {i j : ℕ} (hij : i < j) :
    16*u ≤ oddProjectedPole u j - oddProjectedPole u i := by
  have hj : (i:ℝ)+1 ≤ (j:ℝ) := by exact_mod_cast hij
  have h1 : 0 ≤ (2*(j:ℝ)+3) - (2*(i:ℝ)+5) := by linarith
  have h2 : 0 ≤ (2*(j:ℝ)+3) + (2*(i:ℝ)+5) := by positivity
  have hraw : 16 ≤ (2*(j:ℝ)+3)^2 - (2*(i:ℝ)+3)^2 := by
    nlinarith [mul_nonneg h1 h2, (show 0 ≤ (i:ℝ) by positivity)]
  unfold oddProjectedPole
  nlinarith [mul_le_mul_of_nonneg_left hraw hu]

/-- For every aspect x≥44 with x u≥1, the candidates 2 and 2−2c
give distance c from each projected radius (including the principal radius 0),
where c=min(1/25,4/x). -/
theorem original_odd_circle_choice {x u : ℝ} (hx : 44 ≤ x) (hu : 1 ≤ x*u) :
    let c := min (1/25 : ℝ) (4/x)
    ∃ a ∈ ({2-2*c,2} : Set ℝ), 48/25 ≤ a ∧ a ≤ 2 ∧
      c ≤ |a| ∧ ∀ j : ℕ, c ≤ |a-oddProjectedPole u j| := by
  let c := min (1/25 : ℝ) (4/x)
  have hx0 : 0 < x := by linarith
  have hu0 : 0 ≤ u := by by_contra! hn; nlinarith [mul_neg_of_pos_of_neg hx0 hn]
  have hc0 : 0 ≤ c := le_min (by norm_num) (by positivity)
  have hcap : c ≤ 1/25 := min_le_left _ _
  have hcx : c ≤ 4*u :=
    (min_le_right _ _).trans ((div_le_iff₀ hx0).mpr (by linarith))
  have hs (i j : ℕ) (hne : oddProjectedPole u i ≠ oddProjectedPole u j) :
      4*c ≤ |oddProjectedPole u i-oddProjectedPole u j| := by
    rcases lt_trichotomy i j with h | h | h
    · exact (show 4*c ≤ 16*u by linarith).trans
        ((odd_projected_spacing hu0 h).trans (le_abs.mpr (Or.inr (by linarith))))
    · exact (hne (h ▸ rfl)).elim
    · exact (show 4*c ≤ 16*u by linarith).trans ((odd_projected_spacing hu0 h).trans (le_abs_self _))
  obtain ⟨a,ha,hgap⟩ := two_candidate_gap (T:=Set.range (oddProjectedPole u)) 2 c
    (by rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩ hn; exact hs i j hn)
  have hchoice : a=2-2*c ∨ a=2 := by simpa using ha
  have hlo : 48/25 ≤ a := by rcases hchoice with h | h <;> linarith
  have hhi : a ≤ 2 := by rcases hchoice with h | h <;> linarith
  exact ⟨a,ha,hlo,hhi,(by rw [abs_of_nonneg (by linarith : 0 ≤ a)]; linarith),
    fun j => hgap _ ⟨j,rfl⟩⟩

private theorem all_signed_heights (l : ℤ) :
    (2*(l:ℝ)+1)^2 = 1 ∨ ∃ j : ℕ, (2*(l:ℝ)+1)^2 = (2*(j:ℝ)+3)^2 := by
  rcases l with m | m
  all_goals cases m with
  | zero => left; norm_num
  | succ j => right; refine ⟨j,?_⟩; simp only [Int.ofNat_eq_natCast, Int.cast_natCast, Nat.cast_succ, Int.cast_negSucc]; push_cast; ring

/-- The chosen projected gap supplies an actual integration radius and a
squared-modulus gap for every signed pole, for either sign of the real height. -/
theorem original_odd_circle_modulus_gap {x K s r : ℝ} (hx : 44 ≤ x) (hK : 0 < K)
    (hr : 0 < r) (hr2 : r^2 = s^2+Real.pi^2) (hu : 1 ≤ x*(K*(Real.pi/r)^2)) :
    let c := min (1/25 : ℝ) (4/x)
    ∃ a ∈ ({2-2*c,2} : Set ℝ), 48/25 ≤ a ∧ a ≤ 2 ∧
    ∃ R : ℝ, 0 < R ∧ R^2 = r^2*(1+a/K) ∧ ∀ l : ℤ,
      c*r^2/K ≤ |R^2 - ‖(⟨s,(2*(l:ℝ)+1)*Real.pi⟩ : ℂ)‖^2| := by
  let u := K*(Real.pi/r)^2
  let c := min (1/25 : ℝ) (4/x)
  obtain ⟨a,ha,hlo,hhi,hzero,hj⟩ := original_odd_circle_choice hx hu
  let R := r*Real.sqrt (1+a/K)
  have ha0 : 0 < a := by linarith
  have harg : 0 < 1+a/K := by positivity
  have hR : 0 < R := mul_pos hr (Real.sqrt_pos.mpr harg)
  have hR2 : R^2 = r^2*(1+a/K) := by dsimp only [R]; rw [mul_pow,Real.sq_sqrt harg.le]
  refine ⟨a,ha,hlo,hhi,R,hR,hR2,?_⟩
  intro l
  let m := 2*(l:ℝ)+1
  have hgap : c ≤ |a-u*(m^2-1)| := by
    rcases all_signed_heights l with h | ⟨j,h⟩
    · change c ≤ |a-u*((2*(l:ℝ)+1)^2-1)|
      simpa only [h,sub_self,mul_zero,sub_zero] using hzero
    · change c ≤ |a-u*((2*(l:ℝ)+1)^2-1)|
      rw [h]
      exact hj j
  have hn : ‖(⟨s,m*Real.pi⟩ : ℂ)‖^2 = s^2 + m^2*Real.pi^2 := by
    rw [Complex.sq_norm,Complex.normSq_apply]
    dsimp
    ring
  have he : R^2-‖(⟨s,m*Real.pi⟩ : ℂ)‖^2 = (a-u*(m^2-1))*(r^2/K) := by
    rw [hR2,hn]
    dsimp only [u]
    field_simp [hr.ne',hK.ne']
    nlinarith [hr2]
  change c*r^2/K ≤ |R^2-‖(⟨s,m*Real.pi⟩ : ℂ)‖^2|
  rw [he,abs_mul,abs_of_nonneg (div_nonneg (sq_nonneg r) hK.le),mul_div_assoc]
  exact mul_le_mul_of_nonneg_right hgap (by positivity)

#print axioms original_odd_circle_modulus_gap
#print axioms two_candidate_gap
#print axioms original_odd_circle_choice
end OpenMathResearch.LongCycleExcedances
