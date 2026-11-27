import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Real.Basic

namespace OpenMathResearch.LongCycleExcedances.RunColors

open Finset

variable {n : ℕ}

/-- Follow downward edges of the actual permutation up to the end of the run. -/
def runEnd (σ : Equiv.Perm (Fin n)) (x : Fin n) : Fin n :=
  if σ x < x then runEnd σ (σ x) else x
termination_by x.val

theorem runEnd_of_down {σ : Equiv.Perm (Fin n)} {x : Fin n} (h : σ x < x) :
    runEnd σ x = runEnd σ (σ x) := by
  rw [runEnd]
  simp [h]

theorem runEnd_of_stop {σ : Equiv.Perm (Fin n)} {x : Fin n} (h : ¬ σ x < x) :
    runEnd σ x = x := by
  rw [runEnd]
  simp [h]

/-- A visible path along downward edges, with its two endpoints. -/
inductive DownRoute (σ : Equiv.Perm (Fin n)) : Fin n → Fin n → Prop
  | refl (x : Fin n) : DownRoute σ x x
  | step {x y : Fin n} : σ x < x → DownRoute σ (σ x) y → DownRoute σ x y

theorem DownRoute.le {σ : Equiv.Perm (Fin n)} {x y : Fin n} (h : DownRoute σ x y) :
    y ≤ x := by
  induction h with
  | refl => exact le_rfl
  | step hdown _ ih => exact ih.trans hdown.le

theorem DownRoute.target_le_first {σ : Equiv.Perm (Fin n)} {x y : Fin n}
    (h : DownRoute σ x y) (hne : x ≠ y) : y ≤ σ x := by
  cases h with
  | refl => exact (hne rfl).elim
  | step _ hroute => exact hroute.le

theorem DownRoute.last_edge {σ : Equiv.Perm (Fin n)} {x y : Fin n}
    (h : DownRoute σ x y) (hne : x ≠ y) :
    ∃ z : Fin n, z ≤ x ∧ σ z = y ∧ σ z < z := by
  induction h with
  | refl => exact (hne rfl).elim
  | @step x y hdown route ih =>
    by_cases hy : σ x = y
    · exact ⟨x, le_rfl, hy, hdown⟩
    · obtain ⟨z, hz, hzy, hd⟩ := ih hy
      exact ⟨z, hz.trans hdown.le, hzy, hd⟩

theorem runEnd_route (σ : Equiv.Perm (Fin n)) (x : Fin n) :
    DownRoute σ x (runEnd σ x) := by
  by_cases hd : σ x < x
  · rw [runEnd_of_down hd]
    exact .step hd (runEnd_route σ (σ x))
  · rw [runEnd_of_stop hd]
    exact .refl _
termination_by x.val

theorem runEnd_le (σ : Equiv.Perm (Fin n)) (x : Fin n) : runEnd σ x ≤ x :=
  (runEnd_route σ x).le

theorem runEnd_stops (σ : Equiv.Perm (Fin n)) (x : Fin n) :
    ¬ σ (runEnd σ x) < runEnd σ x := by
  by_cases hd : σ x < x
  · rw [runEnd_of_down hd]
    exact runEnd_stops σ (σ x)
  · rwa [runEnd_of_stop hd]
termination_by x.val

/-- The labels with the same run end lie on the same strictly decreasing path.
Injectivity of the permutation excludes a branch entering a used edge. -/
theorem downRoute_of_runEnd_eq (σ : Equiv.Perm (Fin n)) (x y : Fin n)
    (hxy : x ≤ y) (he : runEnd σ x = runEnd σ y) :
    DownRoute σ y x := by
  by_cases hn : x = y
  · rw [hn]
    exact .refl _
  · have hlt := lt_of_le_of_ne hxy hn
    by_cases hd : σ y < y
    · have hey : runEnd σ x = runEnd σ (σ y) := he.trans (runEnd_of_down hd)
      by_cases hx : x ≤ σ y
      · exact .step hd (downRoute_of_runEnd_eq σ x (σ y) hx hey)
      · have hroute := downRoute_of_runEnd_eq σ (σ y) x (le_of_not_ge hx) hey.symm
        obtain ⟨z, hz, hzy, _⟩ := hroute.last_edge (ne_of_gt (lt_of_not_ge hx))
        have hz' : z = y := σ.injective hzy
        exact (not_le_of_gt hlt (hz' ▸ hz)).elim
    · have hz : runEnd σ x = y := he.trans (runEnd_of_stop hd)
      exact (not_le_of_gt hlt (hz ▸ runEnd_le σ x)).elim
termination_by y.val

/-- The image of an ascent is the largest label of its run. -/
theorem ascent_image_is_max {σ : Equiv.Perm (Fin n)} {x y : Fin n}
    (hx : x < σ x) (he : runEnd σ y = runEnd σ (σ x)) : y ≤ σ x := by
  by_contra! hy
  have hr := downRoute_of_runEnd_eq σ (σ x) y hy.le he.symm
  obtain ⟨z, _, hz, hd⟩ := hr.last_edge hy.ne'
  have hzx : z = x := σ.injective hz
  exact (not_lt_of_ge hx.le) (hzx ▸ hd)

abbrev Tails (σ : Equiv.Perm (Fin n)) := {x : Fin n // x < σ x}

/-- On a fixed-point-free permutation, the end of a decreasing run is the
tail of an ascent. -/
def runTail (σ : Equiv.Perm (Fin n)) (hσ : ∀ x, σ x ≠ x) (x : Fin n) : Tails σ :=
  ⟨runEnd σ x, lt_of_le_of_ne (le_of_not_gt (runEnd_stops σ x)) (hσ _).symm⟩

@[simp] theorem runTail_of_tail (σ : Equiv.Perm (Fin n)) (hσ : ∀ x, σ x ≠ x)
    (x : Tails σ) : runTail σ hσ x.val = x :=
  Subtype.ext (runEnd_of_stop (not_lt_of_ge x.property.le))

/-- The next run is the one containing the image of the current run's tail. -/
def nextTail (σ : Equiv.Perm (Fin n)) (hσ : ∀ x, σ x ≠ x) (x : Tails σ) : Tails σ :=
  runTail σ hσ (σ x.val)

theorem nextTail_injective (σ : Equiv.Perm (Fin n)) (hσ : ∀ x, σ x ≠ x) :
    Function.Injective (nextTail σ hσ) := by
  intro x y he
  have hh : runEnd σ (σ x.val) = runEnd σ (σ y.val) := congrArg Subtype.val he
  exact Subtype.ext (σ.injective (le_antisymm
    (ascent_image_is_max y.property hh) (ascent_image_is_max x.property hh.symm)))

noncomputable def tailPermutation (σ : Equiv.Perm (Fin n)) (hσ : ∀ x, σ x ≠ x) :
    Equiv.Perm (Tails σ) :=
  Equiv.ofBijective (nextTail σ hσ)
    ⟨nextTail_injective σ hσ, Finite.surjective_of_injective (nextTail_injective σ hσ)⟩

@[simp] theorem tailPermutation_apply (σ : Equiv.Perm (Fin n)) (hσ : ∀ x, σ x ≠ x)
    (x : Tails σ) :
    tailPermutation σ hσ x = runTail σ hσ (σ x.val) := rfl

/-- The membership relation of the decreasing runs and the destination run of
each ascent determine the actual permutation. -/
theorem perm_eq_of_same_runs {σ τ : Equiv.Perm (Fin n)} (hσ : ∀ x, σ x ≠ x)
    (hτ : ∀ x, τ x ≠ x)
    (hsame : ∀ a b, runEnd σ a = runEnd σ b ↔ runEnd τ a = runEnd τ b)
    (hnext : ∀ x, x < σ x → x < τ x →
      runEnd τ (σ x) = runEnd τ (τ x)) : σ = τ := by
  ext x
  by_cases hd : σ x < x
  · have hrun := (hsame (σ x) x).mp (runEnd_of_down hd).symm
    have ht : τ x < x := by
      by_contra h
      have he := hrun.trans (runEnd_of_stop h)
      have hz := runEnd_le τ (σ x)
      rw [he] at hz
      exact (not_le_of_gt hd) hz
    have hrun' := (hsame (τ x) x).mpr (runEnd_of_down ht).symm
    exact le_antisymm
      ((downRoute_of_runEnd_eq τ (σ x) x hd.le hrun).target_le_first hd.ne')
      ((downRoute_of_runEnd_eq σ (τ x) x ht.le hrun').target_le_first ht.ne')
  · have hs : x < σ x := lt_of_le_of_ne (le_of_not_gt hd) (hσ x).symm
    have ht : x < τ x := by
      by_cases hdown : τ x < x
      · have he := ((hsame (τ x) x).mpr (runEnd_of_down hdown).symm).trans (runEnd_of_stop hd)
        have hz := runEnd_le σ (τ x)
        rw [he] at hz
        exact ((not_le_of_gt hdown) hz).elim
      · exact lt_of_le_of_ne (le_of_not_gt hdown) (hτ x).symm
    have he := hnext x hs ht
    exact le_antisymm (ascent_image_is_max ht he)
      (ascent_image_is_max hs ((hsame (σ x) (τ x)).mpr he).symm)

private def color {p : ℕ} (σ : Equiv.Perm (Fin n)) (hσ : ∀ x, σ x ≠ x)
    (e : Tails σ ≃ Fin p) : Fin n → Fin p :=
  fun x => e (runTail σ hσ x)

private theorem color_eq_iff {p : ℕ} (σ : Equiv.Perm (Fin n)) (hσ : ∀ x, σ x ≠ x)
    (e : Tails σ ≃ Fin p) (a b : Fin n) :
    color σ hσ e a = color σ hσ e b ↔ runEnd σ a = runEnd σ b := by
  constructor
  · intro h
    exact congrArg Subtype.val (e.injective h)
  · intro h
    exact congrArg e (Subtype.ext h)

private noncomputable def colorSuccessor {p : ℕ} (σ : Equiv.Perm (Fin n))
    (hσ : ∀ x, σ x ≠ x) (e : Tails σ ≃ Fin p) : Equiv.Perm (Fin p) :=
  e.symm.trans ((tailPermutation σ hσ).trans e)

private theorem color_of_ascent {p : ℕ} (σ : Equiv.Perm (Fin n))
    (hσ : ∀ x, σ x ≠ x) (e : Tails σ ≃ Fin p) {x : Fin n} (hx : x < σ x) :
    colorSuccessor σ hσ e (color σ hσ e x) = color σ hσ e (σ x) := by
  let t : Tails σ := ⟨x, hx⟩
  change colorSuccessor σ hσ e (color σ hσ e t.val) = color σ hσ e (σ t.val)
  simp [colorSuccessor, color]

private theorem perm_eq_of_codes {p : ℕ} {σ τ : Equiv.Perm (Fin n)}
    {hσ : ∀ x, σ x ≠ x} {hτ : ∀ x, τ x ≠ x}
    {e : Tails σ ≃ Fin p} {f : Tails τ ≃ Fin p}
    (hw : color σ hσ e = color τ hτ f)
    (hc : colorSuccessor σ hσ e = colorSuccessor τ hτ f) : σ = τ := by
  apply perm_eq_of_same_runs hσ hτ
  · intro a b
    rw [← color_eq_iff σ hσ e, ← color_eq_iff τ hτ f, hw]
  · intro x hs ht
    have he := color_of_ascent σ hσ e hs
    rw [hw, hc] at he
    exact (color_eq_iff τ hτ f _ _).mp (he.symm.trans (color_of_ascent τ hτ f ht))

/-- All fixed-point-free permutations with exactly the specified number of ascents.
The actual cycle length condition is a subset of these permutations. -/
abbrev Rows (n p : ℕ) :=
  {σ : Equiv.Perm (Fin n) // (∀ x, σ x ≠ x) ∧ Fintype.card (Tails σ) = p}

noncomputable instance (n p : ℕ) : Fintype (Rows n p) := Fintype.ofFinite _

private abbrev RunLabels {n p : ℕ} (σ : Rows n p) := Tails σ.val ≃ Fin p

private noncomputable def code (n p : ℕ) (tagged : Sigma (RunLabels (n := n) (p := p))) :
    (Fin n → Fin p) × Equiv.Perm (Fin p) :=
  (color tagged.1.val tagged.1.property.1 tagged.2,
    colorSuccessor tagged.1.val tagged.1.property.1 tagged.2)

private theorem code_injective (n p : ℕ) : Function.Injective (code n p) := by
  rintro ⟨σ, e⟩ ⟨τ, f⟩ heq
  have hw : color σ.val σ.property.1 e = color τ.val τ.property.1 f :=
    congrArg Prod.fst heq
  have hc : colorSuccessor σ.val σ.property.1 e = colorSuccessor τ.val τ.property.1 f :=
    congrArg Prod.snd heq
  have hστ : σ = τ := Subtype.ext (perm_eq_of_codes hw hc)
  subst τ
  have hef : e = f := by
    apply Equiv.ext
    intro x
    have hx := congrFun hw x.val
    simpa [color] using hx
  subst f
  rfl

/-- Labeled runs inject into words together with a permutation of the run colors.
Both sides have the same factor of p factorial for the color labelings. -/
theorem card_rows_le_pow (n p : ℕ) : Fintype.card (Rows n p) ≤ p ^ n := by
  classical
  have h := Fintype.card_le_of_injective _ (code_injective n p)
  have hf (σ : Rows n p) : Fintype.card (RunLabels σ) = p.factorial := by
    let e : RunLabels σ := Fintype.equivFinOfCardEq σ.property.2
    rw [Fintype.card_equiv e, σ.property.2]
  rw [Fintype.card_sigma, Fintype.card_prod, Fintype.card_fun, Fintype.card_perm,
    Fintype.card_fin, Fintype.card_fin] at h
  simp only [hf, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  exact Nat.le_of_mul_le_mul_right h (Nat.factorial_pos p)

/-- The original strict excedance count in the order on the labels. -/
def excedanceCount (σ : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun x => x < σ x).card

theorem card_tails_eq_excedanceCount (σ : Equiv.Perm (Fin n)) :
    Fintype.card (Tails σ) = excedanceCount σ :=
  Fintype.card_subtype _

/-- The cycle cutoff in return-time form, as in the external quotient bridge. -/
def cycleAllowed (k : ℕ) (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ x : Fin n, ∀ j : ℕ, 0 < j → j < k → (σ ^ j) x ≠ x

theorem cycleAllowed_fixedPointFree {k : ℕ} (hk : 2 ≤ k)
    {σ : Equiv.Perm (Fin n)} (hσ : cycleAllowed k σ) :
    ∀ x, σ x ≠ x := by
  intro x
  simpa using hσ x 1 (by decide) (by omega)

/-- The actual permutation enumerator, represented with an admissibility test. -/
noncomputable def originalEnumerator (n k : ℕ) : Polynomial ℝ := by
  classical
  exact ∑ σ : Equiv.Perm (Fin n),
    if cycleAllowed k σ then Polynomial.X ^ excedanceCount σ else 0

private noncomputable def eligible (n k p : ℕ) : Finset (Equiv.Perm (Fin n)) := by
  classical
  exact Finset.univ.filter fun σ => cycleAllowed k σ ∧ excedanceCount σ = p

private theorem coeff_eq_eligible_card (n k p : ℕ) :
    (originalEnumerator n k).coeff p = (eligible n k p).card := by
  classical
  have heq : (originalEnumerator n k).coeff p =
      ∑ σ : Equiv.Perm (Fin n), if cycleAllowed k σ ∧ excedanceCount σ = p then (1 : ℝ) else 0 := by
    unfold originalEnumerator
    rw [Polynomial.finset_sum_coeff]
    apply Finset.sum_congr rfl
    intro σ _
    by_cases hr : cycleAllowed k σ
    · by_cases he : excedanceCount σ = p
      · simp [hr, he, Polynomial.coeff_X_pow]
      · simp [hr, he, Ne.symm he, Polynomial.coeff_X_pow]
    · simp [hr]
  rw [heq, ← Finset.sum_filter]
  simp [eligible]

private theorem eligible_card_le_rows (n k p : ℕ) (hk : 2 ≤ k) :
    (eligible n k p).card ≤ Fintype.card (Rows n p) := by
  classical
  let f : ↥(eligible n k p) → Rows n p := fun σ =>
    ⟨σ.val, cycleAllowed_fixedPointFree hk (Finset.mem_filter.mp σ.property).2.1,
      (card_tails_eq_excedanceCount σ.val).trans (Finset.mem_filter.mp σ.property).2.2⟩
  have h := Fintype.card_le_of_injective f (fun a b hab => Subtype.ext (congrArg (fun x : Rows n p => x.val) hab))
  simpa using h

/-- The nonnegative coefficient envelope for the actual minimum-cycle
excedance polynomial. The bound counts all fixed-point-free permutations
at that excedance count via their labeled decreasing runs. -/
theorem original_coeff_envelope (n k p : ℕ) (hk : 2 ≤ k) :
    0 ≤ (originalEnumerator n k).coeff p ∧
      (originalEnumerator n k).coeff p ≤ (p : ℝ) ^ n := by
  rw [coeff_eq_eligible_card]
  exact ⟨Nat.cast_nonneg _, by
    exact_mod_cast (eligible_card_le_rows n k p hk).trans (card_rows_le_pow n p)⟩

/-- Direct input for the prefix-tail certificate once the quotient identity
for the original row has been supplied. -/
theorem reduced_coeff_envelope {n k : ℕ} {P : Polynomial ℝ} (hk : 2 ≤ k)
    (hrow : originalEnumerator n k = Polynomial.X * P) (j : ℕ) :
    0 ≤ P.coeff j ∧ P.coeff j ≤ ((j : ℝ) + 1) ^ n := by
  have h := original_coeff_envelope n k (j+1) hk
  rw [hrow, Polynomial.coeff_X_mul] at h
  simpa only [Nat.cast_add, Nat.cast_one] using h

#print axioms reduced_coeff_envelope
#print axioms original_coeff_envelope

#print axioms card_rows_le_pow

#print axioms nextTail_injective
#print axioms perm_eq_of_same_runs

#print axioms runEnd_route
#print axioms downRoute_of_runEnd_eq
#print axioms ascent_image_is_max

end OpenMathResearch.LongCycleExcedances.RunColors
