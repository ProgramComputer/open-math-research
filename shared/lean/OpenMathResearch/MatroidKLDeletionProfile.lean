import OpenMathResearch.MatroidKLRecurrence

/-!
# Centered coefficient profiles for matroid deletion

The integer-indexed coefficient of `t^h p(t⁻²)` implements the Laurent
polynomial notation used in the Braden–Vysogorets deletion argument.
-/

open Finset Polynomial
open scoped BigOperators Polynomial

noncomputable section

namespace OpenMathResearch.MatroidKL

/-- Coefficient of `t^k` in the centered expression `t^h p(t⁻²)`. -/
def centeredCoeff (h : ℕ) (p : ℤ[X]) (k : ℤ) : ℤ :=
  let d := (h : ℤ) - k
  if 0 ≤ d ∧ d % 2 = 0 then p.coeff (d / 2).toNat else 0

theorem centeredCoeff_at_exponent (h : ℕ) (p : ℤ[X]) (i : ℕ) :
    centeredCoeff h p ((h : ℤ) - 2 * (i : ℤ)) = p.coeff i := by
  have hd : (h : ℤ) - ((h : ℤ) - 2 * (i : ℤ)) = 2 * (i : ℤ) := by omega
  have hi : ((2 * (i : ℤ)) / 2).toNat = i := by omega
  simp [centeredCoeff, hd, hi, Int.mul_emod_right]

private theorem centeredCoeff_mul_X_pow (h g : ℕ) (hg : g ≤ h) (p : ℤ[X]) (k : ℤ) :
    centeredCoeff h (X ^ g * p) k = centeredCoeff (h - g) p (k + (g : ℤ)) := by
  have he : ((h - g : ℕ) : ℤ) - (k + (g : ℤ)) = (h : ℤ) - k - 2 * (g : ℤ) := by omega
  rw [centeredCoeff, centeredCoeff]
  simp only [he, coeff_X_pow_mul']
  split_ifs with hd hSize hOther hOther hOther
  · congr 1
    omega
  · exfalso
    omega
  · exfalso
    omega
  · rfl
  · exfalso
    omega
  · rfl

private theorem centeredCoeff_sum {ι : Type*} (s : Finset ι) (p : ι → ℤ[X]) (h : ℕ) (k : ℤ) :
    centeredCoeff h (∑ i ∈ s, p i) k = ∑ i ∈ s, centeredCoeff h (p i) k := by
  by_cases hd : 0 ≤ (h : ℤ) - k ∧ ((h : ℤ) - k) % 2 = 0
  · simp [centeredCoeff, hd, Polynomial.finsetSum_coeff]
  · simp [centeredCoeff, hd]

variable {α : Type*} [PartialOrder α] [OrderTop α] [LocallyFiniteOrder α]

/-- Sum the translated coefficients of the profiles indexed by the upper interval. -/
def translatedSum (rank : α → ℕ) (v : α → ℤ → ℤ) (a : α) (k : ℤ) : ℤ :=
  ∑ b ∈ Finset.Icc a ⊤, v b (k + ((rank b : ℤ) - (rank a : ℤ)))

theorem centeredCoeff_shiftedSum (rank : α → ℕ) (hRank : Monotone rank)
    (p : α → ℤ[X]) (a : α) (k : ℤ) :
    centeredCoeff (height rank a) (shiftedSum rank p a) k =
      translatedSum rank (fun b => centeredCoeff (height rank b) (p b)) a k := by
  rw [shiftedSum_apply, centeredCoeff_sum, translatedSum]
  apply Finset.sum_congr rfl
  intro b hb
  have hab := hRank (Finset.mem_Icc.mp hb).1
  have hbt := hRank (le_top : b ≤ ⊤)
  have hGap : rank b - rank a ≤ height rank a := by unfold height; omega
  have hHeight : height rank a - (rank b - rank a) = height rank b := by unfold height; omega
  rw [centeredCoeff_mul_X_pow _ _ hGap, hHeight, Nat.cast_sub hab]

/-- Nonnegative coordinate support and symmetry of all translated upper sums. -/
structure IsPerverseProfile (rank : α → ℕ) (v : α → ℤ → ℤ) : Prop where
  nonneg (a : α) (k : ℤ) (hk : k < 0) : v a k = 0
  symmetric (a : α) (k : ℤ) : translatedSum rank v a k = translatedSum rank v a (-k)

private theorem translatedSum_split (rank : α → ℕ) (v : α → ℤ → ℤ) (a : α) (k : ℤ) :
    translatedSum rank v a k = v a k +
      ∑ b ∈ Finset.Ioc a ⊤, v b (k + ((rank b : ℤ) - (rank a : ℤ))) := by
  rw [translatedSum, Finset.Icc_eq_cons_Ioc (le_top : a ≤ ⊤), Finset.sum_cons]
  simp

/-- Perverse profiles are uniquely determined by their coordinate constant terms. -/
theorem IsPerverseProfile.ext_of_constants (rank : α → ℕ) (hRank : StrictMono rank)
    {v w : α → ℤ → ℤ} (hv : IsPerverseProfile rank v) (hw : IsPerverseProfile rank w)
    (hConst : ∀ a, v a 0 = w a 0) : v = w := by
  suffices h : ∀ a : α, ∀ k : ℤ, v a k = w a k by
    exact funext fun a => funext (h a)
  intro a
  induction a using (measure (height rank)).wf.induction with
  | h a ih =>
    intro k
    rcases lt_trichotomy k 0 with hneg | heq | hpos
    · rw [hv.nonneg a k hneg, hw.nonneg a k hneg]
    · simpa only [heq] using hConst a
    have hLT : -k < 0 := by omega
    have hV := hv.symmetric a k
    have hW := hw.symmetric a k
    simp only [translatedSum_split, hv.nonneg a (-k) hLT, hw.nonneg a (-k) hLT, zero_add] at hV hW
    have hSum (j : ℤ) : (∑ b ∈ Finset.Ioc a ⊤, v b (j + ((rank b : ℤ) - (rank a : ℤ)))) =
        ∑ b ∈ Finset.Ioc a ⊤, w b (j + ((rank b : ℤ) - (rank a : ℤ))) := by
      apply Finset.sum_congr rfl
      intro b hb
      have hab := hRank (Finset.mem_Ioc.mp hb).1
      have hbt := hRank.monotone (le_top : b ≤ ⊤)
      apply ih b
      change height rank b < height rank a
      unfold height
      omega
    rw [hSum k, hSum (-k)] at hV
    omega

private theorem centeredCoeff_symm (h : ℕ) (p : ℤ[X]) (hp : p.reflect h = p)
    (hDegree : p.natDegree ≤ h) (k : ℤ) : centeredCoeff h p k = centeredCoeff h p (-k) := by
  unfold centeredCoeff
  dsimp
  split_ifs with hd hd' hd'
  · let i := (((h : ℤ) - k) / 2).toNat
    have hi : i ≤ h := by dsimp [i]; omega
    have hi' : h - i = (((h : ℤ) - -k) / 2).toNat := by dsimp [i]; omega
    have hc := congrArg (fun f : ℤ[X] => f.coeff i) hp
    simp only [coeff_reflect, revAt_le hi, hi'] at hc
    exact hc.symm
  · exact Polynomial.natDegree_le_iff_coeff_eq_zero.mp hDegree _ (by omega)
  · exact (Polynomial.natDegree_le_iff_coeff_eq_zero.mp hDegree _ (by omega)).symm
  · rfl

theorem centeredCoeff_one (h : ℕ) (p : ℤ[X]) : centeredCoeff h p 1 =
    if h % 2 = 1 then p.coeff ((h - 1) / 2) else 0 := by
  unfold centeredCoeff
  dsimp
  split_ifs with hd hp hp
  · congr 1
    omega
  · omega
  · omega
  · rfl

variable [Fintype α]

omit [LocallyFiniteOrder α] in
private theorem IsKLFamily.centeredCoeff_nonneg (rank : α → ℕ) (p : α → ℤ[X])
    (hp : IsKLFamily rank (fun a i => (p a).coeff i)) (a : α) {k : ℤ} (hk : k < 0) :
    centeredCoeff (height rank a) (p a) k = 0 := by
  unfold centeredCoeff
  dsimp
  split_ifs with hd
  · by_cases ha : height rank a = 0
    · have hi : (((height rank a : ℤ) - k) / 2).toNat ≠ 0 := by omega
      rw [hp.rank_zero a ha, if_neg hi]
    · exact hp.high_coeff a _ (Nat.pos_of_ne_zero ha) (by omega)
  · rfl

private def topConstant {γ : Type*} [Top γ] (a : γ) : ℤ := by
  classical
  exact if a = ⊤ then 1 else 0

omit [LocallyFiniteOrder α] in
theorem IsKLFamily.centeredCoeff_zero (rank : α → ℕ) (hRank : StrictMono rank) (p : α → ℤ[X])
    (hp : IsKLFamily rank (fun a i => (p a).coeff i)) (a : α) :
    centeredCoeff (height rank a) (p a) 0 = topConstant a := by
  classical
  unfold topConstant
  by_cases ha : a = ⊤
  · subst a
    have ht : height rank (⊤ : α) = 0 := by simp [height]
    simp [ht, centeredCoeff, hp.rank_zero _ ht 0]
  · rw [if_neg ha]
    have h₀ : 0 < height rank a := by
      have h := hRank (lt_of_le_of_ne le_top ha)
      unfold height
      omega
    unfold centeredCoeff
    dsimp
    split_ifs with hd
    · exact hp.high_coeff a _ h₀ (by omega)
    · rfl

/-- The centered Kazhdan–Lusztig coefficient family has symmetric translated upper sums. -/
theorem IsKLFamily.isPerverseProfile (rank : α → ℕ) (hRank : StrictMono rank) (p : α → ℤ[X])
    (hp : IsKLFamily rank (fun a i => (p a).coeff i)) :
    IsPerverseProfile rank (fun a => centeredCoeff (height rank a) (p a)) := by
  constructor
  · exact hp.centeredCoeff_nonneg rank p
  · intro a k
    rw [← centeredCoeff_shiftedSum rank hRank.monotone p,
      ← centeredCoeff_shiftedSum rank hRank.monotone p]
    apply centeredCoeff_symm
    · exact shiftedSum_reflect_of_isKLFamily rank p hp a
    · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
      intro i hi
      rw [coeff_shiftedSum]
      exact hp.zCoeff_eq_zero_of_height_lt rank hRank a hi

section Push

variable {β : Type*} [PartialOrder β] [OrderTop β] [LocallyFiniteOrder β]

/-- Translate the profile from each source coordinate by its discrepancy, then add by fibers. -/
def pushProfile (rA : α → ℕ) (rB : β → ℕ) (f : α → β) (v : α → ℤ → ℤ)
    (b : β) (k : ℤ) : ℤ := by
  classical
  exact ∑ a ∈ Finset.univ.filter (fun a => f a = b), v a (k + ((rA a : ℤ) - (rB b : ℤ)))

/-- The translated upper sum commutes with a rank-preserving lift of the deletion order. -/
theorem translatedSum_pushProfile (rA : α → ℕ) (rB : β → ℕ) (f : α → β) (lift : β → α)
    (hAdj : ∀ a b, b ≤ f a ↔ lift b ≤ a) (hLift : ∀ b, rA (lift b) = rB b)
    (v : α → ℤ → ℤ) (b : β) (k : ℤ) :
    translatedSum rB (pushProfile rA rB f v) b k = translatedSum rA v (lift b) k := by
  classical
  let s := Finset.Icc (lift b) ⊤
  let t := Finset.Icc b ⊤
  have hMem (a : α) : a ∈ s ↔ f a ∈ t := by
    simp [s, t, hAdj]
  have hFibre (d : β) (hd : d ∈ t) : (Finset.univ.filter fun a => f a = d) = s.filter fun a => f a = d := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => ⟨(hMem a).mpr (h.symm ▸ hd), h⟩, And.right⟩
  simp only [translatedSum]
  calc
    _ = ∑ d ∈ t, ∑ a ∈ s.filter (fun a => f a = d), v a (k + ((rA a : ℤ) - (rA (lift b) : ℤ))) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [pushProfile, hFibre d hd]
      apply Finset.sum_congr rfl
      intro a _
      congr 1
      rw [hLift]
      omega
    _ = _ := Finset.sum_fiberwise_of_maps_to (fun a ha => (hMem a).mp ha) _

omit [LocallyFiniteOrder β] in
private theorem pushProfile_nonneg (rA : α → ℕ) (rB : β → ℕ) (f : α → β)
    (hTop : f ⊤ = ⊤) (hTopRank : rA ⊤ = rB ⊤)
    (hUpper : ∀ a, rA a ≤ rB (f a) + 1) {v : α → ℤ → ℤ}
    (hv : IsPerverseProfile rA v) (hConst : ∀ a, v a 0 = topConstant a)
    (b : β) (k : ℤ) (hk : k < 0) : pushProfile rA rB f v b k = 0 := by
  classical
  rw [pushProfile]
  apply Finset.sum_eq_zero
  intro a ha
  have he := (Finset.mem_filter.mp ha).2
  have h := hUpper a
  rw [he] at h
  let j := k + ((rA a : ℤ) - (rB b : ℤ))
  change v a j = 0
  by_cases hn : j < 0
  · exact hv.nonneg a j hn
  · have hz : j = 0 := by dsimp [j] at hn ⊢; omega
    have ha' : a ≠ ⊤ := by
      intro hEq
      subst a
      rw [hTop] at he
      subst b
      dsimp [j] at hz
      rw [hTopRank] at hz
      omega
    rw [hz, hConst, topConstant, if_neg ha']

private theorem pushProfile_constants (rA : α → ℕ) (rB : β → ℕ) (f : α → β)
    (hTop : f ⊤ = ⊤) (hTopRank : rA ⊤ = rB ⊤)
    (hGap : ∀ a, rB (f a) ≤ rA a ∧ rA a ≤ rB (f a) + 1) (v : α → ℤ → ℤ)
    (hConst : ∀ a, v a 0 = topConstant a)
    (hCorrection : ∀ a, rA a = rB (f a) + 1 → v a 1 = 0) (b : β) :
    pushProfile rA rB f v b 0 = topConstant b := by
  classical
  have hOthers (a : α) (ha : f a = b) (hNe : a ≠ ⊤) :
      v a (0 + ((rA a : ℤ) - (rB b : ℤ))) = 0 := by
    obtain ⟨hLe, hHi⟩ := hGap a
    rw [ha] at hLe hHi
    by_cases hZero : rA a = rB b
    · simp [hZero, hConst, topConstant, hNe]
    · have hOne : rA a = rB b + 1 := by omega
      have hj : (0 : ℤ) + ((rA a : ℤ) - (rB b : ℤ)) = 1 := by omega
      rw [hj]
      exact hCorrection a (by rwa [ha])
  rw [pushProfile, topConstant]
  by_cases hb : b = ⊤
  · rw [if_pos hb, Finset.sum_eq_single (⊤ : α)]
    · subst b
      simp [hTopRank, hConst, topConstant]
    · exact fun a ha hn => hOthers a (Finset.mem_filter.mp ha).2 hn
    · simp [hTop, hb]
  · rw [if_neg hb]
    apply Finset.sum_eq_zero
    intro a ha
    have hEq := (Finset.mem_filter.mp ha).2
    exact hOthers a hEq (fun ht => hb (hEq.symm.trans (ht ▸ hTop)))

/-- The Z-sum is preserved when every correction at a discrepancy-one coordinate vanishes. -/
theorem shiftedSum_eq_of_deletionPush [Fintype β] [OrderBot α] [OrderBot β]
    (rA : α → ℕ) (rB : β → ℕ) (hA : StrictMono rA) (hB : StrictMono rB)
    (f : α → β) (lift : β → α) (hAdj : ∀ a b, b ≤ f a ↔ lift b ≤ a)
    (hLift : ∀ b, rA (lift b) = rB b) (hTop : f ⊤ = ⊤) (hTopRank : rA ⊤ = rB ⊤)
    (hGap : ∀ a, rB (f a) ≤ rA a ∧ rA a ≤ rB (f a) + 1)
    (p : α → ℤ[X]) (q : β → ℤ[X])
    (hp : IsKLFamily rA (fun a i => (p a).coeff i)) (hq : IsKLFamily rB (fun b i => (q b).coeff i))
    (hCorrection : ∀ a, rA a = rB (f a) + 1 → centeredCoeff (height rA a) (p a) 1 = 0) :
    shiftedSum rA p ⊥ = shiftedSum rB q ⊥ := by
  classical
  let v : α → ℤ → ℤ := fun a => centeredCoeff (height rA a) (p a)
  let w : β → ℤ → ℤ := fun b => centeredCoeff (height rB b) (q b)
  have hv : IsPerverseProfile rA v := hp.isPerverseProfile rA hA p
  have hw : IsPerverseProfile rB w := hq.isPerverseProfile rB hB q
  have hConst (a : α) : v a 0 = topConstant a := hp.centeredCoeff_zero rA hA p a
  have hPush : IsPerverseProfile rB (pushProfile rA rB f v) := by
    constructor
    · exact pushProfile_nonneg rA rB f hTop hTopRank (fun a => (hGap a).2) hv hConst
    · intro b k
      rw [translatedSum_pushProfile rA rB f lift hAdj hLift,
        translatedSum_pushProfile rA rB f lift hAdj hLift]
      exact hv.symmetric (lift b) k
  have hEqual : pushProfile rA rB f v = w := by
    apply hPush.ext_of_constants rB hB hw
    intro b
    rw [pushProfile_constants rA rB f hTop hTopRank hGap v hConst hCorrection]
    exact (hq.centeredCoeff_zero rB hB q b).symm
  have hBot : lift ⊥ = ⊥ := le_antisymm ((hAdj ⊥ ⊥).mp bot_le) bot_le
  have hrBot := hLift ⊥
  rw [hBot] at hrBot
  have hHeight : height rA ⊥ = height rB ⊥ := by simp [height, hTopRank, hrBot]
  have he (k : ℤ) : centeredCoeff (height rA ⊥) (shiftedSum rA p ⊥) k =
      centeredCoeff (height rB ⊥) (shiftedSum rB q ⊥) k := by
    rw [centeredCoeff_shiftedSum rA hA.monotone p, centeredCoeff_shiftedSum rB hB.monotone q]
    change translatedSum rA v ⊥ k = translatedSum rB w ⊥ k
    rw [← hEqual, translatedSum_pushProfile rA rB f lift hAdj hLift, hBot]
  ext i
  simpa only [hHeight, centeredCoeff_at_exponent] using he ((height rA ⊥ : ℤ) - 2 * (i : ℤ))

end Push

#print axioms IsPerverseProfile.ext_of_constants
#print axioms centeredCoeff_shiftedSum
#print axioms IsKLFamily.isPerverseProfile
#print axioms IsKLFamily.centeredCoeff_zero
#print axioms translatedSum_pushProfile
#print axioms shiftedSum_eq_of_deletionPush

end OpenMathResearch.MatroidKL
