import Mathlib.Data.Finset.Powerset
import OpenMathResearch.MatroidFlatPolynomial
import CircuitNarayanaCoefficients

open Set Matroid
open scoped BigOperators

noncomputable section

namespace OpenMathResearch.MatroidKL

variable {α : Type*} [Finite α]

/-- A rank-r circuit is specified by its r+1 ground elements and its r-element bases. -/
structure CircuitBases (M : Matroid α) (r : ℕ) : Prop where
  ground_card : M.E.ncard = r + 1
  bases (B : Set α) : M.IsBase B ↔ B ⊆ M.E ∧ B.ncard = r

variable {M : Matroid α} {r : ℕ} (h : CircuitBases M r)

include h

omit [Finite α] in
theorem CircuitBases.rank_eq : M.eRank.toNat = r := by
  obtain ⟨B, hB⟩ := M.exists_isBase
  rw [← hB.encard_eq_eRank, ← Set.ncard_def]
  exact ((h.bases B).mp hB).2

theorem CircuitBases.indep_iff {I : Set α} : M.Indep I ↔ I ⊆ M.E ∧ I.ncard ≤ r := by
  constructor
  · intro hi
    obtain ⟨B, hB, hIB⟩ := hi.exists_isBase_superset
    exact ⟨hi.subset_ground, (Set.ncard_le_ncard hIB (Set.toFinite _)).trans_eq ((h.bases B).mp hB).2⟩
  · rintro ⟨hIE, hI⟩
    have hIC : I.encard ≤ (r : ℕ∞) := by
      rw [← (Set.toFinite I).cast_ncard_eq]
      exact_mod_cast hI
    have hEC : (r : ℕ∞) ≤ M.E.encard := by
      rw [← (Set.toFinite M.E).cast_ncard_eq, h.ground_card]
      exact_mod_cast Nat.le_succ r
    obtain ⟨B, hIB, hBG, hBC⟩ := Set.exists_superset_subset_encard_eq hIE hIC hEC
    have hr : B.ncard = r := by
      rw [Set.ncard_def, hBC, ENat.toNat_coe]
    exact ((h.bases B).mpr ⟨hBG, hr⟩).indep.subset hIB

theorem CircuitBases.isFlat_of_ncard_lt {X : Set α} (hXE : X ⊆ M.E) (hXR : X.ncard < r) : M.IsFlat X := by
  apply Matroid.isFlat_iff_closure_eq.mpr
  apply Set.Subset.antisymm _ (M.subset_closure X hXE)
  intro x hx
  by_contra hxX
  have hI := (h.indep_iff).mpr ⟨hXE, hXR.le⟩
  have hI' : M.Indep (insert x X) := by
    apply (h.indep_iff).mpr
    refine ⟨Set.insert_subset (M.closure_subset_ground _ hx) hXE, ?_⟩
    rw [Set.ncard_insert_of_notMem hxX (Set.toFinite _)]
    omega
  exact hxX ((hI.mem_closure_iff'.mp hx).2 hI')

omit [Finite α] in
theorem CircuitBases.ncard_lt_of_proper_flat {F : Flat M} (hF : F ≠ ⊤) : F.val.ncard < r := by
  by_contra! hRank
  obtain ⟨B, hBF, hCard⟩ := Set.exists_subset_card_eq hRank
  have hB : M.IsBase B := (h.bases B).mpr ⟨hBF.trans F.property.subset_ground, hCard⟩
  have hc := M.closure_mono hBF
  rw [hB.closure_eq, F.property.closure] at hc
  exact hF (Subtype.ext (Set.Subset.antisymm F.property.subset_ground hc))

theorem CircuitBases.flatRank_of_proper {F : Flat M} (hF : F ≠ ⊤) : flatRank M F = F.val.ncard := by
  have hi := h.indep_iff.mpr ⟨F.property.subset_ground, (h.ncard_lt_of_proper_flat hF).le⟩
  change (M.eRk F.val).toNat = F.val.ncard
  rw [hi.eRk_eq_encard, Set.ncard_def]

omit h

private def finiteSetFinset (S : Set α) : Finset α := (Set.toFinite S).toFinset

@[simp] private theorem coe_finiteSetFinset (S : Set α) : ↑(finiteSetFinset S) = S := by
  simp [finiteSetFinset]

@[simp] private theorem card_finiteSetFinset (S : Set α) : (finiteSetFinset S).card = S.ncard := by
  exact (Set.ncard_eq_toFinset_card S (Set.toFinite S)).symm

private abbrev rankLayer (F : Flat M) (k : ℕ) := {G : Flat M // F ≤ G ∧ flatRank M G - flatRank M F = k}

private instance (F : Flat M) (k : ℕ) : Fintype (rankLayer F k) := Fintype.ofFinite _


include h

private theorem CircuitBases.rankLayer_card (F : Flat M) (k : ℕ) (hk : k < height (flatRank M) F) :
    Fintype.card (rankLayer F k) = (height (flatRank M) F + 1).choose k := by
  classical
  have hF : F ≠ ⊤ := by
    intro hf
    rw [hf, height, Nat.sub_self] at hk
    exact Nat.not_lt_zero _ hk
  have hRankF := h.flatRank_of_proper hF
  have hBoundF := h.ncard_lt_of_proper_flat hF
  have hHeight : height (flatRank M) F = r - F.val.ncard := by
    rw [height, flatRank_top, h.rank_eq, hRankF]
  let T := finiteSetFinset (M.E \ F.val)
  have hT : T.card = height (flatRank M) F + 1 := by
    have hc := Set.ncard_sdiff_add_ncard_of_subset F.property.subset_ground (Set.toFinite _)
    rw [h.ground_card] at hc
    dsimp [T]
    rw [card_finiteSetFinset, hHeight]
    omega
  have hGP (G : rankLayer F k) : G.val ≠ ⊤ := by
    intro hTop
    have hGap := G.property.2
    rw [hTop] at hGap
    have hh : height (flatRank M) F = k := hGap
    omega
  let map : rankLayer F k → ↑(T.powersetCard k) := fun G => ⟨finiteSetFinset (G.val.val \ F.val), by
    apply Finset.mem_powersetCard.mpr
    constructor
    · intro x hx
      change x ∈ (↑(finiteSetFinset (G.val.val \ F.val)) : Set α) at hx
      rw [coe_finiteSetFinset] at hx
      change x ∈ (↑(finiteSetFinset (M.E \ F.val)) : Set α)
      rw [coe_finiteSetFinset]
      exact ⟨G.val.property.subset_ground hx.1, hx.2⟩
    · rw [card_finiteSetFinset]
      have hSub : F.val ⊆ G.val.val := G.property.1
      have hc := Set.ncard_sdiff_add_ncard_of_subset hSub (Set.toFinite _)
      have hg : G.val.val.ncard - F.val.ncard = k := calc
        _ = flatRank M G.val - flatRank M F :=
          congrArg₂ (· - ·) (h.flatRank_of_proper (hGP G)).symm hRankF.symm
        _ = k := G.property.2
      omega⟩
  have hInjective : Function.Injective map := by
    intro B C hBC
    have hs : B.val.val \ F.val = C.val.val \ F.val := by
      have hEq : finiteSetFinset (B.val.val \ F.val) = finiteSetFinset (C.val.val \ F.val) :=
        congrArg Subtype.val hBC
      simpa using congrArg (fun t : Finset α => (t : Set α)) hEq
    have hB : F.val ⊆ B.val.val := B.property.1
    have hC : F.val ⊆ C.val.val := C.property.1
    apply Subtype.ext
    apply Subtype.ext
    rw [← Set.sdiff_union_of_subset hB, ← Set.sdiff_union_of_subset hC, hs]
  have hSurjective : Function.Surjective map := by
    intro D
    have hD := Finset.mem_powersetCard.mp D.property
    have hSubD : (D.val : Set α) ⊆ M.E \ F.val := by
      simpa [T] using (show (D.val : Set α) ⊆ (T : Set α) from hD.1)
    have hDisj : Disjoint F.val (D.val : Set α) := by
      rw [Set.disjoint_left]
      exact fun _ hF' hD' => (hSubD hD').2 hF'
    have hU : F.val ∪ (D.val : Set α) ⊆ M.E := Set.union_subset F.property.subset_ground (hSubD.trans Set.diff_subset)
    have hCard : (F.val ∪ (D.val : Set α)).ncard = F.val.ncard + k := by
      rw [Set.ncard_union_eq hDisj, Set.ncard_coe_Finset, hD.2]
    have hSmall : (F.val ∪ (D.val : Set α)).ncard < r := by
      rw [hHeight] at hk
      omega
    let G : Flat M := ⟨F.val ∪ (D.val : Set α), h.isFlat_of_ncard_lt hU hSmall⟩
    have hG : G ≠ ⊤ := by
      intro htop
      have hEq : F.val ∪ (D.val : Set α) = M.E := congrArg Subtype.val htop
      rw [hEq, h.ground_card] at hSmall
      omega
    have hGap : flatRank M G - flatRank M F = k := by
      rw [h.flatRank_of_proper hG, hRankF]
      change (F.val ∪ (D.val : Set α)).ncard - F.val.ncard = k
      rw [hCard]
      omega
    have hFD : F ≤ G := Set.subset_union_left
    refine ⟨⟨G, hFD, hGap⟩, Subtype.ext ?_⟩
    have hEq : (F.val ∪ (D.val : Set α)) \ F.val = (D.val : Set α) := by
      ext x
      constructor
      · exact fun hx => hx.1.resolve_left hx.2
      · exact fun hx => ⟨Or.inr hx, (hSubD hx).2⟩
    apply Finset.coe_injective
    change (↑(finiteSetFinset ((F.val ∪ (D.val : Set α)) \ F.val)) : Set α) = (D.val : Set α)
    rw [coe_finiteSetFinset, hEq]
  rw [Fintype.card_congr (Equiv.ofBijective map ⟨hInjective, hSurjective⟩),
    Fintype.card_coe, Finset.card_powersetCard, hT]


omit h

private theorem zCoeff_eq_inclusive (rank : Flat M → ℕ) (p : Flat M → ℕ → ℤ) (F : Flat M) (i : ℕ) :
    zCoeff rank p F i = ∑ G ∈ Finset.Icc F ⊤,
      if rank G - rank F ≤ i then p G (i - (rank G - rank F)) else 0 := by
  classical
  rw [Finset.Icc_eq_cons_Ioc (le_top : F ≤ ⊤), Finset.sum_cons, zCoeff, upperTail]
  simp only [Nat.sub_self, Nat.zero_le, if_true, Nat.sub_zero]
  congr 1
  exact (Finset.sum_subtype (Finset.Ioc F ⊤)
    (fun G => (Finset.mem_Ioc.trans (and_iff_left (le_top : G ≤ ⊤))))
    (fun G => if rank G - rank F ≤ i then p G (i - (rank G - rank F)) else 0)).symm

private def circuitCandidate (M : Matroid α) (F : Flat M) (i : ℕ) : ℤ :=
  circuitKLCoeff (height (flatRank M) F) i

private theorem height_of_rank_gap (F G : Flat M) (hFG : F ≤ G) :
    height (flatRank M) G = height (flatRank M) F - (flatRank M G - flatRank M F) := by
  have hMono := (strictMono_flatRank M).monotone
  have h₁ := hMono hFG
  have h₂ := hMono (le_top : G ≤ ⊤)
  unfold height
  omega

include h

private theorem candidate_below_top (F : Flat M) (i : ℕ) (hi : i < height (flatRank M) F) :
    zCoeff (flatRank M) (circuitCandidate M) F i =
      ∑ k ∈ Finset.range (i + 1), ((height (flatRank M) F + 1).choose k : ℤ) *
        circuitKLCoeff (height (flatRank M) F - k) (i - k) := by
  classical
  let gap (G : Flat M) := flatRank M G - flatRank M F
  let S := (Finset.Icc F ⊤).filter (fun G => gap G ≤ i)
  let T := Finset.range (i + 1)
  have hMaps (G : Flat M) (hG : G ∈ S) : gap G ∈ T := by
    have hle := (Finset.mem_filter.mp hG).2
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hle)
  calc
    _ = ∑ G ∈ S, circuitCandidate M G (i - gap G) := by
      rw [zCoeff_eq_inclusive, Finset.sum_filter]
    _ = ∑ k ∈ T, ∑ G ∈ S.filter (fun G => gap G = k), circuitCandidate M G (i - gap G) :=
      (Finset.sum_fiberwise_of_maps_to hMaps _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      have hki : k ≤ i := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      have hMem (G : Flat M) : G ∈ S.filter (fun G => gap G = k) ↔
          F ≤ G ∧ flatRank M G - flatRank M F = k := by
        simp only [S, Finset.mem_filter, Finset.mem_Icc, and_iff_left le_top]
        constructor
        · rintro ⟨⟨h₁, _⟩, h₂⟩
          exact ⟨h₁, h₂⟩
        · rintro ⟨h₁, h₂⟩
          exact ⟨⟨h₁, by dsimp [gap]; rw [h₂]; exact hki⟩, h₂⟩
      calc
        _ = ∑ G ∈ S.filter (fun G => gap G = k),
            circuitKLCoeff (height (flatRank M) F - k) (i - k) := by
          apply Finset.sum_congr rfl
          intro G hG
          obtain ⟨hFG, hGap⟩ := (hMem G).mp hG
          rw [circuitCandidate, height_of_rank_gap F G hFG, hGap]
          rw [show gap G = k from hGap]
        _ = ∑ _ : rankLayer F k, circuitKLCoeff (height (flatRank M) F - k) (i - k) :=
          Finset.sum_subtype _ hMem _
        _ = _ := by
          simp [Finset.sum_const, nsmul_eq_mul, h.rankLayer_card F k (hki.trans_lt hi)]

omit h

private theorem candidate_at_or_above_top (F : Flat M) (i : ℕ) (hi : height (flatRank M) F ≤ i) :
    zCoeff (flatRank M) (circuitCandidate M) F i = if i = height (flatRank M) F then 1 else 0 := by
  classical
  rw [zCoeff_eq_inclusive, Finset.sum_eq_single (⊤ : Flat M)]
  · have hTop : height (flatRank M) (⊤ : Flat M) = 0 := Nat.sub_self _
    unfold circuitCandidate
    rw [show flatRank M ⊤ - flatRank M F = height (flatRank M) F from rfl]
    simp [hi, hTop, circuitKLCoeff, show i - height (flatRank M) F = 0 ↔
      i = height (flatRank M) F by omega]
  · intro G hG hTop
    have hFG := (Finset.mem_Icc.mp hG).1
    have hGG := strictMono_flatRank M (lt_of_le_of_ne (le_top : G ≤ ⊤) hTop)
    have hPos : 0 < height (flatRank M) G := by unfold height; omega
    let k := flatRank M G - flatRank M F
    by_cases hk : k ≤ i
    · rw [if_pos hk, circuitCandidate]
      apply circuitKLCoeff_high _ _ hPos
      have he := height_of_rank_gap F G hFG
      change height (flatRank M) G = height (flatRank M) F - k at he
      change height (flatRank M) G ≤ 2 * (i - k)
      omega
    · exact if_neg hk
  · simp

include h

private theorem candidate_z_clear (F : Flat M) (i : ℕ) :
    ((height (flatRank M) F + 1 : ℕ) : ℤ) *
      zCoeff (flatRank M) (circuitCandidate M) F i =
    ((height (flatRank M) F + 1).choose i : ℤ) * ((height (flatRank M) F + 1).choose (i + 1) : ℤ) := by
  by_cases hi : i < height (flatRank M) F
  · rw [candidate_below_top h F i hi, circuitKLCoeff_convolution _ _ hi]
    exact circuitNarayana_clear _ _ hi.le
  · have hi' := Nat.le_of_not_gt hi
    rw [candidate_at_or_above_top F i hi']
    by_cases he : i = height (flatRank M) F
    · subst i
      simp [Nat.choose_succ_self]
    · simp [he, Nat.choose_eq_zero_of_lt (show height (flatRank M) F + 1 < i + 1 by omega)]

private theorem circuitCandidate_isKLFamily : IsKLFamily (flatRank M) (circuitCandidate M) where
  rank_zero := by
    intro F hF i
    simp [circuitCandidate, hF, circuitKLCoeff]
  high_coeff := by
    intro F i hPos hHigh
    exact circuitKLCoeff_high _ _ hPos hHigh
  palindrome := by
    intro F i hi
    let m := height (flatRank M) F
    have hi' : i ≤ m := by
      change 2 * i < m at hi
      omega
    have ha := candidate_z_clear h F i
    have hb := candidate_z_clear h F (m - i)
    change ((m + 1 : ℕ) : ℤ) * zCoeff (flatRank M) (circuitCandidate M) F i =
      ((m + 1).choose i : ℤ) * ((m + 1).choose (i + 1) : ℤ) at ha
    change ((m + 1 : ℕ) : ℤ) * zCoeff (flatRank M) (circuitCandidate M) F (m - i) =
      ((m + 1).choose (m - i) : ℤ) * ((m + 1).choose (m - i + 1) : ℤ) at hb
    have hA : (m + 1).choose (m - i) = (m + 1).choose (i + 1) := by
      rw [show m - i = m + 1 - (i + 1) by omega,
        Nat.choose_symm (show i + 1 ≤ m + 1 by omega)]
    have hB : (m + 1).choose (m - i + 1) = (m + 1).choose i := by
      rw [show m - i + 1 = m + 1 - i by omega,
        Nat.choose_symm (show i ≤ m + 1 by omega)]
    rw [hA, hB, mul_comm (↑((m + 1).choose (i + 1)) : ℤ)] at hb
    exact mul_left_cancel₀ (show ((m + 1 : ℕ) : ℤ) ≠ 0 by positivity) (ha.trans hb.symm)

/-- The Z-polynomial of an actual circuit matroid has the Narayana coefficients. -/
theorem CircuitBases.narayana_coeff (i : ℕ) :
    ((r + 1 : ℕ) : ℤ) * (matroidZ M).coeff i =
    ((r + 1).choose i : ℤ) * ((r + 1).choose (i + 1) : ℤ) := by
  have hKL : circuitCandidate M = flatKLCoeff M :=
    IsKLFamily.eq_klCoeff _ (strictMono_flatRank M) (circuitCandidate_isKLFamily h)
  have hHeight : height (flatRank M) (⊥ : Flat M) = r := by
    rw [height, flatRank_top, flatRank_bot, Nat.sub_zero, h.rank_eq]
  have hZ := candidate_z_clear h ⊥ i
  rw [hHeight, hKL, ← matroidZCoeff, ← coeff_matroidZ] at hZ
  exact hZ

end OpenMathResearch.MatroidKL
