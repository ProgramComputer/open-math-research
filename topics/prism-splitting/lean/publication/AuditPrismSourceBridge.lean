import AuditPrismCountBridge

namespace AuditReference

open PrismSplit PrismFamily Polynomial

private theorem realRoots_multiset {p : Polynomial ℝ} {xs : List ℝ} (h : RealRoots p xs) :
    p.roots = (xs : Multiset ℝ) ∧ xs.length = p.natDegree := by
  have hfac : p = Polynomial.C p.leadingCoeff *
      ((xs : Multiset ℝ).map (fun x => X - Polynomial.C x)).prod := h.2.2
  have hl := leadingCoeff_ne_zero.mpr h.1
  constructor
  · nth_rw 1 [hfac]
    rw [roots_C_mul _ hl, roots_multiset_prod_X_sub_C]
  · nth_rw 1 [hfac]
    rw [natDegree_C_mul_of_isUnit (isUnit_iff_ne_zero.mpr hl),
      natDegree_multiset_prod_X_sub_C_eq_card, Multiset.coe_card]

private theorem alternating_of_getD {xs ys : List ℝ} (hl : xs.length + 1 = ys.length)
    (h : ∀ i < xs.length, ys.getD i 0 ≤ xs.getD i 0 ∧ xs.getD i 0 ≤ ys.getD (i+1) 0) :
    alternatingRoots xs ys := by
  induction xs generalizing ys with
  | nil =>
    obtain ⟨y, rfl⟩ := List.length_eq_one_iff.mp hl.symm
    trivial
  | cons x xs ih =>
    cases ys with
    | nil => simp at hl
    | cons y ys =>
      cases ys with
      | nil => simp at hl
      | cons z zs =>
        have h₀ : y ≤ x ∧ x ≤ z := by
          simpa only [List.getD_cons_zero, List.getD_cons_succ] using h 0 (by simp)
        refine ⟨h₀.1, h₀.2, ih (by simpa only [List.length_cons, Nat.add_right_cancel_iff] using hl) ?_⟩
        intro i hi
        have h₁ := h (i+1) (by simpa only [List.length_cons, Nat.add_lt_add_iff_right] using hi)
        simpa only [List.getD_cons_succ] using h₁

private theorem alternating_of_source {p q : Polynomial ℝ} (hd : p.natDegree+1 = q.natDegree)
    (h : InterleavingPolynomials p q) :
    ∃ xs ys : List ℝ, RealRoots p xs ∧ RealRoots q ys ∧ alternatingRoots xs ys := by
  obtain ⟨xs, ys, hp, hq, horder⟩ := h
  have hlen : xs.length+1 = ys.length := by
    rw [(realRoots_multiset hp).2, (realRoots_multiset hq).2, hd]
  refine ⟨xs, ys, hp, hq, ?_⟩
  rcases horder with hfwd | hrev
  · rcases hfwd with ⟨hlen', _, _⟩ | ⟨_, h⟩
    · omega
    · exact alternating_of_getD hlen h
  · rcases hrev with ⟨hlen', _, _⟩ | ⟨hlen', _⟩ <;> omega

private noncomputable abbrev asReal (p : Polynomial Int) : Polynomial ℝ :=
  p.map (Int.castRingHom ℝ)

private theorem asReal_natDegree (p : Polynomial Int) : (asReal p).natDegree = p.natDegree :=
  Polynomial.natDegree_map_eq_of_injective Int.cast_injective _

private theorem rootList_eval₂ {p : Polynomial Int} {xs : List ℝ} (h : RealRoots (asReal p) xs) (x : ℝ) :
    x ∈ xs ↔ p.eval₂ (Int.castRingHom ℝ) x = 0 := by
  have hr := Polynomial.mem_roots h.1 (a := x)
  rw [(realRoots_multiset h).1] at hr
  simpa only [Multiset.mem_coe, Polynomial.IsRoot, asReal, Polynomial.eval_map] using hr

private theorem noInterleaves_six {p q : Polynomial Int} (hp : p.natDegree = 9) (hq : q.natDegree = 10)
    (h : ¬ ∃ xs ys : List ℝ,
      (∀ x : ℝ, x ∈ xs ↔ p.eval₂ (Int.castRingHom ℝ) x = 0) ∧
      (∀ y : ℝ, y ∈ ys ↔ q.eval₂ (Int.castRingHom ℝ) y = 0) ∧ alternatingRoots xs ys) :
    ¬ InterleavingPolynomials (asReal p) (asReal q) := by
  intro hal
  have hd : (asReal p).natDegree+1 = (asReal q).natDegree := by
    rw [asReal_natDegree, asReal_natDegree, hp, hq]
  obtain ⟨xs, ys, hxs, hys, horder⟩ := alternating_of_source hd hal
  exact h ⟨xs, ys, rootList_eval₂ hxs, rootList_eval₂ hys, horder⟩

private theorem noInterleaves_family {p q : Polynomial Int}
    (hd : p.natDegree+1 = q.natDegree)
    (h : ¬ ((asReal p).roots.card = (asReal p).natDegree ∧
      (asReal q).roots.card = (asReal q).natDegree ∧
      ∃ xs ys : List ℝ, (xs : Multiset ℝ) = (asReal p).roots ∧
        (ys : Multiset ℝ) = (asReal q).roots ∧ alternatingRoots xs ys)) :
    ¬ InterleavingPolynomials (asReal p) (asReal q) := by
  intro hal
  have hdr : (asReal p).natDegree+1 = (asReal q).natDegree := by
    rw [asReal_natDegree, asReal_natDegree, hd]
  obtain ⟨xs, ys, hxs, hys, horder⟩ := alternating_of_source hdr hal
  obtain ⟨hxr, hxd⟩ := realRoots_multiset hxs
  obtain ⟨hyr, hyd⟩ := realRoots_multiset hys
  refine h ⟨?_, ?_, xs, ys, hxr.symm, hyr.symm, horder⟩
  · rwa [hxr, Multiset.coe_card]
  · rwa [hyr, Multiset.coe_card]

/-- The source-level parameters have positive capacities, a valid level and the
    exact split of the last cap into two unit caps. -/
theorem prismSourceAdmissible (a : ℕ) (ha : 6 ≤ a) :
    (∀ c ∈ originalBounds a, 0 < c) ∧
    (originalBounds a).getLast? = some 2 ∧
    splitBounds a = (originalBounds a).dropLast ++ [1, 1] ∧
    0 < a ∧ a < (originalBounds a).sum := by
  refine ⟨?_, ?_, ?_, by omega, ?_⟩
  · intro c hc
    simp [originalBounds] at hc
    rcases hc with ⟨_, rfl⟩ | rfl <;> decide
  · simp [originalBounds]
  · have hlen : 2*a = (2*a-2)+2 := by omega
    calc
      splitBounds a = List.replicate ((2*a-2)+2) 1 := congrArg (List.replicate · 1) hlen
      _ = _ := by simp [originalBounds, List.replicate_add]
  · simp [originalBounds, List.sum_replicate]
    omega

/-- Disproof family expressed only using the independent source vocabulary. -/
theorem prismSourcePublished : PrismPublished := by
  intro a ha
  by_cases h : a = 6
  · subst a
    obtain ⟨p, q, hp, hq, hps, hqs, hal⟩ := AuditExportType.prismSix
    refine ⟨asReal p, asReal q, ?_, ?_, noInterleaves_six hp hq hal⟩
    · have hcaps : List.ofFn unsplitFinCaps = originalBounds 6 := by decide
      rw [← hcaps]
      exact isPrismNumerator_of_slice (by rw [unsplitAffineDimension, List.length_ofFn]) hps
    · have hcaps : List.ofFn splitFinCaps = splitBounds 6 := by decide
      rw [← hcaps]
      exact isPrismNumerator_of_slice (by rw [splitAffineDimension, List.length_ofFn]) hqs
  · let b := a - 1
    have hb : 6 ≤ b := by omega
    have hab : b+1 = a := by omega
    obtain ⟨p, q, hp, hq, hps, hqs, hal⟩ := AuditExportType.prismFamily b hb
    refine ⟨asReal p, asReal q, ?_, ?_, noInterleaves_family (by omega) hal⟩
    · have hpre := isPrismNumerator_of_slice
        (by rw [beforeAffineDimension, List.length_ofFn]) hps
      rw [beforeFinCaps_list, hab, beforeCaps, show 2*b = 2*a-2 by omega] at hpre
      exact hpre
    · have hpost := isPrismNumerator_of_slice
        (by rw [afterAffineDimension, List.length_ofFn]) hqs
      rw [afterFinCaps_list, hab, afterCaps, show 2*b+2 = 2*a by omega] at hpost
      exact hpost

#print axioms prismSourceAdmissible
#print axioms prismSourcePublished

end AuditReference
