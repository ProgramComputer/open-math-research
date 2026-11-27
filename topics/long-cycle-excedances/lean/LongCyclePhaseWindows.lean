import OpenMathResearch.FirstLevelHits
import OpenMathResearch.AlternatingSignRoots

namespace OpenMathResearch.LongCycleExcedances
open Set Polynomial FirstLevelHits

/-- A contiguous block of oscillations yields singleton witnesses in increasing
modulus order. The offset is the number of earlier witnesses. The old sample parity is
independent of the next-row sign convention. Analytic inputs
are the old sample signs and the next-row signs at old zeros within each phase
band. The phase need not be monotone. -/
theorem singleton_windows_of_phase {m offset : ℕ} {a b : ℝ} {P Q : ℝ[X]}
    {phase radius : ℝ → ℝ} (sampleParity : ℕ) (hab : a ≤ b)
    (hf : ContinuousOn phase (Icc a b)) (hr : ContinuousOn radius (Icc a b))
    (hrmono : StrictMonoOn radius (Icc a b)) (hb : radius b ≤ 1)
    (level : Fin (m + 1) → ℝ) (hlevel : StrictMono level)
    (hstart : phase a ≤ level 0) (hend : level (Fin.last m) ≤ phase b)
    (hsample : ∀ i x, x ∈ Icc a b → phase x = level i →
      0 < (-1 : ℝ) ^ (sampleParity + i.val) * P.eval (-radius x))
    (hnext : ∀ (i : Fin m) x, x ∈ Icc a b → phase x ∈ Ioo (level i.castSucc) (level i.succ) →
      P.IsRoot (-radius x) → 0 < (-1 : ℝ) ^ (offset + i.val + 1) * Q.eval (-radius x)) :
    ∃ x : Fin m → ℝ, StrictMono x ∧ StrictMono (radius ∘ x) ∧
      ∀ i, x i ∈ Ioo a b ∧ radius (x i) ∈ Ioo (radius a) 1 ∧
        phase (x i) ∈ Ioo (level i.castSucc) (level i.succ) ∧
        P.IsRoot (-radius (x i)) ∧
        0 < (-1 : ℝ) ^ (offset + i.val + 1) * Q.eval (-radius (x i)) := by
  classical
  have hlo (i : Fin (m + 1)) := hstart.trans (hlevel.monotone (Fin.zero_le i))
  have hhi (i : Fin (m + 1)) := (hlevel.monotone (Fin.le_last i)).trans hend
  choose hit hhit using fun i => exists_firstLevelHitOn hf hab (hlo i) (hhi i)
  have hhitmono : StrictMono hit := by
    intro i j hij
    have hj : phase (hit j) = level j := (hhit j).1.2
    have hsub : Icc a (hit j) ⊆ Icc a b := fun _ ht => ⟨ht.1, ht.2.trans (hhit j).1.1.2⟩
    obtain ⟨w, hw, hwv⟩ := intermediate_value_Icc (hhit j).1.1.1 (hf.mono hsub)
      ⟨(hlo i), hj.symm ▸ (hlevel hij).le⟩
    have hlt := lt_of_le_of_ne hw.2 (fun he => (hlevel hij).ne (hwv.symm.trans (he ▸ hj)))
    exact ((hhit i).2 ⟨hsub hw, hwv⟩).trans_lt hlt
  have hband (i : Fin m) := exists_lastLower_before_firstUpper hf (hlo i.castSucc)
    (hlevel (show i.castSucc < i.succ from Nat.lt_succ_self i.val)) (hhit i.succ)
  choose left hleft hlt hinside using hband
  have hleftMem (i : Fin m) : left i ∈ Icc a b :=
    ⟨(hleft i).1.1.1, (hlt i).le.trans (hhit i.succ).1.1.2⟩
  have hroot (i : Fin m) : ∃ x ∈ Ioo (left i) (hit i.succ), P.IsRoot (-radius x) := by
    let g (x : ℝ) := P.eval (-radius x)
    have hsub : Icc (left i) (hit i.succ) ⊆ Icc a b :=
      fun _ hx => ⟨(hleftMem i).1.trans hx.1, hx.2.trans (hhit i.succ).1.1.2⟩
    have hg : ContinuousOn g (Icc (left i) (hit i.succ)) :=
      P.continuous.comp_continuousOn (hr.mono hsub).neg
    have hprod : g (left i) * g (hit i.succ) < 0 :=
      AlternatingSignRoots.opposite_signs (hsample i.castSucc _ (hleftMem i) (hleft i).1.2)
        (by simpa [Nat.add_assoc] using hsample i.succ _ (hhit i.succ).1.1 (hhit i.succ).1.2)
    rcases mul_neg_iff.mp hprod with ⟨hl, hu⟩ | ⟨hl, hu⟩
    · obtain ⟨x, hx, hz⟩ := intermediate_value_Icc' (hlt i).le hg ⟨hu.le, hl.le⟩
      exact ⟨x, ⟨lt_of_le_of_ne hx.1 (by rintro rfl; exact hl.ne' hz),
        lt_of_le_of_ne hx.2 (by rintro rfl; exact hu.ne hz)⟩, hz⟩
    · obtain ⟨x, hx, hz⟩ := intermediate_value_Icc (hlt i).le hg ⟨hl.le, hu.le⟩
      exact ⟨x, ⟨lt_of_le_of_ne hx.1 (by rintro rfl; exact hl.ne hz),
        lt_of_le_of_ne hx.2 (by rintro rfl; exact hu.ne' hz)⟩, hz⟩
  choose x hx hz using hroot
  have hxmono : StrictMono x := by
    intro i j hij
    have hidx : i.succ ≤ j.castSucc := Fin.le_def.mpr (Nat.succ_le_of_lt hij)
    have hh := hhitmono.monotone hidx
    have hbefore : hit j.castSucc ≤ left j :=
      (hleft j).2 ⟨⟨(hhit j.castSucc).1.1.1,
        (hhitmono (show j.castSucc < j.succ from Nat.lt_succ_self j.val)).le⟩, (hhit j.castSucc).1.2⟩
    exact (hx i).2.trans ((hh.trans hbefore).trans_lt (hx j).1)
  have hxab (i : Fin m) : x i ∈ Ioo a b :=
    ⟨(hleftMem i).1.trans_lt (hx i).1, (hx i).2.trans_le (hhit i.succ).1.1.2⟩
  refine ⟨x, hxmono, ?_, ?_⟩
  · intro i j hij
    exact hrmono (Ioo_subset_Icc_self (hxab i)) (Ioo_subset_Icc_self (hxab j)) (hxmono hij)
  · intro i
    have hxi := hxab i
    have hx' : x i ∈ Icc a b := Ioo_subset_Icc_self hxi
    have hs := hinside i (x i) (hx i)
    exact ⟨hxi, ⟨hrmono ⟨le_rfl, hab⟩ hx' hxi.1,
      (hrmono hx' ⟨hab, le_rfl⟩ hxi.2).trans_le hb⟩, hs, hz i, hnext i _ hx' hs (hz i)⟩

#print axioms singleton_windows_of_phase
end OpenMathResearch.LongCycleExcedances
