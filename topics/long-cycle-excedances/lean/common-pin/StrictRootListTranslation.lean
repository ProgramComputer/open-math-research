import LongCycleMixedRootWitnesses
import Mathlib.Data.Fin.Rev

namespace OpenMathResearch.LongCycleExcedances
open Polynomial OrientedNegativeInterlace Finset

/-- The complete positive moduli in increasing order become the complete
negative roots in increasing order by negating and reversing the indices. -/
theorem complete_moduli_factorization {d : ℕ} {P : ℝ[X]} {r : Fin d → ℝ}
    (hr : CompleteNegativeRoots P r) :
    P = C P.leadingCoeff * ∏ i : Fin d, (X - C (-r i.rev)) := by
  classical
  obtain ⟨hd, hmono, _, hroots⟩ := hr
  have hinj : Function.Injective (fun i => -r i) := neg_injective.comp hmono.injective
  have hcard : Multiset.card P.roots = P.natDegree := by
    rw [hd, hroots]
    change (Finset.univ.image (fun i => -r i)).card = d
    rw [Finset.card_image_of_injective _ hinj, card_univ, Fintype.card_fin]
  have hp := (C_leadingCoeff_mul_prod_multiset_X_sub_C hcard).symm
  rw [hroots] at hp
  change P = C P.leadingCoeff *
    (∏ x ∈ (Finset.univ.image (fun i => -r i)), (X - C x)) at hp
  rw [Finset.prod_image (fun x _ y _ hxy => hinj hxy)] at hp
  refine hp.trans ?_
  congr 1
  exact (Fin.rev_bijective.prod_comp (fun i : Fin d => X - C (-r i))).symm

theorem negative_reversed_mono {d : ℕ} {r : Fin d → ℝ} (hr : StrictMono r) :
    StrictMono (fun i : Fin d => -r i.rev) :=
  fun {_i _j} hij => neg_lt_neg (hr (Fin.rev_lt_rev.mpr hij))

theorem negative_reversed_interlaces {d : ℕ} {r : Fin d → ℝ} {s : Fin (d + 1) → ℝ}
    (h : ∀ i, s i.castSucc < r i ∧ r i < s i.succ) :
    ∀ i : Fin d, -s i.castSucc.rev < -r i.rev ∧ -r i.rev < -s i.succ.rev := by
  intro i
  rw [Fin.rev_castSucc, Fin.rev_succ]
  exact ⟨neg_lt_neg (h i.rev).2, neg_lt_neg (h i.rev).1⟩

#print axioms complete_moduli_factorization
#print axioms negative_reversed_mono
#print axioms negative_reversed_interlaces

end OpenMathResearch.LongCycleExcedances
