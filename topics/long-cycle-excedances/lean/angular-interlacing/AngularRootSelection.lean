import DeterminantCellSigns

set_option autoImplicit false
namespace OpenMathResearch.LongCycleExcedances
open Set Real

noncomputable def integerPhaseAngle (n j : ℕ) := (j:ℝ)*π/(n:ℝ)

theorem integerPhaseAngle_strictMono {n : ℕ} (hn : 0<n) : StrictMono (integerPhaseAngle n) := by
  intro i j h
  exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_right (by exact_mod_cast h) pi_pos) (by exact_mod_cast hn)

theorem integerPhaseAngle_level {n : ℕ} (hn : 0<n) (j : ℕ) :
    (n:ℝ)*integerPhaseAngle n j=(j:ℝ)*π := by
  unfold integerPhaseAngle
  have hp : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  field_simp

/-- Select one signed zero in each complete integer phase interval.  The open
intervals give strict ordering, including when the last endpoint is π/2. -/
theorem ordered_angular_cell_moduli (n H : ℕ) (hn : 0<n)
    {P Q μ : ℝ→ℝ} {sep : ℝ} (hμ : StrictMonoOn μ (Ioc 0 (π/2)))
    (hcenter : μ (π/2)=1)
    (hsep : sep ≤ μ (integerPhaseAngle n (H+1)))
    (hstart : 0 < integerPhaseAngle n (H+1))
    (cell : ∀ j : ℕ, H+1≤j → j+1≤n/2 →
      ∃ θ ∈ Ioo (integerPhaseAngle n j) (integerPhaseAngle n (j+1)),
        P (-μ θ)=0 ∧ 0<(-1:ℝ)^(j+1)*Q (-μ θ)) :
    ∃ u : Fin (n/2-(H+1)) → ℝ, StrictMono u ∧
      ∀ i, sep<u i ∧ u i<1 ∧ P (-u i)=0 ∧ 0<(-1:ℝ)^(H+1+i.val+1)*Q (-u i) := by
  let j (i : Fin (n/2-(H+1))) := H+1+i.val
  have grid := integerPhaseAngle_strictMono hn
  have tail (i : Fin (n/2-(H+1))) : j i+1 ≤ n/2 := by dsimp only [j]; have := i.isLt; omega
  have start (i : Fin (n/2-(H+1))) : H+1 ≤ j i := Nat.le_add_right _ _
  choose θ hθ hz hs using fun i => cell (j i) (start i) (tail i)
  have stop (i : Fin (n/2-(H+1))) : integerPhaseAngle n (j i+1) ≤ π/2 := by
    have hm : (2:ℝ)*((j i+1:ℕ):ℝ) ≤ n := by exact_mod_cast (show 2*(j i+1)≤n by have := tail i; omega)
    have hp : 0<(n:ℝ) := by exact_mod_cast hn
    unfold integerPhaseAngle
    apply (div_le_iff₀ hp).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hm pi_pos.le]
  have lower (i) := (grid.monotone (start i)).trans_lt (hθ i).1
  have upper (i) := (hθ i).2.trans_le (stop i)
  have inside (i) : θ i ∈ Ioc 0 (π/2) := ⟨hstart.trans (lower i), (upper i).le⟩
  refine ⟨fun i => μ (θ i), ?_, ?_⟩
  · intro i l hil
    apply hμ (inside i) (inside l)
    have hi : j i+1 ≤ j l := by dsimp only [j]; have := Fin.lt_iff_val_lt_val.mp hil; omega
    exact (hθ i).2.trans ((grid.monotone hi).trans_lt (hθ l).1)
  · intro i
    have hleft := hμ (show integerPhaseAngle n (H+1) ∈ Ioc 0 (π/2) from
      ⟨hstart, ((lower i).trans (upper i)).le⟩) (inside i) (lower i)
    have hright := hμ (inside i) (show π/2 ∈ Ioc 0 (π/2) from ⟨by positivity,le_rfl⟩) (upper i)
    exact ⟨hsep.trans_lt hleft, hcenter ▸ hright,hz i,hs i⟩

#print axioms integerPhaseAngle_strictMono
#print axioms integerPhaseAngle_level
#print axioms ordered_angular_cell_moduli
end OpenMathResearch.LongCycleExcedances
