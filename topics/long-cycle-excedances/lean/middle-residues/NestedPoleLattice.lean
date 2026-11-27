import NestedPoleRadii

noncomputable section
namespace OpenMathResearch.LongCycleExcedances

/-- Summing the inverse-square majorant gives both summability of the
piecewise pole approximants and an error bound for their lattice sum. -/
theorem nested_pole_lattice_error {ι : Type*} (poles : ι → ℂ) (T : ℕ → ℂ)
    {q : ℕ} (hq : 0 < q) {A r R₁ R₀ Rstar : ℝ}
    (hA : 0 ≤ A) (hr : 0 < r) (h₁ : r < R₁)
    (h₀ : R₁ < R₀) (hstar : R₀ < Rstar) (hw : ∀ l, r ≤ ‖poles l‖)
    (hT : ∀ j, ‖T j‖ ≤ A/Rstar^j)
    (hSquare : Summable fun l => (r/‖poles l‖)^2)
    (hPrefix : Summable fun l => normalizedPolePrefix T q r (poles l)) :
    (Summable fun l => normalizedPoleApprox T q r R₀ (poles l)) ∧
    ‖(∑' l, normalizedPolePrefix T q r (poles l)) -
      ∑' l, normalizedPoleApprox T q r R₀ (poles l)‖ ≤
      max ((R₀/Rstar)/(1-R₀/Rstar)) (1/(1-R₁/R₀)) *
        (A*(r/R₁)^(q-1)) * ∑' l, (r/‖poles l‖)^2 := by
  let C := max ((R₀/Rstar)/(1-R₀/Rstar)) (1/(1-R₁/R₀))
  let B := C*(A*(r/R₁)^(q-1))
  let f (l : ι) := normalizedPolePrefix T q r (poles l)
  let g (l : ι) := normalizedPoleApprox T q r R₀ (poles l)
  have hm (l : ι) : ‖f l - g l‖ ≤ B*(r/‖poles l‖)^2 := by
    have h := nested_pole_radii_error_uniform T hq hA hr h₁ h₀ hstar (hw l) hT
    simpa only [f,g,B,C,mul_assoc] using h
  have hMajor : Summable (fun l : ι => B*(r/‖poles l‖)^2) := hSquare.mul_left B
  have hErr := Summable.of_nonneg_of_le (fun l => norm_nonneg (f l-g l)) hm hMajor
  have hApprox : Summable g := by
    apply (hPrefix.sub hErr.of_norm).congr
    intro l
    change f l-(f l-g l) = g l
    abel
  refine ⟨hApprox,?_⟩
  change ‖(∑' l, f l)-(∑' l, g l)‖ ≤ B*∑' l, (r/‖poles l‖)^2
  rw [←hPrefix.tsum_sub hApprox]
  exact (norm_tsum_le_tsum_norm hErr).trans
    ((hErr.tsum_le_tsum hm hMajor).trans_eq tsum_mul_left)

/-- The two gaps of length r/(200k) give the same exact majorant constant. -/
theorem fixed_nested_radius_budget {r : ℝ} (hr : 0 < r) {k : ℕ} (hk : 0 < k) :
    let R₁ := r*(1+1/(100*(k:ℝ)))
    let R₀ := r*(1+3/(200*(k:ℝ)))
    let Rstar := r*(1+1/(50*(k:ℝ)))
    r < R₁ ∧ R₁ < R₀ ∧ R₀ < Rstar ∧
    max ((R₀/Rstar)/(1-R₀/Rstar)) (1/(1-R₁/R₀)) = (200*(k:ℝ)+3) := by
  dsimp only
  have hk' : 0 < (k:ℝ) := by exact_mod_cast hk
  let R₁ := r*(1+1/(100*(k:ℝ)))
  let R₀ := r*(1+3/(200*(k:ℝ)))
  let Rstar := r*(1+1/(50*(k:ℝ)))
  have hgap : 0 < r/(200*(k:ℝ)) := by positivity
  have h₁ : R₁-r = 2*(r/(200*(k:ℝ))) := by dsimp [R₁]; ring
  have h₀ : R₀-R₁ = r/(200*(k:ℝ)) := by dsimp [R₀,R₁]; ring
  have hstar : Rstar-R₀ = r/(200*(k:ℝ)) := by dsimp [Rstar,R₀]; ring
  have hr1 : r < R₁ := by linarith
  have hr0 : R₁ < R₀ := by linarith
  have hrs : R₀ < Rstar := by linarith
  have hR₀ : 0 < R₀ := (hr.trans hr1).trans hr0
  have hRs : 0 < Rstar := hR₀.trans hrs
  refine ⟨hr1,hr0,hrs,?_⟩
  change max ((R₀/Rstar)/(1-R₀/Rstar)) (1/(1-R₁/R₀)) = _
  have he₀ : 1-R₀/Rstar = (Rstar-R₀)/Rstar := by
    rw [sub_div,div_self hRs.ne']
  have he₁ : 1-R₁/R₀ = (R₀-R₁)/R₀ := by
    rw [sub_div,div_self hR₀.ne']
  have hR : R₀/(r/(200*(k:ℝ))) = 200*(k:ℝ)+3 := by
    dsimp [R₀]
    field_simp [hr.ne',hk'.ne'] <;> ring
  have hleft : (R₀/Rstar)/((r/(200*(k:ℝ)))/Rstar) = R₀/(r/(200*(k:ℝ))) := by
    field_simp [hRs.ne',hgap.ne'] <;> ring
  rw [he₀,he₁,hstar,h₀,hleft,one_div_div,hR,max_self]

#print axioms nested_pole_lattice_error
#print axioms fixed_nested_radius_budget
end OpenMathResearch.LongCycleExcedances
