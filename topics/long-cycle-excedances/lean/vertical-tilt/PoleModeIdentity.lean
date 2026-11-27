import VerticalMeshSum

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset

def logPolyAt (m : ℕ) (g : ℕ → ℂ) (z : ℂ) := ∑ j ∈ range m, g (j+1)*z^(j+1)

private theorem exp_at_scaled (a : ℕ) (z t : ℂ) (hz : Complex.exp (-z) = t) :
    Complex.exp (-((a:ℂ)*z))=t^a := by
  rw [←hz,←Complex.exp_nat_mul]
  congr 1
  ring

private theorem trun_diff_mode (m a : ℕ) (ha : 0 < a) (z y t : ℂ)
    (hz : Complex.exp (-z)=t) (hy : Complex.exp (-y)=t) :
    cutoffExp m ((a:ℂ)*z)/(a:ℂ) - cutoffExp m ((a:ℂ)*y)/(a:ℂ) =
      ∑ j ∈ range m, t^a*(a:ℂ)^j*((z^(j+1)-y^(j+1))/((j+1).factorial:ℂ)) := by
  unfold cutoffExp
  rw [exp_at_scaled a z t hz,exp_at_scaled a y t hy]
  simp only [sum_range_succ' _ m,pow_zero,Nat.factorial_zero,Nat.cast_one,div_one]
  let A := ∑ j ∈ range m, ((a:ℂ)*z)^(j+1)/((j+1).factorial:ℂ)
  let B := ∑ j ∈ range m, ((a:ℂ)*y)^(j+1)/((j+1).factorial:ℂ)
  change t^a*(A+1)/(a:ℂ)-t^a*(B+1)/(a:ℂ) = _
  rw [show t^a*(A+1)/(a:ℂ)-t^a*(B+1)/(a:ℂ) = (t^a/(a:ℂ))*(A-B) by ring]
  dsimp only [A,B]
  rw [←sum_sub_distrib,mul_sum]
  apply sum_congr rfl
  intro j _
  rw [mul_pow,mul_pow,pow_succ (a:ℂ) j]
  have hn : (a:ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  field_simp [hn] <;> ring

/-- At two points with the same negative exponential, the change of the
literal polynomial is the negative sum of the vertical-mode differences. -/
theorem log_difference_from_modes (m : ℕ) (g : ℕ → ℂ) (x l u : ℝ) (t : ℂ)
    (hu : Complex.exp (-verticalArgument x u)=t) (hl : Complex.exp (-verticalArgument x l)=t)
    (coeff : ∀ j ∈ range m, HasSum (fun i : ℕ => t^(i+1)*((i+1:ℕ):ℂ)^j)
      (-g (j+1)*((j+1).factorial:ℂ))) :
    logPolyAt m g (verticalArgument x u) - logPolyAt m g (verticalArgument x l) =
      -(∑' i : ℕ, (verticalMode m (i+1) x u - verticalMode m (i+1) x l)) := by
  let z := verticalArgument x u
  let y := verticalArgument x l
  let D (j : ℕ) := z^(j+1)-y^(j+1)
  let F (j i : ℕ) := t^(i+1)*((i+1:ℕ):ℂ)^j*(D j/((j+1).factorial:ℂ))
  have hs (j : ℕ) (hj : j ∈ range m) : HasSum (F j) (-g (j+1)*D j) := by
    have h := (coeff j hj).mul_right (D j/((j+1).factorial:ℂ))
    have hfac : ((j+1).factorial:ℂ) ≠ 0 := by exact_mod_cast (j+1).factorial_ne_zero
    rw [show -g (j+1)*((j+1).factorial:ℂ)*(D j/((j+1).factorial:ℂ)) =
      -g (j+1)*D j by field_simp [hfac] <;> ring] at h
    exact h
  have h := (hasSum_sum hs).tsum_eq
  have eq (i : ℕ) : verticalMode m (i+1) x u - verticalMode m (i+1) x l =
      ∑ j ∈ range m, F j i := trun_diff_mode m (i+1) (Nat.succ_pos _) z y t hu hl
  simp only [eq]
  rw [h]
  have hen : (∑ j ∈ range m, -g (j+1)*D j) =
      -(logPolyAt m g z-logPolyAt m g y) := by
    unfold logPolyAt
    rw [←sum_sub_distrib,←sum_neg_distrib]
    apply sum_congr rfl
    intro j _
    dsimp only [D]
    ring
  rw [hen,neg_neg]

#print axioms log_difference_from_modes
end OpenMathResearch.LongCycleExcedances
