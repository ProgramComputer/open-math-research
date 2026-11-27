import FourierOddPoleProduct
import FourierPoleContrast

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real MeasureTheory

/-- The pole-product estimate on the literal lattice of the common-circle proof.
Here r is the modulus of the two nearest poles, R is the integration radius. -/
theorem row_circle_pole_product (s r R : ℝ) (hr : 0 < r) (hR : 0 < R)
    (hr2 : r^2=s^2+π^2) {k : ℕ} (hk : 3 ≤ k)
    (hg : ∀ l : ℤ, ‖(⟨s,(2*(l:ℝ)+1)*π⟩:ℂ)‖ ≠ R) :
    let P := fun l : ℤ => (⟨s,(2*(l:ℝ)+1)*π⟩:ℂ)
    let c := fun l => (R:ℂ)^k/(P l)^(k-1)
    let a := fun l => poleWeight (c l) (P l) R
    (∫ x in (0:ℝ)..2*π, ‖(∑' l, c l/(P l-circleMap 0 R x))*
      (∑' l, (((r:ℂ)/P l-(s/r:ℝ))*c l)/(P l-circleMap 0 R x))‖) ≤
      2*π*(∑' l, a l)*((∑' l : ℤ, |2*(l:ℝ)+1| * a l)*(π/r)) := by
  let P := fun l : ℤ => (⟨s,(2*(l:ℝ)+1)*π⟩:ℂ)
  let C := s/r
  let S := π/r
  have hcs : C^2+S^2=1 := by
    dsimp only [C,S]
    rw [div_pow,div_pow,←add_div,←hr2,div_self (pow_ne_zero _ hr.ne')]
  have hS : 0 ≤ S := div_nonneg Real.pi_pos.le hr.le
  apply odd_lattice_pole_product P (fun l => (r:ℂ)/P l-(C:ℂ)) (fun _ => rfl) hR hg _ hk
  intro l
  let m := 2*(l:ℝ)+1
  let z : ℂ := ⟨C,m*S⟩
  have he : P l = (r:ℂ)*z := by
    apply Complex.ext
    · simp [P,z,Complex.mul_re,C,hr.ne']; field_simp
    · simp [P,z,Complex.mul_im,S,m]; field_simp
  have hratio : (r:ℂ)/P l = 1/z := by
    calc
      _ = ((r:ℂ)*1)/((r:ℂ)*z) := by rw [mul_one,←he]
      _ = _ := mul_div_mul_left _ _ (Complex.ofReal_ne_zero.mpr hr.ne')
  change ‖(r:ℂ)/P l-(C:ℂ)‖ ≤ |m| * S
  rw [hratio]
  exact normalized_lattice_contrast hcs hS (odd_lattice_height_one_le l)

#print axioms row_circle_pole_product
end OpenMathResearch.LongCycleExcedances
