import ColorTransformError

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open PowerSeries Finset
open scoped Polynomial PowerSeries

private theorem color_geom_step (n : ℕ) :
    (invOneSubPow ℝ (n+1)).val = (invOneSubPow ℝ n).val*(invOneSubPow ℝ 1).val := by
  rw [invOneSubPow_add]; rfl

private theorem color_geom_cancel : (1-X:ℝ⟦X⟧)*(invOneSubPow ℝ 1).val=1 := by
  have h := (invOneSubPow ℝ 1).inv_val
  rwa [invOneSubPow_inv_eq_one_sub_pow,pow_one] at h

theorem color_geom_derivative (n : ℕ) :
    derivative ℝ (invOneSubPow ℝ n).val=(n:ℝ⟦X⟧)*(invOneSubPow ℝ (n+1)).val := by
  let g : ℝ⟦X⟧ := (invOneSubPow ℝ 1).val
  have hg : (1-X)*g=1 := color_geom_cancel
  have dh := congrArg (derivative ℝ) hg
  have dz : derivative ℝ (1-X:ℝ⟦X⟧) = -1 := by simp
  rw [Derivation.leibniz,smul_eq_mul,smul_eq_mul,dz,Derivation.map_one_eq_zero] at dh
  have dg : derivative ℝ g=g*g := by
    linear_combination g*dh - derivative ℝ g*hg
  induction n with
  | zero => simp [invOneSubPow_zero, Derivation.map_one_eq_zero]
  | succ n ih =>
    rw [color_geom_step n,Derivation.leibniz,smul_eq_mul,smul_eq_mul,ih]
    rw [color_geom_step (n+1),color_geom_step n]
    change _*derivative ℝ g + _ = _
    rw [dg,Nat.cast_succ]
    ring

/-- Conjugating the Eulerian insertion operator by the color transform makes
it the Euler operator on power series, with multiplier p at color count p. -/
theorem color_transform_insertion (P : ℝ[X]) (n : ℕ) :
    colorTransform (n+1) (Polynomial.C (n:ℝ)*Polynomial.X*P+
      Polynomial.X*(1-Polynomial.X)*P.derivative) =
    X*derivative ℝ (colorTransform n P) := by
  simp only [colorTransform, Derivation.leibniz,smul_eq_mul,derivative_coe,
    Polynomial.coe_add,Polynomial.coe_mul,Polynomial.coe_C,Polynomial.coe_X,
    Polynomial.coe_sub,Polynomial.coe_one,color_geom_derivative]
  have hcast : C (R := ℝ) (n:ℝ)=(n:ℝ⟦X⟧) := map_natCast (C (R := ℝ)) n
  rw [hcast,color_geom_step]
  linear_combination X*((P.derivative:ℝ[X]):ℝ⟦X⟧)*(invOneSubPow ℝ n).val*color_geom_cancel

/-- The full transformed insertion recurrence; every hypothesis concerns the
ordinary Eulerian row or the literal polynomial insertion law. -/
theorem color_transform_successor (A : ℕ → ℝ[X]) (hOne : A 1=1)
    (hrec : ∀ m, A (m+1)=(1+Polynomial.C (m:ℝ)*Polynomial.X)*A m+
      Polynomial.X*(1-Polynomial.X)*(A m).derivative)
    (P Q R : ℝ[X]) (n k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n+1) (b : ℝ)
    (hQ : Q=Polynomial.C (n:ℝ)*Polynomial.X*P+
      Polynomial.X*(1-Polynomial.X)*P.derivative+
      Polynomial.C b*(Polynomial.X*A (k-1))*R) :
    colorTransform (n+1) Q = X*derivative ℝ (colorTransform n P)+
      C (R := ℝ) b*colorPowerSeries (k-1)*colorTransform (n+1-k) R := by
  have hsize : k+(n+1-k)=n+1 := by omega
  have hlag := colorTransform_mul k (n+1-k) (Polynomial.X*A (k-1)) R
  rw [hsize, colorTransform_cycle A hOne hrec hk] at hlag
  rw [←color_transform_insertion P n]
  unfold colorTransform at hlag ⊢
  rw [hQ]
  push_cast at *
  linear_combination C (R := ℝ) b*hlag

theorem coeff_color_euler_operator (p : ℕ) (F : ℝ⟦X⟧) :
    coeff (R := ℝ) p (X*derivative ℝ F)=(p:ℝ)*coeff (R := ℝ) p F := by
  cases p with
  | zero => simp [coeff_zero_eq_constantCoeff]
  | succ j => rw [coeff_succ_X_mul,coeff_derivative,Nat.cast_succ,mul_comm]

/-- The lag convolution is exactly the difference of consecutive normalized
counts after adjoining one label. -/
theorem color_successor_coefficient (F G H : ℝ⟦X⟧) (b : ℝ) (d p : ℕ)
    (hs : G=X*derivative ℝ F+C (R := ℝ) b*colorPowerSeries d*H) :
    coeff (R := ℝ) p G-(p:ℝ)*coeff (R := ℝ) p F =
      b*∑ j ∈ range (p+1), (j:ℝ)^d*coeff (R := ℝ) (p-j) H := by
  have hfun : mk (fun j => coeff (R := ℝ) j H)=H := by ext j; rw [coeff_mk]
  have h := color_convolution_coeff b d p (fun j => coeff (R := ℝ) j H)
  rw [hfun] at h
  rw [hs,map_add,coeff_color_euler_operator,h]; ring

/-- The positive binomial transform of the literal lag dominates its
untransformed coefficient at every color count. -/
theorem color_lag_comparison (P Q L : ℝ[X]) (n p : ℕ)
    (hQ : Q=Polynomial.C (n:ℝ)*Polynomial.X*P+
      Polynomial.X*(1-Polynomial.X)*P.derivative+L)
    (hL : ∀ j, 0≤L.coeff j) :
    0≤L.coeff p ∧ L.coeff p≤
      coeff (R := ℝ) p (colorTransform (n+1) Q)-(p:ℝ)*coeff (R := ℝ) p (colorTransform n P) := by
  have he : colorTransform (n+1) Q =
      X*derivative ℝ (colorTransform n P)+colorTransform (n+1) L := by
    rw [←color_transform_insertion P n,hQ]
    simp only [colorTransform,Polynomial.coe_add,add_mul]
  rw [he,map_add,coeff_color_euler_operator,add_sub_cancel_left]
  refine ⟨hL p,sub_nonneg.mp ?_⟩
  rw [color_extra_bars L (Nat.zero_lt_succ n)]
  exact sum_nonneg fun j _ => mul_nonneg (hL _) (by positivity)

theorem color_coeff_product_nonneg (P Q : ℝ[X])
    (hP : ∀ i, 0≤P.coeff i) (hQ : ∀ i, 0≤Q.coeff i) (j : ℕ) :
    0 ≤ (P*Q).coeff j := by
  rw [Polynomial.coeff_mul]
  exact sum_nonneg fun i _ => mul_nonneg (hP _) (hQ _)

theorem color_lag_coefficients_nonneg {ι : Type*} [Fintype ι]
    (d : ι → ℕ) (b : ℝ) (hb : 0≤b) (R : ℝ[X]) (hR : ∀ i, 0≤R.coeff i) (p : ℕ) :
    0≤(Polynomial.C b*(Polynomial.X*(∑ i : ι, Polynomial.X^(d i)))*R).coeff p := by
  apply color_coeff_product_nonneg _ _ _ hR
  apply color_coeff_product_nonneg
  · intro i; rw [Polynomial.coeff_C]; split_ifs <;> first | exact hb | rfl
  · apply color_coeff_product_nonneg
    · intro i; rw [Polynomial.coeff_X]; split_ifs <;> norm_num
    · intro j; rw [Polynomial.finsetSum_coeff]
      exact sum_nonneg fun i _ => by rw [Polynomial.coeff_X_pow]; split_ifs <;> norm_num

#print axioms color_lag_coefficients_nonneg
#print axioms color_lag_comparison
#print axioms color_transform_successor
#print axioms coeff_color_euler_operator
#print axioms color_successor_coefficient
#print axioms color_geom_derivative
#print axioms color_transform_insertion
end OpenMathResearch.LongCycleExcedances
