import FourierNumericCoefficients

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real

/-- Direct interface to the output of the twice-integrated Fourier theorem.
The four raw kernel masses occur in the same order in the two row bounds. -/
theorem normalized_fourier_pair_of_kernel_masses {n k : ℤ} (hk : (100:ℝ) ≤ k) {x : ℝ}
    (hx : 48 ≤ x) (hn : (n:ℝ)=x*(k:ℝ)) (F : ℤ → ℂ) (a A C : ℂ)
    {S M r R T decay B s₀ s₁ t₀ t₁ : ℝ} (hS : 0 < S) (hr : 0 ≤ r) (hT : 0 < T)
    (hR : 0 ≤ R) (hu : 1 ≤ x*((k:ℝ)*S^2))
    (hdec : decay ≤ Real.exp (-(19/20)*x))
    (hamp : r*M/T ≤ (k:ℝ)*Real.exp (2997/100)*B)
    (hB₁ : x ≤ 100 → B ≤ 457) (hB₂ : 100 ≤ x → B ≤ (46/100)*x*Real.sqrt x)
    (h₀ : 0 ≤ s₀) (h₁ : 0 ≤ s₁) (ht₀ : 0 ≤ t₀) (ht₁ : 0 ≤ t₁)
    (hb₀ : s₀/Real.sqrt k ≤ 9*x) (hb₁ : s₁/Real.sqrt k ≤ 12*x*Real.sqrt x)
    (hv₀ : R*t₀/k ≤ 10*x*Real.sqrt x) (hv₁ : R*t₁/k ≤ 13*x^2)
    (hA : ‖A‖ ≤ 9*Real.sqrt x) (ha : ‖a‖ ≤ 1)
    (hbase : ∀ j : ℤ, ‖((j-k:ℤ):ℂ)*(j:ℂ)*F j‖ ≤ M*(s₀^2+R*t₀))
    (hadj : ‖((n-k:ℤ):ℂ)*(n:ℂ)*(a*F (n+1)-C*F n)‖ ≤
      M*(S*s₀*s₁+R*S*t₁)+‖((n-k:ℤ):ℂ)*A*F (n+1-k)‖+‖((n-k:ℤ):ℂ)*a*F (n+1)‖) :
    (r/(2*T))*decay*‖F n‖ < 1/25 ∧
      (r/(2*T))*decay*‖a*F (n+1)-C*F n‖ < S/25 := by
  have hk' : (0:ℝ) < k := by linarith
  have hkz : (0:ℤ) < k := by exact_mod_cast hk'
  have hsqrt := Real.sqrt_pos.mpr hk'
  have hsq := Real.sq_sqrt hk'.le
  let O := (s₀/Real.sqrt k)^2 + R*t₀/k
  let J := (s₀/Real.sqrt k)*(s₁/Real.sqrt k) + R*t₁/k
  have hOld : (k:ℝ)*O = s₀^2+R*t₀ := by
    dsimp only [O]; rw [div_pow,hsq,mul_add,mul_div_cancel₀ _ hk'.ne',mul_div_cancel₀ _ hk'.ne']
  have hNew : (k:ℝ)*J = s₀*s₁+R*t₁ := by
    dsimp only [J]; rw [div_mul_div_comm,←sq,hsq,mul_add,mul_div_cancel₀ _ hk'.ne',mul_div_cancel₀ _ hk'.ne']
  have hb := scaled_fourier_kernel_bounds hx (div_nonneg h₀ hsqrt.le) (div_nonneg h₁ hsqrt.le) hb₀ hb₁ hv₀ hv₁
  have hcorr := correction_bounds_from_entrance hk hx hn hS hu hA ha
  apply numerical_fourier_coefficient_pair hkz hx hn F a A C hS hr hT
    (O:=O) (J:=J) (by dsimp [O]; positivity) (by dsimp [J]; positivity) hdec hamp hB₁ hB₂
    hb.1 hb.2.2 hcorr.1 hcorr.2
  · intro j
    simpa only [mul_assoc M (k:ℝ) O,hOld] using hbase j
  · have h : M*S*(k:ℝ)*J = M*(S*s₀*s₁+R*S*t₁) := by
      rw [mul_assoc (M*S),hNew]; ring
    simpa only [h] using hadj

#print axioms normalized_fourier_pair_of_kernel_masses
end OpenMathResearch.LongCycleExcedances
