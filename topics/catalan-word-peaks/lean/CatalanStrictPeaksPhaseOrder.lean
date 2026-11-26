import CatalanStrictPeaksPhaseBridge
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# Ordering the Catalan phase

The explicit correction has derivative at most five, so the actual
phase is strictly increasing at the analytic row lengths.
-/

namespace CatalanStrictPeaks.CutGeometry

open Real Set OpenMathResearch.OrientedNegativeInterlace

private theorem phaseCorrection_hasDerivAt_le {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) (π / 2)) :
    ∃ v : ℝ, v ≤ 5 ∧ HasDerivAt phaseCorrection v θ := by
  let c := cos θ
  let s := sin θ
  let A := 1 + 2 * c
  let B := 1 + c - c ^ 2
  let f := s / A
  let g := c * s / B
  let f' := (c + 2) / A ^ 2
  let g' := ((c ^ 2 - s ^ 2) * B + (c * s) * (s * (1 - 2 * c))) / B ^ 2
  have hc : 0 ≤ c := cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, pi_pos], hθ.2⟩
  have hc1 : c ≤ 1 := cos_le_one θ
  have hs : 0 ≤ s := sin_nonneg_of_mem_Icc ⟨hθ.1, hθ.2.trans (by linarith [pi_pos])⟩
  have hs1 : s ≤ 1 := sin_le_one θ
  have htrig : s ^ 2 + c ^ 2 = 1 := sin_sq_add_cos_sq θ
  have hA : 1 ≤ A := by dsimp [A]; linarith
  have hB : 1 ≤ B := by
    dsimp only [B]
    nlinarith [mul_nonneg hc (sub_nonneg.mpr hc1)]
  have hApos : 0 < A := zero_lt_one.trans_le hA
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  have hf : HasDerivAt (fun x => sin x / (1 + 2 * cos x)) f' θ := by
    convert (hasDerivAt_sin θ).div
      (((hasDerivAt_cos θ).const_mul 2).const_add 1) hApos.ne' using 1
    change (c + 2) / A ^ 2 = (c * A - s * (2 * -s)) / A ^ 2
    congr 1
    dsimp only [A]
    linear_combination -2 * htrig
  have hg : HasDerivAt (fun x => cos x * sin x / (1 + cos x - cos x ^ 2)) g' θ := by
    convert ((hasDerivAt_cos θ).mul (hasDerivAt_sin θ)).div
      (((hasDerivAt_cos θ).const_add 1).sub ((hasDerivAt_cos θ).pow 2)) hBpos.ne' using 1
    change ((c ^ 2 - s ^ 2) * B + (c * s) * (s * (1 - 2 * c))) / B ^ 2 =
      ((-s * s + c * c) * B - c * s * (-s - 2 * c ^ (2 - 1) * -s)) / B ^ 2
    norm_num
    ring
  have hf' : f' ≤ 3 := by
    apply (div_le_iff₀ (pow_pos hApos 2)).2
    have hA2 : 1 ≤ A ^ 2 := by simpa only [one_pow] using pow_le_pow_left₀ zero_le_one hA 2
    linarith
  have hg' : g' ≤ 3 / 2 := by
    apply (div_le_iff₀ (pow_pos hBpos 2)).2
    have h₁ : (c ^ 2 - s ^ 2) * B ≤ 1 * B :=
      mul_le_mul_of_nonneg_right (by linarith [sq_nonneg s]) hBpos.le
    have hslope : s * (1 - 2 * c) ≤ 1 := by
      have h := mul_le_mul_of_nonneg_left (show 1 - 2 * c ≤ 1 by linarith) hs
      rw [mul_one] at h
      exact h.trans hs1
    have hprod : c * s ≤ 1 / 2 := by nlinarith [sq_nonneg (s - c)]
    have h₂ : (c * s) * (s * (1 - 2 * c)) ≤ 1 / 2 := by
      have h := mul_le_mul_of_nonneg_left hslope (mul_nonneg hc hs)
      rw [mul_one] at h
      exact h.trans hprod
    have hB2 : 1 ≤ B ^ 2 := by simpa only [one_pow] using pow_le_pow_left₀ zero_le_one hB 2
    have hB3 : B ≤ B ^ 2 := by
      rw [pow_two]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hB hBpos.le
    calc
      _ ≤ 1 * B + 1 / 2 := add_le_add h₁ h₂
      _ ≤ B ^ 2 + (1 / 2 : ℝ) * B ^ 2 := by
        simpa only [one_mul, mul_one] using
          add_le_add hB3 (mul_le_mul_of_nonneg_left hB2 (by norm_num : 0 ≤ (1 / 2 : ℝ)))
      _ = _ := by ring
  have hAatan : (1 / (1 + f ^ 2)) * f' ≤ 3 := by
    have hu : 1 / (1 + f ^ 2) ≤ 1 := (div_le_one (by positivity)).2 (le_add_of_nonneg_right (sq_nonneg _))
    exact (mul_le_mul_of_nonneg_left hf' (by positivity)).trans (by linarith)
  have hBatan : (1 / (1 + g ^ 2)) * g' ≤ 3 / 2 := by
    have hu : 1 / (1 + g ^ 2) ≤ 1 := (div_le_one (by positivity)).2 (le_add_of_nonneg_right (sq_nonneg _))
    exact (mul_le_mul_of_nonneg_left hg' (by positivity)).trans (by linarith)
  refine ⟨1 / 2 + (1 / 2) * ((1 / (1 + f ^ 2)) * f') +
    2 * ((1 / (1 + g ^ 2)) * g'), by linarith, ?_⟩
  unfold phaseCorrection
  simpa only [div_eq_mul_inv, one_mul, id_eq, f, g, A, B, c, s] using
    ((((hasDerivAt_id θ).div_const 2).sub_const (π / 4)).add
      (hf.arctan.const_mul ((2 : ℝ)⁻¹))).add (hg.arctan.const_mul 2)

/-- The phase strictly increases across the checkpoint interval for every
row at or above the analytic threshold. -/
theorem checkpointPhase_strictMonoOn {n : ℕ} (hn : 150 ≤ n) :
    StrictMonoOn (checkpointPhase n) (Icc (0 : ℝ) (π / 2)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (continuousOn_checkpointPhase n)
  intro θ hθ
  rw [interior_Icc] at hθ
  obtain ⟨v, hv, hderiv⟩ := phaseCorrection_hasDerivAt_le ⟨hθ.1.le, hθ.2.le⟩
  have h : HasDerivAt (checkpointPhase n) ((n : ℝ) - v) θ := by
    simpa only [checkpointPhase, mul_one] using
      ((hasDerivAt_id θ).const_mul (n : ℝ)).sub hderiv
  rw [h.deriv]
  have hnR : (150 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  linarith

private theorem continuousOn_modulus : ContinuousOn modulus (Ioo (0 : ℝ) (π / 2)) := by
  have hcos : ContinuousOn cos (Ioo (0 : ℝ) (π / 2)) := continuous_cos.continuousOn
  have hA : ContinuousOn (fun x => 1 + 2 * cos x) (Ioo (0 : ℝ) (π / 2)) :=
    continuousOn_const.add (continuousOn_const.mul hcos)
  have hroot := continuous_sqrt.comp_continuousOn hA
  have har : ContinuousOn (fun x => radius (cos x)) (Ioo (0 : ℝ) (π / 2)) := by
    unfold radius
    apply hroot.inv₀
    intro x hx
    have hp : 0 < 1 + 2 * cos x := by linarith [(cosine_in_unit hx).1]
    exact (sqrt_pos.2 hp).ne'
  have hScale : ContinuousOn (fun x => scale (cos x)) (Ioo (0 : ℝ) (π / 2)) := by
    unfold scale
    exact (((continuousOn_const.mul (hcos.pow 2)).mul
      (continuousOn_const.add hcos)).mul (har.pow 3))
  unfold modulus
  exact ((hScale.pow 2).inv₀ (fun x hx => (pow_pos (scale_pos (cosine_in_unit hx).1) 2).ne')).sub
    continuousOn_const

/-- The complete old root list can be normalized by the angular parameter
at every middle rank. Its phase lies strictly between the two consecutive
checkpoint levels. The rank index in this statement is zero-based. -/
theorem middle_roots_between_checkpoints {n : ℕ} (hn : 150 ≤ n) :
    ∃ roots : Fin (rowDegree n) → ℝ, CompleteNegativeRoots (C n) roots ∧
      ∀ i, 0 < i.val → i.val + 1 < rowDegree n →
        ∃ θ ∈ Ioo (0 : ℝ) (π / 2), roots i = modulus θ ∧
          (i.val : ℝ) * π < checkpointPhase n θ ∧
          checkpointPhase n θ < ((i.val : ℝ) + 1) * π := by
  let H := catalanCheckpoints n hn
  let m := rowDegree n - 1
  have hd : rowDegree n = m + 1 := by dsimp [m, rowDegree]; omega
  have hmNat : 2 * m + 3 ≤ n := by dsimp [m, rowDegree]; omega
  have hmReal : 2 * (m : ℝ) + 3 ≤ (n : ℝ) := by exact_mod_cast hmNat
  have hL : H.phase H.left < 1 := by rw [H.leftPhase]; norm_num
  have hR : (m : ℝ) < H.phase H.right := by rw [H.rightPhase]; linarith
  obtain ⟨t, ht, hmem, heval⟩ :=
    OpenMathResearch.IntegerLevelNodes.increasing_integer_level_nodes
      H.interval H.continuous hL m hR
  let q (j : Fin m) := modulus (t j)
  have hq : StrictMono q := fun _ _ h => H.modulusOrder (hmem _) (hmem _) (ht h)
  have hqp (j : Fin m) : 0 < q j := H.modulusPos _ (hmem j)
  have hsign (j : Fin m) : 0 < (-1 : ℝ) ^ (j.val + 1) * (C n).eval (-q j) :=
    H.signs (j.val + 1) (Nat.succ_pos _) (by have hj := j.isLt; omega)
      (t j) (hmem j) (heval j)
  obtain ⟨roots, hroots, horient⟩ :=
    roots_of_signed_test_points (C n) q (natDegree_C n) (Or.inr hd) hq hqp
      (eval_zero_pos n) (leadingCoeff_pos n) hsign
  refine ⟨roots, hroots, ?_⟩
  intro i hi hlast
  let prev : Fin m := ⟨i.val - 1, by omega⟩
  let curr : Fin m := ⟨i.val, by omega⟩
  have hlo : q prev < roots i := horient.2 prev i (by dsimp only [prev]; omega)
  have hhi : roots i < q curr := horient.1 curr i rfl
  have htorder : t prev < t curr := ht (show prev.val < curr.val by dsimp only [prev, curr]; omega)
  have hprev : t prev ∈ Ioo (0 : ℝ) (π / 2) := hmem prev
  have hcurr : t curr ∈ Ioo (0 : ℝ) (π / 2) := hmem curr
  have hcont := continuousOn_modulus.mono (show Icc (t prev) (t curr) ⊆ Ioo 0 (π / 2) from
    fun _ hx => ⟨hprev.1.trans_le hx.1, hx.2.trans_lt hcurr.2⟩)
  obtain ⟨θ, hθ, hvalue⟩ := intermediate_value_Icc htorder.le hcont
    (show roots i ∈ Icc (modulus (t prev)) (modulus (t curr)) from ⟨hlo.le, hhi.le⟩)
  have hθ' : θ ∈ Ioo (t prev) (t curr) :=
    ⟨lt_of_le_of_ne hθ.1 (by rintro rfl; exact hlo.ne hvalue),
     lt_of_le_of_ne hθ.2 (by rintro rfl; exact hhi.ne' hvalue)⟩
  have hθI : θ ∈ Ioo (0 : ℝ) (π / 2) := ⟨hprev.1.trans hθ'.1, hθ'.2.trans hcurr.2⟩
  have hprev' : checkpointPhase n (t prev) = (i.val : ℝ) * π := by
    have he := (div_eq_iff pi_ne_zero).mp (heval prev)
    have hid : prev.val + 1 = i.val := by dsimp only [prev]; omega
    simpa only [hid] using he
  have hcurr' : checkpointPhase n (t curr) = ((i.val : ℝ) + 1) * π := by
    have he := (div_eq_iff pi_ne_zero).mp (heval curr)
    simpa only [curr, Nat.cast_add, Nat.cast_one] using he
  have hPhase := checkpointPhase_strictMonoOn hn
  refine ⟨θ, hθI, hvalue.symm, ?_, ?_⟩
  · rw [← hprev']
    exact hPhase ⟨hprev.1.le, hprev.2.le⟩ ⟨hθI.1.le, hθI.2.le⟩ hθ'.1
  · rw [← hcurr']
    exact hPhase ⟨hθI.1.le, hθI.2.le⟩ ⟨hcurr.1.le, hcurr.2.le⟩ hθ'.2

/-- The imaginary part of the actual phase factor has the sign for the
zero-based middle rank between the two levels. -/
theorem nearPhaseUnit_im_sign_between {θ : ℝ} {n j : ℕ}
    (hθ : θ ∈ Ioo (0 : ℝ) (π / 2))
    (hlo : (j : ℝ) * π < checkpointPhase n θ)
    (hhi : checkpointPhase n θ < ((j : ℝ) + 1) * π) :
    0 < (-1 : ℝ) ^ (j + 1) * (nearPhaseUnit (cos θ) n).im := by
  let δ := checkpointPhase n θ - (j : ℝ) * π
  have hδ : 0 < δ := sub_pos.mpr hlo
  have hδ' : δ < π := by dsimp [δ]; linarith
  have happ : checkpointPhase n θ = δ + (j : ℝ) * π := by dsimp [δ]; ring
  have h : sin (checkpointPhase n θ) = (-1 : ℝ) ^ j * sin δ := by
    rw [happ, sin_add_nat_mul_pi]
  have hsign : (-1 : ℝ) ^ j * (-1 : ℝ) ^ j = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  rw [nearPhaseUnit_eq_exp hθ, ← Complex.ofReal_neg, Complex.exp_ofReal_mul_I_im,
    sin_neg, h, pow_succ]
  calc
    (0 : ℝ) < sin δ := sin_pos_of_pos_of_lt_pi hδ hδ'
    _ = ((-1 : ℝ) ^ j * (-1 : ℝ) ^ j) * sin δ := by rw [hsign, one_mul]
    _ = _ := by ring

end CatalanStrictPeaks.CutGeometry
