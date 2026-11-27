import PrimitiveFirstBlock

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset

def checkerDegreeFloor (i : ℕ) : ℝ := if i=4 then 1 else ((i-1:ℕ):ℝ)/4

def checkerDegreeMass (K i : ℕ) : ℝ :=
  if i < 4 then 0 else if i=4 then 1 else if i ≤ 8 then
    1/(checkerDegreeFloor i-1/(K:ℝ))-4/(i:ℝ)+(if i=8 then 1/(4*(K:ℝ)) else 0)
  else (1/4+1/(K:ℝ))/(2*(((i-1)/4).factorial:ℝ))

theorem checker_degree_floor_le {k N i s : ℕ} (hk : 0 < k) (hi : 4 ≤ i)
    (hs : s ∈ primitiveDegrees k N i) : checkerDegreeFloor i ≤ (s:ℝ)/k := by
  have hkR : (0:ℝ)<k := by exact_mod_cast hk
  by_cases h : i=4
  · rw [checkerDegreeFloor,if_pos h]
    exact (one_le_div hkR).mpr (by exact_mod_cast (mem_Icc.mp (mem_filter.mp hs).1).1)
  · rw [checkerDegreeFloor,if_neg h]
    have h4 := ((degreeBin_iff hk (by omega : 0 < i)).mp (mem_filter.mp hs).2).1
    have h4R : ((i-1:ℕ):ℝ)*k ≤ 4*(s:ℝ) := by exact_mod_cast h4.le
    apply (le_div_iff₀ hkR).mpr
    linarith only [h4R]

theorem primitive_first_checker_bin_mass {K k N i : ℕ} (hK : 2 ≤ K) (hKk : K ≤ k)
    (hi5 : 5 ≤ i) (hi8 : i ≤ 8) (b : ℕ → ℝ)
    (hb : ∀ s : ℕ, k < s → s < 2*k → b s = -1/((s:ℝ)*((s:ℝ)-1)))
    (hj : |b (2*k)| ≤ 1/(4*(k:ℝ)^2)) :
    (k:ℝ)*(∑ s ∈ primitiveDegrees k N i, |b s|) ≤ checkerDegreeMass K i := by
  let l := ((i-1)*k)/4
  let u := min (i*k/4) (2*k-1)
  let T := primitiveDegrees k N i
  have hk : 0 < k := by omega
  have hkR : (0:ℝ)<k := by exact_mod_cast hk
  have hKR : (0:ℝ)<K := by exact_mod_cast (show 0 < K by omega)
  have hKkR : (K:ℝ) ≤ k := by exact_mod_cast hKk
  have hkl : k≤l := (Nat.le_div_iff_mul_le (by decide : 0 < 4)).mpr (by
    have h := Nat.mul_le_mul_right k (by omega : 4 ≤ i-1)
    simpa [mul_comm] using h)
  have hlt : l < 2*k := (Nat.div_lt_iff_lt_mul (by decide : 0 < 4)).mpr (by
    have h := Nat.mul_le_mul_right k (by omega : i-1 ≤ 7)
    omega)
  have hli : (i-1)*k ≤ i*k := Nat.mul_le_mul_right _ (Nat.sub_le ..)
  have hlu : l ≤ u := le_min (Nat.div_le_div_right hli) (by omega)
  have hu : u<2*k := (min_le_right _ _).trans_lt (by omega)
  have hT : T.erase (2*k) ⊆ Ioc l u := by
    intro s hs
    obtain ⟨hne,hs'⟩ := mem_erase.mp hs
    have he := (degreeBin_iff hk (by omega : 0 < i)).mp (mem_filter.mp hs').2
    have hupper : s ≤ i*k/4 := (Nat.le_div_iff_mul_le (by decide : 0 < 4)).2 (by
      simpa [mul_comm] using he.2)
    have hhigh := Nat.mul_le_mul_right k hi8
    exact mem_Ioc.mpr ⟨(Nat.div_lt_iff_lt_mul (by decide : 0 < 4)).2 (by simpa [mul_comm] using he.1),
      le_min hupper (by omega)⟩
  have hbase := primitive_first_block_subset_mass hk hkl hlu hu _ hT b hb
  have hprime : (k:ℝ)*(∑ s ∈ T, |b s|) ≤
      (k:ℝ)/(l:ℝ)-(k:ℝ)/(u:ℝ)+(if i=8 then 1/(4*(K:ℝ)) else 0) := by
    by_cases hmem : 2*k ∈ T
    · have hh := (degreeBin_iff hk (by omega : 0 < i)).mp (mem_filter.mp hmem).2
      have hI : i=8 := by
        by_contra hn
        have := Nat.mul_le_mul_right k (by omega : i ≤ 7)
        omega
      rw [←sum_erase_add T (fun s => |b s|) hmem,mul_add,if_pos hI]
      apply add_le_add hbase
      calc
        _ ≤ (k:ℝ)*(1/(4*(k:ℝ)^2)) := mul_le_mul_of_nonneg_left hj hkR.le
        _ = 1/(4*(k:ℝ)) := by field_simp; ring
        _ ≤ _ := one_div_le_one_div_of_le (by positivity) (by linarith)
    · rw [erase_eq_of_not_mem hmem] at hbase
      exact hbase.trans (le_add_of_nonneg_right (by split <;> positivity))
  have hlR : (0:ℝ)<l := by exact_mod_cast (hk.trans_le hkl)
  have huR : (0:ℝ)<u := by exact_mod_cast (hk.trans_le (hkl.trans hlu))
  have hg : checkerDegreeFloor i=((i-1:ℕ):ℝ)/4 := if_neg (by omega)
  have hfloorN : ((i-1)*k) ≤ 4*l+4 := by
    dsimp [l]
    have h := Nat.div_add_mod ((i-1)*k) 4
    have hrem := Nat.mod_lt ((i-1)*k) (by decide : 0 < 4)
    omega
  have hfloor : ((i-1:ℕ):ℝ)*k ≤ 4*(l:ℝ)+4 := by exact_mod_cast hfloorN
  have hKinv : (1/(K:ℝ))*k ≥ 1 := by
    rw [one_div_mul_eq_div]
    exact (one_le_div hKR).mpr hKkR
  have hl1 : checkerDegreeFloor i-1/(K:ℝ) ≤ (l:ℝ)/k := by
    apply (le_div_iff₀ hkR).mpr
    rw [hg]
    nlinarith only [hfloor,hKinv]
  have hiR : (0:ℝ) < i := by exact_mod_cast (show 0 < i by omega)
  have hleft : (k:ℝ)/(l:ℝ) ≤ 1/(checkerDegreeFloor i-1/(K:ℝ)) := by
    rw [show (k:ℝ)/(l:ℝ) = 1/((l:ℝ)/k) by field_simp]
    apply one_div_le_one_div_of_le _ hl1
    rw [hg]
    have hq : (1:ℝ)/(K:ℝ) ≤ 1/2 := one_div_le_one_div_of_le (by norm_num)
      (by exact_mod_cast hK)
    have hiR' : (4:ℝ) ≤ ((i-1:ℕ):ℝ) := by exact_mod_cast (show 4 ≤ i-1 by omega)
    linarith
  have hceilingN : 4*u ≤ i*k := by
    have h := Nat.div_add_mod (i*k) 4
    have hu' : u ≤ i*k/4 := min_le_left _ _
    omega
  have hceiling : 4*(u:ℝ) ≤ (i:ℝ)*k := by exact_mod_cast hceilingN
  have hright : 4/(i:ℝ) ≤ (k:ℝ)/(u:ℝ) := (div_le_div_iff₀ hiR huR).mpr (by linarith)
  apply hprime.trans
  simp only [checkerDegreeMass,if_neg (by omega : ¬ i < 4),if_neg (by omega : i≠4),if_pos hi8]
  linarith only [hleft,hright]

theorem primitiveDegrees_below_four {k N i : ℕ} (hk : 0 < k) (hi : i < 4) :
    primitiveDegrees k N i = ∅ := by
  apply eq_empty_iff_forall_not_mem.mpr
  intro s hs
  obtain ⟨hm,he⟩ := mem_filter.mp hs
  have hks := (mem_Icc.mp hm).1
  have hbin : 4 ≤ degreeBin k s := by
    apply (Nat.le_div_iff_mul_le hk).2
    have := Nat.mul_le_mul_left 4 hks
    omega
  omega

/-- Every coefficient envelope used by the scalar checker, including the
isolated atom and the right endpoint of its first ordinary block. -/
theorem primitive_all_checker_bin_mass {K k N i : ℕ} (hK : 2 ≤ K) (hKk : K ≤ k)
    (b : ℕ → ℝ) (hatom : b k=1/(k:ℝ))
    (hfirst : ∀ s : ℕ, k < s → s < 2*k → b s = -1/((s:ℝ)*((s:ℝ)-1)))
    (hjump : |b (2*k)| ≤ 1/(4*(k:ℝ)^2))
    (hblock : ∀ j s : ℕ, 2 ≤ j → j*k < s → s ≤ (j+1)*k →
      |b s| ≤ 1/(2*(j.factorial:ℝ)*(k:ℝ)^2)) :
    (k:ℝ)*(∑ s ∈ primitiveDegrees k N i, |b s|) ≤ checkerDegreeMass K i := by
  have hk : 0 < k := by omega
  by_cases hi : i < 4
  · simp [primitiveDegrees_below_four hk hi,checkerDegreeMass,hi]
  by_cases he : i=4
  · subst i
    simp only [checkerDegreeMass,if_neg (by decide : ¬4 < 4),if_pos rfl]
    by_cases hN : k ≤ N
    · exact (primitive_atom_mass hk hN b hatom).le
    · have hz : primitiveDegrees k N 4 = ∅ := by
        apply eq_empty_iff_forall_not_mem.mpr
        intro s hs
        have := mem_Icc.mp (mem_filter.mp hs).1
        omega
      simp [hz]
  by_cases hi8 : i ≤ 8
  · exact primitive_first_checker_bin_mass hK hKk (by omega) hi8 b hfirst hjump
  have h := primitive_factorial_bin_mass (N:=N) hk (by omega : 9 ≤ i) b hblock
  apply h.trans
  simp only [checkerDegreeMass,if_neg hi,if_neg he,if_neg hi8]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hK0 : (0:ℝ)<K := Nat.cast_pos.mpr (by omega)
  exact add_le_add_left (one_div_le_one_div_of_le hK0 (by exact_mod_cast hKk)) _

#print axioms primitive_all_checker_bin_mass
#print axioms checker_degree_floor_le
#print axioms primitive_first_checker_bin_mass
end OpenMathResearch.LongCycleExcedances
