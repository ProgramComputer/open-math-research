import PrismFamilyCounts

/-! Direct integer reflection for the two prism family lattice counts. -/

namespace PrismFamily

open PrismSplit
open scoped BigOperators fwdDiff

private theorem choose_reflection (x : Int) (d : Nat) :
    (-1 : Int) ^ d * Ring.choose x d = Ring.choose ((d : Int) - 1 - x) d := by
  have h := Ring.choose_neg (x - (d : Int) + 1) d
  rw [show -(x - (d : Int) + 1) = (d : Int) - 1 - x by abel,
    show (x - (d : Int) + 1) + (d : Int) - 1 = x by abel,
    Units.smul_def, Int.coe_negOnePow_natCast, smul_eq_mul] at h
  exact h.symm

private noncomputable def interiorRows (n d k w e q : Nat) : Int :=
  ∑ j ∈ Finset.range (n + 1), if j + w < k then
    (-1 : Int) ^ j * (n.choose j : Int) * ((((k - (j + w)) * q + (j + e) - 1).choose d : Nat) : Int)
    else 0

private theorem intSignedRows_reflected (n d k w e q : Nat) (hq : 0 < q) (hd : k - 1 + e ≤ d) :
    (-1 : Int) ^ d * intSignedRows n d k w e (-(q : Int)) = interiorRows n d k w e q := by
  rw [intSignedRows, Finset.sum_apply, Finset.mul_sum, interiorRows]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j + w < k
  · have hje : j + e ≤ d := by omega
    have hpos := Nat.mul_pos (Nat.sub_pos_of_lt hj) hq
    have hsum : 1 ≤ (k - (j + w)) * q + (j + e) := by omega
    simp only [hj, if_true, Pi.smul_apply, smul_eq_mul, intAffineChoose]
    rw [mul_left_comm, choose_reflection,
      ← Ring.choose_natCast (R := Int) ((k - (j + w)) * q + (j + e) - 1) d]
    congr 2
    push_cast [Nat.cast_sub hje, Nat.cast_sub hsum]
    ring
  · simp [hj]

private theorem coeff_interiorShift (d k w e j q : Nat)
    (hq : 2 ≤ q) (hk : d + 1 ≤ k * q) (hew : e ≤ w) (hje : j + e ≤ d + 1)
    (hmax : j + e = d + 1 → k < j + w) :
    PowerSeries.coeff Int (k * q - (d + 1))
      (PowerSeries.X ^ ((q - 1) * j + (w * q - e)) *
        PowerSeries.mk (fun x => ((d + x).choose d : Int))) =
      if j + w < k then ((((k - (j + w)) * q + (j + e) - 1).choose d : Nat) : Int) else 0 := by
  let target := k * q - (d + 1)
  let shift := (q - 1) * j + (w * q - e)
  change PowerSeries.coeff Int target (PowerSeries.X ^ shift * _) = _
  have htar : (target : Int) = (k : Int) * q - (d + 1 : Nat) := by
    dsimp only [target]
    rw [Nat.cast_sub hk, Nat.cast_mul]
  have hmul : e ≤ w * q := hew.trans (by
    simpa only [mul_one] using Nat.mul_le_mul_left w (show 1 ≤ q by omega))
  have hshift : (shift : Int) = ((j + w : Nat) : Int) * q - (j + e : Nat) := by
    simp only [shift, Nat.cast_add, Nat.cast_mul, Nat.cast_sub hmul,
      Nat.cast_sub (show 1 ≤ q by omega), Nat.cast_one]
    ring
  rw [PowerSeries.coeff_X_pow_mul']
  by_cases hj : j + w < k
  · have hp := Nat.mul_pos (Nat.sub_pos_of_lt hj) (show 0 < q by omega)
    have hpos : 1 ≤ (k - (j + w)) * q + (j + e) := by omega
    have hcast : (((k - (j + w)) * q + (j + e) - 1 : Nat) : Int) =
        ((k : Int) - (j + w : Nat)) * q + (j + e : Nat) - 1 := by
      simp only [Nat.cast_sub hpos, Nat.cast_add, Nat.cast_mul,
        Nat.cast_sub hj.le, Nat.cast_one]
    have hdiff : (target : Int) - shift + d =
        (((k - (j + w)) * q + (j + e) - 1 : Nat) : Int) := by
      rw [htar, hshift, hcast, sub_mul, Nat.cast_add, Nat.cast_one]
      omega
    rw [if_pos hj]
    by_cases hst : shift ≤ target
    · rw [if_pos hst, PowerSeries.coeff_mk]
      congr 2
      exact_mod_cast (show ((d + (target - shift) : Nat) : Int) =
          (((k - (j + w)) * q + (j + e) - 1 : Nat) : Int) by
        rw [Nat.cast_add, Nat.cast_sub hst]
        linarith only [hdiff])
    · rw [if_neg hst, Nat.choose_eq_zero_of_lt]
      · simp
      · have hs : (target : Int) < shift := by exact_mod_cast (Nat.lt_of_not_ge hst)
        exact_mod_cast (show (((k - (j + w)) * q + (j + e) - 1 : Nat) : Int) < d by
          omega)
  · have hle : (k : Int) * q ≤ ((j + w : Nat) : Int) * q := by
      exact_mod_cast Nat.mul_le_mul_right q (show k ≤ j + w by omega)
    have hlt : (target : Int) < shift := by
      rw [htar, hshift]
      by_cases hcase : j + e = d + 1
      · have hmul := Nat.mul_lt_mul_of_pos_right (hmax hcase) (show 0 < q by omega)
        have hm : (k : Int) * q < ((j + w : Nat) : Int) * q := by exact_mod_cast hmul
        omega
      · omega
    have hn : target < shift := by exact_mod_cast hlt
    rw [if_neg (not_le_of_gt hn), if_neg hj]

private theorem coeff_interiorRows (n d k w e q : Nat)
    (hq : 2 ≤ q) (hk : d + 1 ≤ k * q) (hew : e ≤ w) (hn : n + e ≤ d + 1)
    (hmax : ∀ j ≤ n, j + e = d + 1 → k < j + w) :
    PowerSeries.coeff Int (k * q - (d + 1))
      ((1 - PowerSeries.X ^ (q - 1)) ^ n * PowerSeries.X ^ (w * q - e) *
        PowerSeries.mk (fun x => ((d + x).choose d : Int))) = interiorRows n d k w e q := by
  rw [one_sub_X_pow_expansion, Finset.sum_mul, Finset.sum_mul, map_sum, interiorRows]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  rw [mul_assoc, mul_assoc, PowerSeries.coeff_C_mul,
    ← mul_assoc (PowerSeries.X ^ ((q - 1) * j)) (PowerSeries.X ^ (w * q - e)),
    ← pow_add, coeff_interiorShift d k w e j q hq hk hew
        (by omega) (hmax j hjn)]
  by_cases h : j + w < k <;> simp [h]

def beforeInterior (b q : Nat) : Int :=
  if q < 2 then 0
  else (boundedCount (List.replicate (2 * b) (q - 2) ++ [2 * q - 2])
    ((b + 1) * q - (2 * b + 1)) : Int)

def afterInterior (b q : Nat) : Int :=
  if q < 2 then 0
  else (boundedCount (List.replicate (2 * b + 2) (q - 2))
    ((b + 1) * q - (2 * b + 2)) : Int)

private theorem beforeInterior_rows (b q : Nat) (hq : 2 ≤ q) :
    beforeInterior b q =
      interiorRows (2 * b) (2 * b) (b + 1) 0 0 q -
        interiorRows (2 * b) (2 * b) (b + 1) 2 1 q := by
  rw [beforeInterior, if_neg (not_lt_of_ge hq), ← boxSeries_coeff,
    boxSeries_append, boxSeries_replicate]
  simp only [boxSeries, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [capSeries_eq, capSeries_eq, mul_pow,
    show q - 2 + 1 = q - 1 by omega, show 2 * q - 2 + 1 = 2 * q - 1 by omega]
  have h :
      (1 - PowerSeries.X ^ (q - 1)) ^ (2 * b) * (PowerSeries.mk 1 : PowerSeries Int) ^ (2 * b) *
        ((1 - PowerSeries.X ^ (2 * q - 1)) * PowerSeries.mk 1) =
      (1 - PowerSeries.X ^ (q - 1)) ^ (2 * b) * PowerSeries.X ^ (0 * q - 0) *
        (PowerSeries.mk 1 : PowerSeries Int) ^ (2 * b + 1) -
      (1 - PowerSeries.X ^ (q - 1)) ^ (2 * b) * PowerSeries.X ^ (2 * q - 1) *
        (PowerSeries.mk 1 : PowerSeries Int) ^ (2 * b + 1) := by
    simp only [zero_mul, Nat.sub_zero, pow_zero, mul_one, pow_succ (PowerSeries.mk 1) (2 * b)]
    ring
  have hk : 2 * b + 1 ≤ (b + 1) * q := by
    have hm := Nat.mul_le_mul_left (b + 1) hq
    omega
  rw [h, PowerSeries.mk_one_pow_eq_mk_choose_add, map_sub,
    coeff_interiorRows (2 * b) (2 * b) (b + 1) 0 0 q hq hk (by omega) (by omega)
      (fun j hj hu => by omega),
    coeff_interiorRows (2 * b) (2 * b) (b + 1) 2 1 q hq hk (by omega) (by omega)
      (fun j hj hu => by omega)]

private theorem afterInterior_rows (b q : Nat) (hq : 2 ≤ q) :
    afterInterior b q = interiorRows (2 * b + 2) (2 * b + 1) (b + 1) 0 0 q := by
  rw [afterInterior, if_neg (not_lt_of_ge hq), ← boxSeries_coeff,
    boxSeries_replicate, capSeries_eq, mul_pow, show q - 2 + 1 = q - 1 by omega,
    PowerSeries.mk_one_pow_eq_mk_choose_add Int (2 * b + 1)]
  have hk : 2 * b + 2 ≤ (b + 1) * q := by
    have hm := Nat.mul_le_mul_left (b + 1) hq
    omega
  have h := coeff_interiorRows (2 * b + 2) (2 * b + 1) (b + 1) 0 0 q hq hk
    (by omega) (by omega) (fun j hj hu => by omega)
  simpa only [zero_mul, Nat.sub_zero, pow_zero, mul_one] using h

private theorem interiorRows_one (n d k w e : Nat) (hew : e ≤ w) (hd : k ≤ d) :
    interiorRows n d k w e 1 = 0 := by
  unfold interiorRows
  apply Finset.sum_eq_zero
  intro j _
  by_cases h : j + w < k
  · rw [if_pos h, Nat.choose_eq_zero_of_lt (by
      simp only [Nat.mul_one]
      omega : (k - (j + w)) * 1 + (j + e) - 1 < d)]
    simp
  · rw [if_neg h]

theorem beforeInterior_reflection (b q : Nat) (hb : 2 ≤ b) (hq : 0 < q) :
    (-1 : Int) ^ (2 * b) * beforeIntExtension b (-(q : Int)) = beforeInterior b q := by
  rw [beforeIntExtension, Pi.sub_apply, mul_sub,
    intSignedRows_reflected _ _ _ _ _ q hq (by omega),
    intSignedRows_reflected _ _ _ _ _ q hq (by omega)]
  by_cases h2 : 2 ≤ q
  · rw [beforeInterior_rows b q h2]
  · have h1 : q = 1 := by omega
    subst q
    rw [interiorRows_one _ _ _ _ _ (by omega) (by omega),
      interiorRows_one _ _ _ _ _ (by omega) (by omega)]
    rfl

theorem afterInterior_reflection (b q : Nat) (hb : 2 ≤ b) (hq : 0 < q) :
    (-1 : Int) ^ (2 * b + 1) * afterIntExtension b (-(q : Int)) = afterInterior b q := by
  rw [afterIntExtension, intSignedRows_reflected _ _ _ _ _ q hq (by omega)]
  by_cases h2 : 2 ≤ q
  · rw [afterInterior_rows b q h2]
  · have h1 : q = 1 := by omega
    subst q
    rw [interiorRows_one _ _ _ _ _ (by omega) (by omega)]
    rfl

#print axioms beforeInterior_reflection
#print axioms afterInterior_reflection

end PrismFamily
