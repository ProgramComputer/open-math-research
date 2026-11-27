import DyadicStarCertificate
import Mathlib.Data.Rat.Floor

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 2048
namespace OpenMathResearch.LongCycleExcedances
open Finset

def linearScale : ℕ := 2^56

def rationalDegreeFloor (i : ℕ) : ℚ := if i=4 then 1 else ((i-1:ℕ):ℚ)/4
def rationalDegreeMass (K i : ℕ) : ℚ :=
  if i < 4 then 0 else if i=4 then 1 else if i ≤ 8 then
    1/(rationalDegreeFloor i-1/(K:ℚ))-4/(i:ℚ)+(if i=8 then 1/(4*(K:ℚ)) else 0)
  else (1/4+1/(K:ℚ))/(2*(((i-1)/4).factorial:ℚ))

def linearShape (K i X : ℕ) : ℚ :=
  (rationalDegreeFloor i-1/(K:ℚ))*(6/5)/(192*(X:ℚ))

def rationalOdd (q : ℤ) : ℚ := 2*(q:ℚ)+1

def linearWeight (c : ℚ) (q : ℤ) : ℕ :=
  ⌈(linearScale:ℚ)*((1+c*(rationalOdd q^2-1))^96)⁻¹⌉₊

def linearGapWeight (c : ℚ) (a q : ℤ) : ℕ :=
  ⌈(linearWeight c q:ℚ)/(oddGap q a:ℚ)⌉₊

private def linearWeights (c : ℚ) : Array ℕ :=
  Array.ofFn (fun j : Fin 64 => linearWeight c ((j.val:ℤ)-32))

private def linearHeadIndex (q : ℤ) : Fin 64 := ⟨(q+32).toNat%64, Nat.mod_lt _ (by decide)⟩

private def linearNonnegativeInterval (count : ℕ) (start : ℤ) : Finset ℤ :=
  (range count).map ⟨fun j : ℕ => start+(j:ℤ), fun _ _ h => by exact_mod_cast add_left_cancel h⟩

private theorem mem_linearNonnegativeInterval (count : ℕ) (start q : ℤ) :
    q ∈ linearNonnegativeInterval count start ↔ start ≤ q ∧ q < start+(count:ℤ) := by
  rw [linearNonnegativeInterval,mem_map]
  constructor
  · rintro ⟨j,hj,rfl⟩
    have hh := mem_range.mp hj
    change start ≤ start+(j:ℤ) ∧ start+(j:ℤ) < start+(count:ℤ)
    omega
  · intro h
    let j := (q-start).toNat
    have hj : (j:ℤ)=q-start := Int.toNat_of_nonneg (by omega)
    refine ⟨j,mem_range.mpr (by omega),?_⟩
    change start+(j:ℤ)=q
    omega

private def linearHeadPoles : Finset ℤ := linearNonnegativeInterval 64 (-32)
private def linearCenters : Finset ℤ := linearNonnegativeInterval 66 (-33)

private theorem linearHeadPoles_eq : linearHeadPoles = signedHead 31 := by
  ext q
  simp only [linearHeadPoles,mem_linearNonnegativeInterval,signedHead,mem_Icc]
  norm_num
  omega

private theorem linearCenters_eq : linearCenters = signedCenters 31 := by
  ext q
  simp only [linearCenters,mem_linearNonnegativeInterval,signedCenters,mem_Icc]
  norm_num
  omega

def linearHead (c : ℚ) : ℕ :=
  let W := linearWeights c
  linearCenters.sup (fun a => ∑ q ∈ linearHeadPoles.erase a,
    ⌈(W[(linearHeadIndex q).val]'(by simp [W,linearWeights]):ℚ)/
      (oddGap q a:ℚ)⌉₊)

theorem linearHead_eq (c : ℚ) :
    linearHead c =
      (signedCenters 31).sup (fun a => ∑ q ∈ (signedHead 31).erase a, linearGapWeight c a q) := by
  unfold linearHead
  rw [linearCenters_eq,linearHeadPoles_eq]
  apply sup_congr rfl
  intro a _
  apply sum_congr rfl
  intro q hq
  have hrange := mem_Icc.mp (mem_erase.mp hq).2
  change (-32:ℤ) ≤ q ∧ q ≤ 31 at hrange
  have h0 : 0 ≤ q+32 := by omega
  have h64 : (q+32).toNat < 64 := by omega
  have hq' : ((linearHeadIndex q).val:ℤ)-32 = q := by
    simp only [linearHeadIndex,Nat.mod_eq_of_lt h64,Int.toNat_of_nonneg h0]
    omega
  simp only [linearWeights,Array.getElem_ofFn,linearGapWeight,hq']

def linearFirstTail (c : ℚ) : ℕ :=
  ⌈(linearScale:ℚ)*((1+c*(63^2-1))^95)⁻¹/(190*c)⌉₊

def linearMassTail (c : ℚ) : ℕ := ⌈(linearFirstTail c:ℚ)/63⌉₊
def linearHalfTail (c : ℚ) : ℕ := ⌈(linearMassTail c:ℚ)/2⌉₊

/-- Exact production rounding order. The natural table has no real inputs. -/
def literalLinearTable (K X : ℕ) (A₀ : ℚ) (i : ℕ) : ℕ :=
  if i < 4 then 0 else
    let c := linearShape K i X
    ⌈rationalDegreeMass K i*((linearHead c+linearHalfTail c:ℕ):ℚ)/A₀⌉₊

private theorem cast_floor (i : ℕ) : (rationalDegreeFloor i:ℝ)=checkerDegreeFloor i := by
  by_cases h : i=4 <;> simp [rationalDegreeFloor,checkerDegreeFloor,h]

private theorem cast_mass (K i : ℕ) : (rationalDegreeMass K i:ℝ)=checkerDegreeMass K i := by
  by_cases h0 : i < 4
  · simp [rationalDegreeMass,checkerDegreeMass,h0]
  by_cases h1 : i=4
  · simp [rationalDegreeMass,checkerDegreeMass,h0,h1]
  by_cases h2 : i≤8
  · by_cases h3 : i=8 <;> simp [rationalDegreeMass,checkerDegreeMass,h0,h1,h2,h3,cast_floor]
  · simp [rationalDegreeMass,checkerDegreeMass,h0,h1,h2]

theorem cast_linearShape (K i X : ℕ) : (linearShape K i X:ℝ)=checkerShape K i (6/5) X := by
  unfold linearShape checkerShape
  push_cast
  rw [cast_floor]

private theorem ceiling_cast_upper (x : ℚ) : (x:ℝ) ≤ (⌈x⌉₊:ℝ) := by
  exact_mod_cast Nat.le_ceil x

theorem linearHead_upper (c : ℚ) (a : ℤ) (ha : a ∈ signedCenters 31) :
    (∑ q ∈ (signedHead 31).erase a, oddStarTerm (c:ℝ) a q) ≤
      (linearHead c:ℝ)/linearScale := by
  apply finite_star_dyadic_bound _ _ (by decide : 0 < linearScale) (linearWeight c) (linearGapWeight c a)
  · intro q _
    apply (le_div_iff₀ (by norm_num [linearScale] : (0:ℝ)<linearScale)).mpr
    have h := ceiling_cast_upper ((linearScale:ℚ)*((1+c*(rationalOdd q^2-1))^96)⁻¹)
    push_cast at h
    have hw : (⌈(linearScale:ℚ)*((1+c*(rationalOdd q^2-1))^96)⁻¹⌉₊:ℝ) =
        (linearWeight c q:ℝ) := rfl
    rw [hw] at h
    have ho : (rationalOdd q:ℝ) = primitiveOddNumber q := by simp [rationalOdd,primitiveOddNumber]
    rw [ho] at h
    simpa only [oddBinKernel,mul_comm] using h
  · intro q hq
    have hq' := (mem_erase.mp hq).1
    have hpos : 0 < oddGap q a := Int.natAbs_pos.mpr (mul_ne_zero (by decide) (sub_ne_zero.mpr hq'))
    have h := (div_le_iff₀ (show (0:ℚ)<oddGap q a by exact_mod_cast hpos)).mp (Nat.le_ceil
      ((linearWeight c q:ℚ)/(oddGap q a:ℚ)))
    rw [mul_comm] at h
    exact_mod_cast h
  · rw [linearHead_eq]
    exact le_sup (f:=fun t => ∑ q ∈ (signedHead 31).erase t, linearGapWeight c t q) ha

theorem linearTail_upper (c : ℚ) :
    oTail (c:ℝ) 63/(190*(c:ℝ)*63) ≤ 2*(linearHalfTail c:ℝ)/linearScale := by
  have hG : (0:ℝ)<linearScale := by norm_num [linearScale]
  have h1 := ceiling_cast_upper ((linearScale:ℚ)*((1+c*(63^2-1))^95)⁻¹/(190*c))
  have h2 := ceiling_cast_upper ((linearFirstTail c:ℚ)/63)
  have h3 := ceiling_cast_upper ((linearMassTail c:ℚ)/2)
  push_cast at h1 h2 h3
  have h1' : (linearScale:ℝ)*oTail (c:ℝ) 63/(190*(c:ℝ)) ≤ linearFirstTail c := by
    simpa only [linearFirstTail,oTail,oBase] using h1
  change (linearFirstTail c:ℝ)/63 ≤ linearMassTail c at h2
  change (linearMassTail c:ℝ)/2 ≤ linearHalfTail c at h3
  apply (le_div_iff₀ hG).mpr
  have hEq : oTail (c:ℝ) 63/(190*(c:ℝ)*63)*(linearScale:ℝ) =
      ((linearScale:ℝ)*oTail (c:ℝ) 63/(190*(c:ℝ)))/63 := by ring
  rw [hEq]
  have hh := (div_le_div_of_nonneg_right h1' (by norm_num : (0:ℝ)≤63)).trans h2
  linarith only [hh,h3]

theorem linearTable_rounding (K X : ℕ) (A₀ : ℚ) (i : ℕ) (hi : 4 ≤ i) (hA : (A₀:ℝ) ≠ 0) :
    checkerDegreeMass K i*(((linearHead (linearShape K i X):ℝ)/linearScale)
      +(2*(linearHalfTail (linearShape K i X):ℝ)/linearScale)/2)/(A₀:ℝ) ≤
      (literalLinearTable K X A₀ i:ℝ)/linearScale := by
  let c := linearShape K i X
  let H := linearHead c
  let T := linearHalfTail c
  have hG : (0:ℝ)<linearScale := by norm_num [linearScale]
  have hu := ceiling_cast_upper (rationalDegreeMass K i*((H+T:ℕ):ℚ)/A₀)
  push_cast at hu
  rw [cast_mass] at hu
  rw [literalLinearTable,if_neg (not_lt.mpr hi)]
  apply (le_div_iff₀ hG).mpr
  change checkerDegreeMass K i*((H:ℝ)/linearScale+
    (2*(T:ℝ)/linearScale)/2)/(A₀:ℝ)*linearScale ≤
      (⌈rationalDegreeMass K i*((H+T:ℕ):ℚ)/A₀⌉₊:ℝ)
  convert hu using 1
  · field_simp [hG.ne',hA] <;> ring
  · congr 1
    push_cast
    ring

#print axioms linearHead_upper
#print axioms linearTail_upper
#print axioms linearTable_rounding
end OpenMathResearch.LongCycleExcedances
