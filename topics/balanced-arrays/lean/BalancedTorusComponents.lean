import BalancedTorusMaxima
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Order.Compact

/-!
# Connected components of fixed-product torus maximizers

Each connected component of the modulus-maximizing set of a continuous pair-affine
objective contains a diagonal point. This applies to the truncated elementary
symmetric row objective of the balanced-array integral.
-/

namespace BalancedTorusComponents

open Complex BalancedPairCompression BalancedTorusMaxima Set
open scoped BigOperators ComplexConjugate

private def unitCircleSet : Set ℂ := {z | normSq z = 1}

private noncomputable def semicircle (sign a : ℝ) : ℂ :=
  (a : ℂ) + ((sign * Real.sqrt (1 - a ^ 2) : ℝ) : ℂ) * I

private theorem continuous_semicircle (sign : ℝ) : Continuous (semicircle sign) := by
  unfold semicircle
  fun_prop

private theorem normSq_semicircle {sign a : ℝ} (hs : sign ^ 2 = 1)
    (ha : a ∈ Icc (-1 : ℝ) 1) : normSq (semicircle sign a) = 1 := by
  have hn : 0 ≤ 1 - a ^ 2 := by
    have hh := mul_nonneg (show 0 ≤ 1 - a by linarith [ha.2])
      (show 0 ≤ 1 + a by linarith [ha.1])
    nlinarith only [hh]
  rw [semicircle, normSq_add_mul_I, mul_pow, hs, one_mul, Real.sq_sqrt hn]
  ring

private theorem unitCircle_eq_semicircles :
    unitCircleSet =
      semicircle 1 '' Icc (-1 : ℝ) 1 ∪ semicircle (-1) '' Icc (-1 : ℝ) 1 := by
  ext z
  constructor
  · intro hz
    have hsum : z.re ^ 2 + z.im ^ 2 = 1 := by
      simpa [unitCircleSet, normSq_apply, pow_two] using hz
    have hre : z.re ∈ Icc (-1 : ℝ) 1 := by
      have hs : z.re ^ 2 ≤ 1 := by linarith only [hsum, sq_nonneg z.im]
      have h : |z.re| ≤ 1 := (sq_le_sq₀ (abs_nonneg _) zero_le_one).1 (by simpa using hs)
      exact abs_le.mp h
    have him : Real.sqrt (1 - z.re ^ 2) = |z.im| := by
      rw [show 1 - z.re ^ 2 = z.im ^ 2 by linarith only [hsum], Real.sqrt_sq_eq_abs]
    by_cases hs : 0 ≤ z.im
    · left
      refine ⟨z.re, hre, ?_⟩
      apply Complex.ext <;> simp [semicircle, him, abs_of_nonneg hs]
    · right
      refine ⟨z.re, hre, ?_⟩
      apply Complex.ext <;> simp [semicircle, him, abs_of_neg (lt_of_not_ge hs)]
  · rintro (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩)
    · exact normSq_semicircle (by norm_num) ha
    · exact normSq_semicircle (by norm_num) ha

private theorem isPreconnected_unitCircle : IsPreconnected unitCircleSet := by
  rw [unitCircle_eq_semicircles]
  apply IsPreconnected.union (1 : ℂ)
  · refine ⟨1, by norm_num, ?_⟩
    simp [semicircle]
  · refine ⟨1, by norm_num, ?_⟩
    simp [semicircle]
  · exact isPreconnected_Icc.image _ (continuous_semicircle 1).continuousOn
  · exact isPreconnected_Icc.image _ (continuous_semicircle (-1)).continuousOn

private theorem isCompact_unitCircle : IsCompact unitCircleSet := by
  convert isCompact_sphere (0 : ℂ) 1 using 1
  ext z
  change normSq z = 1 ↔ dist z 0 = 1
  rw [dist_zero_right, normSq_eq_norm_sq]
  simpa using sq_eq_sq₀ (norm_nonneg z) (show 0 ≤ (1 : ℝ) by norm_num)

variable {ι : Type*} [Fintype ι]

theorem isCompact_unitProductTorus (p : ℂ) :
    IsCompact (unitProductTorus (ι := ι) p) := by
  have hcompact : IsCompact {x : ι → ℂ | ∀ i, x i ∈ unitCircleSet} :=
    isCompact_pi_infinite (fun _ => isCompact_unitCircle)
  have hclosed : IsClosed {x : ι → ℂ | (∏ i, x i) = p} :=
    isClosed_eq (continuous_finset_prod _ fun i _ => continuous_apply i) continuous_const
  exact hcompact.inter_right hclosed

/-- The set of all squared-modulus maximizers on a unit fixed-product torus. -/
def modulusMaxima (p : ℂ) (f : (ι → ℂ) → ℂ) : Set (ι → ℂ) :=
  {x | x ∈ unitProductTorus p ∧ ∀ y ∈ unitProductTorus p, normSq (f y) ≤ normSq (f x)}

theorem modulusMaxima_nonempty {p : ℂ} {f : (ι → ℂ) → ℂ} (hf : Continuous f)
    (hp : (unitProductTorus (ι := ι) p).Nonempty) : (modulusMaxima p f).Nonempty := by
  obtain ⟨x, hx, hmax⟩ := (isCompact_unitProductTorus p).exists_isMaxOn hp
    (continuous_normSq.comp hf).continuousOn
  exact ⟨x, hx, fun _ hy => hmax hy⟩

private theorem isCompact_modulusMaxima {p : ℂ} {f : (ι → ℂ) → ℂ} (hf : Continuous f)
    {x : ι → ℂ} (hx : x ∈ modulusMaxima p f) : IsCompact (modulusMaxima p f) := by
  have hclosed : IsClosed {y : ι → ℂ | normSq (f y) = normSq (f x)} :=
    isClosed_eq (continuous_normSq.comp hf) continuous_const
  have hlevel : modulusMaxima p f =
      unitProductTorus p ∩ {y : ι → ℂ | normSq (f y) = normSq (f x)} := by
    ext y
    constructor
    · intro hy
      exact ⟨hy.1, le_antisymm (hx.2 y hy.1) (hy.2 x hx.1)⟩
    · intro hy
      exact ⟨hy.1, fun z hz => (hx.2 z hz).trans_eq hy.2.symm⟩
  rw [hlevel]
  exact (isCompact_unitProductTorus p).inter_right hclosed

private theorem isCompact_component {α : Type*} [TopologicalSpace α] {S : Set α}
    (hS : IsCompact S) {x : α} (hx : x ∈ S) : IsCompact (connectedComponentIn S x) := by
  haveI : CompactSpace S := isCompact_iff_compactSpace.mp hS
  rw [connectedComponentIn_eq_image hx]
  exact isClosed_connectedComponent.isCompact.image continuous_subtype_val

variable [DecidableEq ι]

omit [Fintype ι] in
private theorem continuous_pairFiber (x : ι → ℂ) (i j : ι) :
    Continuous (fun u : ℂ => replacePair x i j u ((x i * x j) * conj u)) := by
  apply continuous_pi
  intro k
  by_cases hki : k = i
  · subst k
    simpa [replacePair] using (continuous_id : Continuous (fun z : ℂ => z))
  by_cases hkj : k = j
  · subst k
    simpa [replacePair, hki] using continuous_const.mul Complex.continuous_conj
  simpa [replacePair, hki, hkj] using (continuous_const : Continuous (fun _ : ℂ => x k))

/-- Every connected component of the maximizing set contains a diagonal point. -/
theorem exists_diagonal_in_modulusMaxima_component {p : ℂ} {f : (ι → ℂ) → ℂ}
    (hf : Continuous f) (h_aff : PairAffine f) {x₀ : ι → ℂ}
    (hx₀ : x₀ ∈ modulusMaxima p f) :
    ∃ x ∈ connectedComponentIn (modulusMaxima p f) x₀, ∀ i j, x i = x j := by
  have hcompact := isCompact_component (isCompact_modulusMaxima hf hx₀) hx₀
  have haux_cont : Continuous (fun x : ι → ℂ => normSq (∑ k, x k)) :=
    continuous_normSq.comp (continuous_finset_sum _ fun i _ => continuous_apply i)
  obtain ⟨x, hx_component, haux⟩ := hcompact.exists_isMaxOn
    ⟨x₀, mem_connectedComponentIn hx₀⟩ haux_cont.continuousOn
  refine ⟨x, hx_component, ?_⟩
  have hx : x ∈ modulusMaxima p f := connectedComponentIn_subset _ _ hx_component
  intro i j
  by_contra hxy
  have hij : i ≠ j := fun h => hxy (congrArg x h)
  obtain ⟨a, b, hab⟩ := h_aff x i j hij
  have hbase : f x = a + b * (x i + x j) := by
    simpa using hab (x i) (x j) rfl
  have hb : b = 0 := by
    apply slope_eq_zero_at_unit_pair_max (hx.1.1 i) (hx.1.1 j) hxy a b
    intro u hu hp
    have hprod : u * u = x i * x j := by simpa [pow_two] using hp
    have h := hx.2 _ (replacePair_mem_unitProductTorus hx.1 hij hu hu hprod)
    rwa [hab u u hprod, hbase] at h
  let g (u : ℂ) := replacePair x i j u ((x i * x j) * conj u)
  have hconj (u : ℂ) (hu : normSq u = 1) : conj u * u = 1 := by
    rw [← normSq_eq_conj_mul_self, hu, ofReal_one]
  have hfiber_max : g '' unitCircleSet ⊆ modulusMaxima p f := by
    rintro _ ⟨u, hu, rfl⟩
    have hv : normSq ((x i * x j) * conj u) = 1 := by
      rw [normSq_mul, normSq_mul, normSq_conj, hx.1.1 i, hx.1.1 j, hu, one_mul, one_mul]
    have hprod : u * ((x i * x j) * conj u) = x i * x j := by
      calc
        _ = (x i * x j) * (conj u * u) := by ring
        _ = _ := by rw [hconj u hu, mul_one]
    have heq : f (g u) = f x := by
      change f (replacePair x i j u ((x i * x j) * conj u)) = f x
      rw [hab _ _ hprod, hbase, hb]
      simp
    exact ⟨replacePair_mem_unitProductTorus hx.1 hij hu hv hprod, fun y hy => by
      rw [heq]
      exact hx.2 y hy⟩
  have hfiber_x : x ∈ g '' unitCircleSet := by
    refine ⟨x i, hx.1.1 i, ?_⟩
    have hprod : (x i * x j) * conj (x i) = x j := by
      calc
        _ = x j * (conj (x i) * x i) := by ring
        _ = _ := by rw [hconj _ (hx.1.1 i), mul_one]
    simp [g, hprod]
  have hconn : IsPreconnected (g '' unitCircleSet) :=
    isPreconnected_unitCircle.image _ (continuous_pairFiber x i j).continuousOn
  have hsub := hconn.subset_connectedComponentIn hfiber_x hfiber_max
  have hcomponent_eq := connectedComponentIn_eq hx_component
  rw [← hcomponent_eq] at hsub
  let c := ∑ k ∈ (Finset.univ.erase i).erase j, x k
  obtain ⟨u, hu, hp, hlt⟩ := exists_compressing_unit_pair (hx.1.1 i) (hx.1.1 j) hxy
    c 1 one_ne_zero
  have hug : g u = replacePair x i j u u := by
    have heq : (x i * x j) * conj u = u := by
      rw [← hp]
      calc
        u ^ 2 * conj u = u * (conj u * u) := by ring
        _ = u := by rw [hconj u hu, mul_one]
    simp [g, heq]
  have hmem : replacePair x i j u u ∈ connectedComponentIn (modulusMaxima p f) x₀ := by
    rw [← hug]
    exact hsub ⟨u, hu, rfl⟩
  have hreplace : (∑ k, replacePair x i j u u k) = c + 1 * (u + u) := by
    rw [sum_replacePair x i j hij]
    dsimp [c]
    ring
  have hsum : (∑ k, x k) = c + 1 * (x i + x j) := by
    have h := sum_replacePair x i j hij (x i) (x j)
    rw [replacePair_same] at h
    rw [h]
    dsimp [c]
    ring
  have h := haux hmem
  change normSq (∑ k, replacePair x i j u u k) ≤ normSq (∑ k, x k) at h
  rw [hreplace, hsum] at h
  exact (not_le_of_gt hlt) h

omit [DecidableEq ι] in
theorem continuous_rowObjective (r : ℕ) (hr : r ≤ Fintype.card ι) :
    Continuous (rowObjective (ι := ι) r) := by
  change Continuous (fun x : ι → ℂ => rowObjective r x)
  simp_rw [rowObjective_eq_elementary_sum r hr]
  exact continuous_finset_sum _ fun _ _ => continuous_finset_sum _ fun _ _ =>
    continuous_finset_prod _ fun i _ => continuous_apply i

/-- The component theorem for the actual balanced-array row objective at unit radius. -/
theorem rowObjective_exists_diagonal_in_component (r : ℕ) (hr : r ≤ Fintype.card ι)
    {p : ℂ} {x₀ : ι → ℂ} (hx₀ : x₀ ∈ modulusMaxima p (rowObjective r)) :
    ∃ x ∈ connectedComponentIn (modulusMaxima p (rowObjective r)) x₀, ∀ i j, x i = x j :=
  exists_diagonal_in_modulusMaxima_component (continuous_rowObjective r hr)
    (pairAffine_rowObjective r) hx₀

omit [Fintype ι] in
private theorem pairAffine_dilate {f : (ι → ℂ) → ℂ} (hf : PairAffine f) (t : ℂ) :
    PairAffine (fun x => f (fun k => t * x k)) := by
  intro x i j hij
  obtain ⟨a, b, hab⟩ := hf (fun k => t * x k) i j hij
  refine ⟨a, b * t, ?_⟩
  intro u v hp
  have hprod : (t * u) * (t * v) = (t * x i) * (t * x j) := by
    calc
      _ = t ^ 2 * (u * v) := by ring
      _ = _ := by rw [hp]; ring
  have hreplace : (fun k => t * replacePair x i j u v k) =
      replacePair (fun k => t * x k) i j (t * u) (t * v) := by
    funext k
    by_cases hki : k = i
    · subst k
      simp [replacePair]
    by_cases hkj : k = j
    · subst k
      simp [replacePair, hki]
    simp [replacePair, hki, hkj]
  change f (fun k => t * replacePair x i j u v k) = _
  rw [hreplace, hab _ _ hprod]
  ring

/-- The component theorem for the balanced-array row objective at any fixed radius,
using unit torus coordinates and dilation by the parameter. -/
theorem dilated_rowObjective_exists_diagonal_in_component (r : ℕ) (hr : r ≤ Fintype.card ι)
    (t : ℂ) {p : ℂ} {x₀ : ι → ℂ}
    (hx₀ : x₀ ∈ modulusMaxima p (fun x => rowObjective r (fun k => t * x k))) :
    ∃ x ∈ connectedComponentIn
      (modulusMaxima p (fun x => rowObjective r (fun k => t * x k))) x₀,
      ∀ i j, x i = x j :=
  exists_diagonal_in_modulusMaxima_component
    ((continuous_rowObjective r hr).comp
      (continuous_pi fun k => continuous_const.mul (continuous_apply k)))
    (pairAffine_dilate (pairAffine_rowObjective r) t) hx₀

end BalancedTorusComponents
