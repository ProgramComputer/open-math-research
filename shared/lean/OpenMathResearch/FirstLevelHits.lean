import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace OpenMathResearch.FirstLevelHits

open Set Filter
open scoped Topology

/-- A continuous function with a left tail below a level and a right sample above
it has a first occurrence of that level. -/
theorem exists_firstLevelHit {f : ℝ → ℝ} (hf : Continuous f) {a b y : ℝ}
    (hab : a ≤ b) (ha : ∀ x ≤ a, f x < y) (hb : y < f b) :
    ∃ x : ℝ, IsLeast (f ⁻¹' {y}) x := by
  have hs : IsCompact (Icc a b ∩ f ⁻¹' {y}) :=
    isCompact_Icc.inter_right (isClosed_singleton.preimage hf)
  obtain ⟨z, hz, hzval⟩ :=
    intermediate_value_Icc hab hf.continuousOn ⟨(ha a le_rfl).le, hb.le⟩
  obtain ⟨x, hx, hleast⟩ := hs.exists_isLeast ⟨z, hz, hzval⟩
  refine ⟨x, hx.2, ?_⟩
  intro t ht
  have htval : f t = y := ht
  have hat : a ≤ t := by
    by_contra! h
    exact (ha t h.le).ne htval
  by_cases htb : t ≤ b
  · exact hleast ⟨⟨hat, htb⟩, ht⟩
  · exact hx.1.2.trans (le_of_not_ge htb)

/-- On a continuous phase with distinct endpoint limits, the first hits of
all intervening levels are strictly ordered. No monotonicity of the phase is needed. -/
theorem exists_ordered_firstLevelHits {f : ℝ → ℝ} (hf : Continuous f) {l u : ℝ}
    (hl : Tendsto f atBot (𝓝 l)) (hu : Tendsto f atTop (𝓝 u)) :
    ∃ hit : Ioo l u → ℝ,
      StrictMono hit ∧ ∀ y, IsLeast (f ⁻¹' {y.val}) (hit y) := by
  classical
  have existsHit (y : Ioo l u) : ∃ x : ℝ, IsLeast (f ⁻¹' {y.val}) x := by
    obtain ⟨a, ha⟩ := eventually_atBot.mp (hl.eventually (Iio_mem_nhds y.property.1))
    obtain ⟨b, hb⟩ := eventually_atTop.mp (hu.eventually (Ioi_mem_nhds y.property.2))
    exact exists_firstLevelHit hf (le_max_left a b) ha
      (hb (max a b) (le_max_right a b))
  choose hit hhit using existsHit
  refine ⟨hit, ?_, hhit⟩
  intro y z hyz
  obtain ⟨a, ha⟩ := eventually_atBot.mp (hl.eventually (Iio_mem_nhds y.property.1))
  have hzval : f (hit z) = z.val := (hhit z).1
  have hyz' : y.val < z.val := hyz
  have hza : a ≤ hit z := by
    by_contra! h
    have hzy : z.val < y.val := hzval ▸ ha (hit z) h.le
    exact (not_lt_of_ge hyz'.le) hzy
  have hm : y.val ∈ Icc (f a) (f (hit z)) := ⟨(ha a le_rfl).le, hzval.symm ▸ hyz'.le⟩
  obtain ⟨w, hw, hwval⟩ := intermediate_value_Icc hza hf.continuousOn hm
  have hwlt : w < hit z :=
    lt_of_le_of_ne hw.2 (fun h => hyz.ne (Subtype.ext (hwval.symm.trans (h ▸ hzval))))
  exact lt_of_le_of_lt ((hhit y).2 hwval) hwlt

/-- The same ordered first hits on positive radii, expressed using a continuous
phase in the logarithmic radius. -/
theorem exists_ordered_positive_phase_radii {phase : ℝ → ℝ} {l u : ℝ}
    (hf : Continuous (fun x => phase (Real.exp x)))
    (hl : Tendsto (fun x => phase (Real.exp x)) atBot (𝓝 l))
    (hu : Tendsto (fun x => phase (Real.exp x)) atTop (𝓝 u)) :
    ∃ radius : Ioo l u → ℝ,
      StrictMono radius ∧ (∀ y, 0 < radius y) ∧
        ∀ y, IsLeast {v | 0 < v ∧ phase v = y.val} (radius y) := by
  obtain ⟨hit, hmono, hhit⟩ := exists_ordered_firstLevelHits hf hl hu
  refine ⟨Real.exp ∘ hit, Real.exp_strictMono.comp hmono, fun y => Real.exp_pos _, ?_⟩
  intro y
  refine ⟨⟨Real.exp_pos _, (hhit y).1⟩, ?_⟩
  intro v hv
  have hlogval : phase (Real.exp (Real.log v)) = y.val := by
    rw [Real.exp_log hv.1]
    exact hv.2
  have hle : hit y ≤ Real.log v := (hhit y).2 hlogval
  simpa only [Function.comp_apply, Real.exp_log hv.1] using Real.exp_le_exp.mpr hle

#print axioms exists_firstLevelHit
#print axioms exists_ordered_firstLevelHits
#print axioms exists_ordered_positive_phase_radii

/-- The first hit inside a compact interval can occur at its right endpoint. -/
theorem exists_firstLevelHitOn {f : ℝ → ℝ} {a b y : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hab : a ≤ b) (ha : f a ≤ y) (hb : y ≤ f b) :
    ∃ x, IsLeast (Icc a b ∩ f ⁻¹' {y}) x := by
  obtain ⟨z, hz, hzy⟩ := intermediate_value_Icc hab hf ⟨ha, hb⟩
  have hc : IsCompact (Icc a b ∩ f ⁻¹' {y}) :=
    isCompact_Icc.of_isClosed_subset
      (hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton) inter_subset_left
  exact hc.exists_isLeast ⟨z, hz, hzy⟩

/-- Between the last lower hit before the first upper hit and that upper
hit, a continuous phase lies strictly between the levels. -/
theorem exists_lastLower_before_firstUpper {f : ℝ → ℝ} {a b l u q : ℝ}
    (hf : ContinuousOn f (Icc a b)) (ha : f a ≤ l) (hlu : l < u)
    (hq : IsLeast (Icc a b ∩ f ⁻¹' {u}) q) :
    ∃ p, IsGreatest (Icc a q ∩ f ⁻¹' {l}) p ∧ p < q ∧
      ∀ x ∈ Ioo p q, l < f x ∧ f x < u := by
  classical
  have hqv : f q = u := hq.1.2
  have hsub : Icc a q ⊆ Icc a b := fun _ hx => ⟨hx.1, hx.2.trans hq.1.1.2⟩
  have hfq := hf.mono hsub
  obtain ⟨z, hz, hzv⟩ := intermediate_value_Icc hq.1.1.1 hfq ⟨ha, hqv.symm ▸ hlu.le⟩
  have hc : IsCompact (Icc a q ∩ f ⁻¹' {l}) :=
    isCompact_Icc.of_isClosed_subset
      (hfq.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton) inter_subset_left
  obtain ⟨p, hp⟩ := hc.exists_isGreatest ⟨z, hz, hzv⟩
  have hpv : f p = l := hp.1.2
  refine ⟨p, hp, lt_of_le_of_ne hp.1.1.2 ?_, ?_⟩
  · intro he
    exact hlu.ne (hpv.symm.trans (he ▸ hqv))
  intro x hx
  have hax := hp.1.1.1.trans hx.1.le
  constructor
  · by_contra h
    have hcont := hfq.mono (show Icc x q ⊆ Icc a q from fun _ hy => ⟨hax.trans hy.1, hy.2⟩)
    obtain ⟨w, hw, hwv⟩ := intermediate_value_Icc hx.2.le hcont ⟨le_of_not_gt h, hqv.symm ▸ hlu.le⟩
    exact (not_le_of_gt (hx.1.trans_le hw.1)) (hp.2 ⟨⟨hax.trans hw.1, hw.2⟩, hwv⟩)
  · by_contra h
    have hcont := hfq.mono (show Icc a x ⊆ Icc a q from fun _ hy => ⟨hy.1, hy.2.trans hx.2.le⟩)
    obtain ⟨w, hw, hwv⟩ := intermediate_value_Icc hax hcont ⟨ha.trans hlu.le, le_of_not_gt h⟩
    exact (not_le_of_gt (hw.2.trans_lt hx.2)) (hq.2 ⟨⟨hw.1, hw.2.trans (hx.2.le.trans hq.1.1.2)⟩, hwv⟩)

#print axioms exists_firstLevelHitOn
#print axioms exists_lastLower_before_firstUpper
end OpenMathResearch.FirstLevelHits
