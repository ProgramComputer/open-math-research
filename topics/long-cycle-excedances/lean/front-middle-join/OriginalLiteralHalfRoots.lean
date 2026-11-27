import RepositoryCenterSign

set_option autoImplicit false
noncomputable section
namespace RepositoryQuotientAudit
open LongCycles LongCycleFinite Polynomial OpenMathResearch.LongCycleExcedances

/-- Strict interlacing of the quotient rows and weak interlacing of the
literal rows follow from signed literal singleton roots below modulus one. -/
theorem original_interlacing_of_literal_half_roots {n k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n)
    (u : Fin ((n-2)/2) → ℝ) (hmono : StrictMono u)
    (hw : ∀ i, 0 < u i ∧ u i < 1 ∧ (enumerator n k).eval (-u i) = 0 ∧
      0 < (-1:ℝ)^(i.val+2)*(enumerator (n+1) k).eval (-u i)) :
    StrictNegativeInterlacing (enumerator n k).divX (enumerator (n+1) k).divX (n-2) ∧
    WeakRealInterlacing (enumerator n k) (enumerator (n+1) k) := by
  let P := (enumerator n k).divX
  let Q := (enumerator (n+1) k).divX
  have heval (m : ℕ) (hm : 0 < m) (x : ℝ) :
      (enumerator m k).eval x = x*(enumerator m k).divX.eval x := by
    have h := (LongCycleBounds.Band.actual_general_cycle_row hk hm).trans
      (congrArg (fun R : ℝ[X] => X*R) (generalCycleQuotient_eq_divX m k hm hk))
    exact (congrArg (fun R : ℝ[X] => R.eval x) h).trans (by simp)
  have root (i) : P.IsRoot (-u i) := by
    have hz := (hw i).2.2.1
    rw [heval n (by omega)] at hz
    exact (mul_eq_zero.mp hz).resolve_left (neg_ne_zero.mpr (hw i).1.ne')
  have nextSign (i) : 0 < (-1:ℝ)^(i.val+1)*Q.eval (-u i) := by
    have hs := (hw i).2.2.2
    rw [heval (n+1) (by omega),pow_succ (-1:ℝ) (i.val+1)] at hs
    have hr : (-1:ℝ)^(i.val+1)*(-1)*((-u i)*Q.eval (-u i)) =
        u i*((-1:ℝ)^(i.val+1)*Q.eval (-u i)) := by ring
    rw [hr] at hs
    exact pos_of_mul_pos_right hs (hw i).1.le
  have hrP := original_divX_reciprocity (n := n) hk (by omega)
  have hrQ := original_divX_reciprocity (n := n+1) hk (by omega)
  have hd : n+1-2 = (n-2)+1 := by omega
  rw [hd] at hrQ
  obtain ⟨l,r,hpos,ho,hold,hs,hs'⟩ := mixed_witnesses_of_reciprocal_half
    hrP hrQ u u (fun i => (hw i).1) (fun i => (hw i).2.1) (fun _ _ hij => hmono hij)
    (fun i => Or.inl ⟨rfl,root i⟩) nextSign nextSign (original_next_center_sign hk hkn)
  obtain ⟨hp,mp,_⟩ := original_divX_shape hk hkn
  obtain ⟨hq,mq,hq0⟩ := original_divX_shape hk (by omega : k ≤ n+1)
  rw [hd] at hq
  have hq₀ : 0 < Q.eval 0 := by change 0 < (enumerator (n+1) k).divX.eval 0; rw [hq0]; norm_num
  have hlead : 0 < Q.leadingCoeff := by change 0 < (enumerator (n+1) k).divX.leadingCoeff; rw [mq.leadingCoeff]; norm_num
  obtain ⟨a,b,ha,hb,hbetween⟩ := interlace_of_mixed_root_witnesses
    l r mp.ne_zero hp hq hq₀ hlead hpos ho hold hs hs'
  have hbetween' (i) := And.intro ((hbetween i).1.trans_le (hbetween i).2.1)
    ((hbetween i).2.2.1.trans_lt (hbetween i).2.2.2)
  exact ⟨strict_of_complete_moduli mp.ne_zero mq.ne_zero ha hb hbetween',
    original_weak_of_complete_moduli hk hkn ha hb hbetween'⟩

#print axioms original_interlacing_of_literal_half_roots
end RepositoryQuotientAudit
