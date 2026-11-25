From Stdlib Require Import ZArith List Lia Ring.
From OpenMath Require Import BoundedCompositions.
Import ListNotations.
Open Scope Z_scope.

(* The scaled binomial-basis Ehrhart expansion. *)
Fixpoint combination (d:nat) (cs:list Z) (x:Z) : Z :=
 match cs with []=>0 | c::rest=>c*trunc d x + combination d rest (x-1) end.

Definition mass (x:Z) : Z := if x =? 0 then 1 else 0.
Fixpoint coefficient (cs:list Z) (x:Z) : Z :=
 match cs with []=>0|c::tail=>c*mass x + coefficient tail (x-1) end.
Definition backward (f:Z->Z) (x:Z) := f x - f(x-1).
Fixpoint diff (k:nat) (f:Z->Z) : Z->Z :=
 match k with O=>f | S n=>backward (diff n f) end.

Lemma diff_ext k f g : (forall x, f x=g x) -> forall x, diff k f x=diff k g x.
Proof. intro H. induction k; intro x; cbn [diff]; [apply H|unfold backward; rewrite !IHk; reflexivity]. Qed.
Lemma diff_add k f g x : diff k (fun y=>f y+g y) x=diff k f x+diff k g x.
Proof. revert x; induction k; intro x; cbn [diff]; [reflexivity|unfold backward; rewrite !IHk; ring]. Qed.
Lemma diff_scale k c f x : diff k (fun y=>c*f y) x=c*diff k f x.
Proof. revert x; induction k; intro x; cbn [diff]; [reflexivity|unfold backward; rewrite !IHk; ring]. Qed.
Lemma diff_shift k f h x : diff k (fun y=>f(y-h)) x=diff k f (x-h).
Proof. revert x; induction k; intro x; cbn [diff]; [reflexivity|unfold backward; rewrite !IHk; f_equal; f_equal; lia]. Qed.
Lemma diff_succ k f x : diff (S k) f x=diff k (backward f) x.
Proof. revert x; induction k; intro x; [reflexivity|change (backward (diff (S k) f) x=backward (diff k (backward f)) x); unfold backward at 1 2; rewrite !IHk; reflexivity]. Qed.
Lemma diff_trunc d x : diff (S d) (trunc d) x=fac d * mass x.
Proof.
 revert x; induction d as [|d IH]; intro x.
 - cbn [diff fac]; unfold backward, trunc, mass; cbn [rise]. destruct (x <? 0) eqn:E, (x-1 <? 0) eqn:F, (x =? 0) eqn:G;
    try reflexivity; first [apply Z.ltb_lt in E| apply Z.ltb_ge in E];
    first [apply Z.ltb_lt in F| apply Z.ltb_ge in F];first [apply Z.eqb_eq in G|apply Z.eqb_neq in G]; lia.
 - rewrite diff_succ. transitivity (diff (S d) (fun y=>Z.of_nat (S d)*trunc d y) x).
   + apply diff_ext, trunc_step.
   + rewrite diff_scale, IH. cbn [fac]; ring.
Qed.
Lemma diff_zero k x : diff k (fun _=>0) x=0.
Proof. revert x; induction k; intro x; cbn [diff]; [reflexivity|unfold backward; rewrite !IHk; reflexivity]. Qed.
Lemma diff_combination d cs x : diff (S d) (combination d cs) x=fac d * coefficient cs x.
Proof.
 revert x; induction cs as [|c cs IH]; intro x.
 - change (diff (S d) (fun _=>0) x=fac d*0). rewrite diff_zero; ring.
 - change (diff (S d) (fun y=> c*trunc d y+combination d cs (y-1)) x = fac d*(c*mass x+coefficient cs(x-1))).
   rewrite diff_add, diff_scale, diff_shift, diff_trunc, IH. ring.
Qed.

Lemma combination_negative d cs x : x<0 -> combination d cs x=0.
Proof. revert x; induction cs; intros x H; cbn [combination]; [reflexivity|].
 rewrite trunc_negative by lia. rewrite IHcs by lia. ring.
Qed.

(* The lattice-point series, extended by zero at negative dilation indices. *)
Definition series (level:Z) (bounds:nat->list nat) (z:Z) :=
 if z <? 0 then 0 else Z.of_nat (length (points (bounds (Z.to_nat z)) (level*z))).
Definition numerator (order:nat) (level:Z) (bounds:nat->list nat) (h:list Z) :=
 forall k, diff order (series level bounds) k=coefficient h k.

Lemma normalize_counts d level bounds p :
 (forall t, fac d * latticeCount (bounds t) (level*Z.of_nat t)=combination d p (Z.of_nat t)) ->
 numerator (S d) level bounds p.
Proof.
 intro H. assert (Hfac : 0 < fac d) by (clear; induction d; cbn [fac]; [lia|apply Z.mul_pos_pos; lia]).
 assert (E:forall z, fac d * series level bounds z=combination d p z).
 { intro z; unfold series; destruct (z <? 0) eqn:F.
   - rewrite combination_negative by (apply Z.ltb_lt; exact F). ring.
   - apply Z.ltb_ge in F. rewrite point_count. specialize (H (Z.to_nat z)).
     rewrite Z2Nat.id in H by exact F. exact H. }
 intro k. pose proof (diff_ext (S d) _ _ E k) as Eq.
 rewrite diff_scale, diff_combination in Eq. nia.
Qed.
Lemma coefficient_negative cs x : x<0 -> coefficient cs x=0.
Proof. revert x; induction cs; intros x H; cbn [coefficient]; [reflexivity|].
 unfold mass. rewrite (proj2 (Z.eqb_neq _ _) (Z.lt_neq _ _ H)), IHcs by lia. ring.
Qed.
Lemma coefficient_head c cs : coefficient (c::cs) 0=c.
Proof. cbn [coefficient]. rewrite coefficient_negative by lia. change (c*1+0=c); ring. Qed.
Lemma coefficient_tail c cs k : 0<=k -> coefficient (c::cs) (k+1)=coefficient cs k.
Proof. intro H; cbn [coefficient]; unfold mass.
 rewrite (proj2 (Z.eqb_neq (k+1) 0) ltac:(lia)). replace (k+1-1) with k by lia. ring. Qed.

Fixpoint plusPoly (a b:list Z) : list Z :=
 match a,b with [],_=>b|_,[]=>a|u::us,v::vs=>(u+v)::plusPoly us vs end.
Definition timesOneMinus (a:list Z) := plusPoly a (0 :: map Z.opp a).
Lemma coefficient_plus a b x : coefficient (plusPoly a b) x=coefficient a x+coefficient b x.
Proof. revert b x; induction a; intros [|b bs] x; cbn [plusPoly coefficient]; try ring. rewrite IHa; ring. Qed.
Lemma coefficient_opp a x : coefficient (map Z.opp a) x= -coefficient a x.
Proof. revert x; induction a; intro x; cbn [map coefficient]; [ring|rewrite IHa; ring]. Qed.
Lemma coefficient_times a x : coefficient (timesOneMinus a) x=backward (coefficient a) x.
Proof. unfold timesOneMinus,backward. rewrite coefficient_plus. cbn [coefficient]. rewrite coefficient_opp. ring. Qed.

Fixpoint factors (n:nat) (a:list Z) :=
 match n with O=>a|S k=>timesOneMinus (factors k a) end.
Lemma coefficient_factors n a x : coefficient (factors n a) x = diff n (coefficient a) x.
Proof. revert x; induction n; intro x; cbn [factors diff]; [reflexivity|rewrite coefficient_times; unfold backward;rewrite !IHn;reflexivity]. Qed.
Lemma diff_comp i j f x : diff i (diff j f) x=diff (i+j) f x.
Proof. revert x; induction i; intro x; [reflexivity|cbn [Nat.add diff]; unfold backward; rewrite !IHi; reflexivity]. Qed.
Lemma numerator_cross i j level b p q : numerator i level b p -> numerator j level b q -> forall x,
 coefficient (factors j p) x=coefficient (factors i q) x.
Proof.
 intros H G x. rewrite !coefficient_factors.
 transitivity (diff (j+i) (series level b) x).
 - rewrite <- diff_comp. apply diff_ext. intro y; symmetry; apply H.
 - rewrite Nat.add_comm, <-diff_comp. apply diff_ext, G.
Qed.
