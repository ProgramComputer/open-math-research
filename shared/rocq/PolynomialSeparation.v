From Stdlib Require Import Reals ZArith List Lia Lra Psatz Ring.
From OpenMath Require Import FiniteDifferences.
Import ListNotations.
Open Scope R_scope.

Fixpoint value (cs:list Z) (x:R) : R :=
 match cs with []=>0|c::tail=>IZR c + x*value tail x end.

Lemma value_zero cs : (forall k, (0<=k)%Z -> coefficient cs k=0%Z) ->
 forall x, value cs x=0.
Proof.
 induction cs as [|c cs IH]; intros H x; cbn [value]; [reflexivity|].
 assert (Hc:c=0%Z) by (rewrite <- (coefficient_head c cs); apply H; lia).
 subst. rewrite IH; [ring|]. intros k Hk. rewrite <- (coefficient_tail 0 cs k Hk). apply H; lia.
Qed.
Lemma value_ext a b : (forall k, (0<=k)%Z -> coefficient a k=coefficient b k) ->
 forall x, value a x=value b x.
Proof.
 revert b; induction a as [|c a IH]; intros [|e b] H x.
 - reflexivity.
 - symmetry. apply value_zero. intros k Hk; symmetry; apply H,Hk.
 - apply value_zero. intros k Hk; apply H,Hk.
 - assert (H0:=H 0%Z ltac:(lia)). rewrite !coefficient_head in H0. subst e.
   cbn [value]. rewrite (IH b); [reflexivity|]. intros k Hk.
   specialize (H (k+1)%Z ltac:(lia)). now rewrite !coefficient_tail in H by lia.
Qed.
Lemma value_plus a b x : value (plusPoly a b) x=value a x+value b x.
Proof. revert b; induction a; intros [|b bs]; cbn [value plusPoly]; try ring. rewrite IHa, plus_IZR; ring. Qed.
Lemma value_opp a x : value (map Z.opp a) x= -value a x.
Proof. induction a; cbn [map value]; [ring|rewrite IHa,opp_IZR;ring]. Qed.
Lemma value_factors n a x : value (factors n a) x=(1-x)^n *value a x.
Proof. induction n; cbn [factors pow]; [ring|]. unfold timesOneMinus. rewrite value_plus. cbn [value]. rewrite value_opp, IHn. ring. Qed.
Lemma same_negative_zeros i j level b a c x : numerator i level b a -> numerator j level b c -> x<0 ->
 (value a x=0 <-> value c x=0).
Proof.
 intros Ha Hc Hx. pose proof (value_ext (factors j a) (factors i c)
   (fun k _=>numerator_cross i j level b a c Ha Hc k) x) as E.
 rewrite !value_factors in E. assert (A:0<(1-x)^i) by (apply pow_lt; lra).
 assert (B:0<(1-x)^j) by (apply pow_lt; lra). split; intro Hz;
 rewrite Hz in E; nra.
Qed.

Lemma continuous_value cs x : continuity_pt (value cs) x.
Proof.
 induction cs as [|c cs IH].
 - apply continuity_pt_const; intros y z; reflexivity.
 - change (continuity_pt (plus_fct (fun _=>IZR c) (mult_fct id (value cs))) x).
   apply continuity_pt_plus; [apply continuity_pt_const; intros y z; reflexivity|].
   apply continuity_pt_mult; [apply derivable_continuous_pt, derivable_pt_id|assumption].
Qed.

(* A weak alternation may start with either polynomial and may have ties. *)
Inductive weave : list R -> list R -> Prop :=
| weave_empty : weave [] []
| weave_head : forall x xs ys, (forall y, In y ys -> x<=y) ->
    weave ys xs -> weave (x::xs) ys.
Definition separates (xs ys:list R) := forall a b, In a xs -> In b xs -> a<b ->
 exists y, In y ys /\ a<=y<=b.
Lemma bridge x xs ys : (forall y, In y ys -> x<=y) -> weave ys xs ->
 forall b, In b xs -> exists y, In y ys /\ x<=y<=b.
Proof.
 intros H W. destruct W as [|y rest tail Hy W]; intros b Hb; [contradiction|].
 exists y. split; [left;reflexivity|]. split; [apply H;left;reflexivity|now apply Hy].
Qed.
Lemma weave_separates xs ys : weave xs ys -> separates xs ys /\ separates ys xs.
Proof.
 induction 1 as [|x xs ys H W [IH J]]; [split;intros a b H0; contradiction|].
 split.
 - intros a b [E|Ha] [F|Hb] Hab.
   + subst; lra.
   + subst a; exact (bridge x xs ys H W b Hb).
   + subst b. destruct (bridge x xs ys H W a Ha) as [z [_ Hz]]. lra.
   + exact (J a b Ha Hb Hab).
 - intros a b Ha Hb Hab. destruct (IH a b Ha Hb Hab) as [z [Hz E]].
   exists z. split; [right;exact Hz|exact E].
Qed.

Definition interlace (p q:list Z) := exists xs ys:list R,
 (forall z, In z xs <-> value p z=0) /\ (forall z, In z ys <-> value q z=0) /\
 (weave xs ys \/ weave ys xs).
