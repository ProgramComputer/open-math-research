(* A coefficient table represents every coefficient, including zeros
   outside its support. Reflection reads the top two entries from strict
   interior counts at dilations two and three. *)
From Stdlib Require Import List ZArith Lia Ring.
From OpenMath Require Import BoundedCompositions FiniteDifferences BoxReflection.
Import ListNotations.
Open Scope Z_scope.

Fixpoint table (n:nat) (f:Z->Z) (i:Z) : list Z :=
 match n with O => [] | S m=>f i::table m f (i+1) end.
Lemma table_length n f i : length (table n f i)=n.
Proof. revert i;induction n;intro;cbn;auto. Qed.
Lemma table_at n f i x : 0<=x<Z.of_nat n -> coefficient (table n f i) x=f(i+x).
Proof.
 revert i x;induction n;intros i x H;[lia|].
 cbn [table]. destruct (Z.eq_dec x 0) as [->|E];[rewrite coefficient_head,Z.add_0_r;reflexivity|].
 replace x with ((x-1)+1) at 1 by ring. rewrite coefficient_tail by lia. rewrite IHn by lia.
 f_equal;ring.
Qed.
Lemma coefficient_above cs x : Z.of_nat (length cs)<=x -> coefficient cs x=0.
Proof. revert x;induction cs;intros x H;[reflexivity|]. cbn [length] in H.
 replace x with ((x-1)+1) by ring. rewrite coefficient_tail by lia. apply IHcs;lia.
Qed.
Lemma table_num n f : (forall x, x<0 \/ Z.of_nat n<=x -> f x=0) ->
 forall x, coefficient (table n f 0) x=f x.
Proof. intros H x;destruct (Z_lt_ge_dec x 0).
 - rewrite coefficient_negative,H by (intuition lia);reflexivity.
 - destruct (Z_lt_ge_dec x (Z.of_nat n)).
   + rewrite table_at by lia. ring_simplify (0+x);reflexivity.
   + rewrite coefficient_above by (rewrite table_length;lia). symmetry;apply H;lia.
Qed.
Lemma table_end n f i : table (S n) f i=table n f i++[f(i+Z.of_nat n)].
Proof. revert i;induction n;intro i;[cbn [table app];replace (i+Z.of_nat 0) with i by ring;reflexivity|].
 change (f i::table (S n) f (i+1)=f i::(table n f(i+1)++[f(i+Z.of_nat (S n))])).
 rewrite IHn; replace (i+1+Z.of_nat n) with (i+Z.of_nat (S n)) by lia; reflexivity.
Qed.
Lemma rev_table n f a b g : (forall j, 0<=j<Z.of_nat n -> f (a+j)=g (b+Z.of_nat n-1-j)) ->
 rev (table n f a)=table n g b.
Proof.
 revert a b;induction n;intros a b H;[reflexivity|].
 change (rev (table n f (a+1))++[f a]=table (S n) g b). rewrite (table_end n g b).
 change (rev (table n f(a+1))++[f a]=table n g b++[g(b+Z.of_nat n)]).
 rewrite (IHn (a+1) b).
 - f_equal;f_equal. specialize (H 0 ltac:(lia)). replace (a+0) with a in H by ring.
   replace (b+Z.of_nat (S n)-1-0) with (b+Z.of_nat n) in H by lia. exact H.
 - intros j J. specialize (H (j+1) ltac:(lia)).
   replace (a+1+j) with (a+(j+1)) by ring. rewrite H. f_equal;lia.
Qed.
Definition hcoeff cs k x := diff (length cs) (series k (scaled cs)) x.
Definition hlist cs k := table (length cs-1) (hcoeff cs k) 0.
Lemma interior_below cs k x : x<2 -> interior cs k x=0.
Proof. intro H;unfold interior;rewrite (proj2 (Z.ltb_lt _ _) H);reflexivity. Qed.
Lemma hcoeff_support cs k d : length cs=S d -> admissCaps cs -> 0<k<total cs -> k<boxSize cs ->
 forall x, x<0 \/ Z.of_nat d<=x -> hcoeff cs k x=0.
Proof.
 intros D H K B x [T|T];unfold hcoeff;rewrite D.
 - apply (diff_below _ _ 0);[intros y Y;unfold series;rewrite (proj2 (Z.ltb_lt _ _) Y);reflexivity|lia].
 - rewrite (numerator_reversal cs k d D H K B). apply (diff_below _ _ 2);[apply interior_below|lia].
Qed.
Lemma hlist_full cs k d : length cs=S d -> admissCaps cs -> 0<k<total cs -> k<boxSize cs ->
 numerator (S d) k (scaled cs) (hlist cs k).
Proof.
 intros D H K B x. unfold hlist;rewrite table_num.
 - unfold hcoeff;now rewrite D.
 - rewrite D;replace (S d-1)%nat with d by lia;apply hcoeff_support;assumption.
Qed.
Lemma hlist_top cs k n : length cs=S(S(S n)) -> admissCaps cs -> 0<k<total cs ->
 k<boxSize cs -> interior cs k 2=1 ->
 exists tail, length tail=n /\ rev (hlist cs k)=
  1::(interior cs k 3-Z.of_nat (length cs))::tail.
Proof.
 intros D H K B I. set (g:=fun y=>diff (length cs) (interior cs k) (y+2)).
 assert (R:rev(hlist cs k)=table (S(S n)) g 0).
 { unfold hlist. rewrite D. replace (S(S(S n))-1)%nat with (S(S n)) by lia.
   apply rev_table. intros j J;unfold hcoeff,g;rewrite D.
   rewrite (numerator_reversal cs k (S(S n)) D H K B). f_equal;lia. }
 rewrite R. exists (table n g 2);split;[apply table_length|].
 cbn [table]. pose proof (diff_first (length cs) (interior cs k) 2 (interior_below cs k)) as [A C].
 unfold g. change (0+2) with 2;change (0+1+2) with (2+1);change (0+1+1) with 2.
 rewrite A,C,I. change (2+1) with 3. rewrite Z.mul_1_r;reflexivity.
Qed.
