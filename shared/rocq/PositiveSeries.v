(* A finite summation-by-parts proof of positivity on (0,1). Beyond a
   common cutoff the lower differences are nonnegative, so truncation
   leaves boundary terms of the required sign. *)
From Stdlib Require Import ZArith List Lia Ring Reals Lra Psatz Classical.
From OpenMath Require Import BoundedCompositions FiniteDifferences PolynomialSeparation BoxReflection NumeratorTable.
Import ListNotations.
Open Scope Z_scope.

Definition eventually (p:Z->Prop) := exists N, forall x, N<=x -> p x.
Definition stable_sign (f:Z->Z) :=
 eventually (fun x=>0<=f x) \/ eventually (fun x=>f x<0).

Lemma advance_bound f a c : (forall x,a<x -> c<=backward f x) ->
 forall x,a<=x -> f a+(x-a)*c<=f x.
Proof.
 intros H x T. set (n:=Z.to_nat (x-a)).
 assert (I:forall m:nat,f a+Z.of_nat m*c<=f(a+Z.of_nat m)).
 { induction m;[change (Z.of_nat O) with 0; replace (a+0) with a by ring;rewrite Z.mul_0_l;lia|].
   pose proof (H (a+Z.of_nat (S m)) ltac:(lia)) as Hm. unfold backward in Hm.
   replace (a+Z.of_nat (S m)-1) with (a+Z.of_nat m) in Hm by lia.
   rewrite Nat2Z.inj_succ in *;nia. }
 specialize (I n). unfold n in I;rewrite Z2Nat.id in I by lia.
 replace (a+(x-a)) with x in I by ring;exact I.
Qed.
Lemma descent_negative f : eventually (fun x=>backward f x<0) -> eventually (fun x=>f x<0).
Proof.
 intros [N H]. pose proof (Z.abs_nonneg (f N)). assert (A0:f N <= Z.abs(f N)) by (destruct (Z.abs_spec (f N));lia). exists (N+Z.abs(f N)+1);intros y T.
 assert (A: f y <= f N-(y-N)).
 { pose proof (advance_bound (fun x=> -f x) N 1) as B.
   assert (K:forall x,N<x -> 1<=backward (fun z=> -f z) x).
   { intros x L;specialize (H x ltac:(lia));unfold backward in *;lia. }
   specialize (B K y ltac:(lia));cbn beta in B;lia. }
 lia.
Qed.
Lemma stable_down f : stable_sign (backward f) -> stable_sign f.
Proof.
 intros [[N H]|H];[|right;apply descent_negative,H].
 destruct (classic (exists y, N<=y /\ 0<=f y)) as [[y [Y V]]|E].
 - left;exists y;intros z T. pose proof (advance_bound f y 0 (fun x Hx=>H x ltac:(lia)) z T);lia.
 - right;exists N;intros z T. destruct (Z_lt_ge_dec (f z) 0);[assumption|exfalso;apply E;exists z;lia].
Qed.
Lemma stable_lower n f : stable_sign (diff n f) -> stable_sign f.
Proof. induction n;intro H;[exact H|apply IHn,stable_down;exact H]. Qed.
Lemma negative_lower n f : eventually (fun x=>diff n f x<0) -> eventually (fun x=>f x<0).
Proof. induction n;intro H;[exact H|apply IHn,descent_negative;exact H]. Qed.
Lemma eventual_jets f s : (forall x,0<=f x) -> eventually (fun x=>diff s f x=0) ->
 eventually (fun x=>forall j, (j<=s)%nat -> 0<=diff j f x).
Proof.
 intros F [N H]. assert (J:forall j,(j<=s)%nat -> eventually (fun x=>0<=diff j f x)).
 { intros j T. assert (S:stable_sign (diff j f)).
   { apply (stable_lower (s-j)). left;exists N;intros x X. rewrite diff_comp.
     replace (s-j+j)%nat with s by lia;rewrite H by lia;lia. }
   destruct S as [P|G];[exact P|]. apply negative_lower in G. destruct G as [y E].
   specialize (E y ltac:(lia));specialize (F y);lia. }
 assert (M:forall r,(r<=s)%nat -> eventually (fun x=>forall j,(j<=r)%nat ->0<=diff j f x)).
 { induction r;intro K.
   - exists 0;intros x _ j T;replace j with O by lia;apply F.
   - destruct (IHr ltac:(lia)) as [A HA];destruct (J (S r) K) as [B HB].
     exists (Z.max A B);intros x X j T. destruct (Nat.eq_dec j (S r));[subst;apply HB;lia|apply HA;lia]. }
 apply M;lia.
Qed.

Open Scope R_scope.
Fixpoint subtotal (n:nat) (f:Z->Z) (x:R) : R :=
 match n with O=>0 | S m=>subtotal m f x+IZR (f(Z.of_nat m))*x^m end.
Lemma subtotal_back n f x : f (-1)%Z=0%Z ->
 subtotal n (backward f) x=(1-x)*subtotal n f x+x^n*IZR(f(Z.of_nat n-1)%Z).
Proof.
 intro H;induction n.
 - change (0=(1-x)*0+1*IZR(f (-1)%Z)). rewrite H;ring.
 - cbn [subtotal];rewrite IHn. unfold backward;rewrite minus_IZR,Nat2Z.inj_succ;cbn [pow].
   replace (Z.succ (Z.of_nat n)-1)%Z with (Z.of_nat n) by lia. ring.
Qed.
Lemma value_append a b x : value (a++b) x=value a x+x^(length a)*value b x.
Proof. induction a;cbn [app value length pow];[ring|rewrite IHa;ring]. Qed.
Lemma table_subtotal n f x : value (table n f 0) x=subtotal n f x.
Proof.
 induction n;[reflexivity|]. rewrite table_end,value_append,table_length,IHn.
 cbn [subtotal value];rewrite Z.add_0_l;ring.
Qed.
Lemma subtotal_pos n f x : 0<x -> (forall z,(0<=f z)%Z) -> (0<f 0%Z)%Z -> 0<subtotal (S n) f x.
Proof.
 intros X F H;induction n.
 - change (0<0+IZR(f 0%Z)*1). apply IZR_lt in H;lra.
 - change (0<subtotal (S n) f x+IZR(f (Z.of_nat(S n)))*x^(S n)).
   apply Rplus_lt_le_0_compat;[exact IHn|apply Rmult_le_pos;[apply IZR_le,F|apply pow_le;lra]].
Qed.

Theorem positive_numerator_at_fraction s f p x :
 (forall z,(0<=f z)%Z) -> (forall z,(z<0)%Z -> f z=0%Z) -> (0<f 0%Z)%Z ->
 (forall z,diff s f z=coefficient p z) -> 0<x<1 -> 0<value p x.
Proof.
 intros F Neg H Poly X. assert (Zr:eventually (fun z=>diff s f z=0%Z)).
 { exists (Z.of_nat (length p));intros;rewrite Poly;apply coefficient_above;lia. }
 destruct (eventual_jets f s F Zr) as [N Bound].
 set (n:=Z.to_nat (Z.max N (Z.of_nat (length p)))).
 assert (Nn:(N<=Z.of_nat n /\ Z.of_nat(length p)<=Z.of_nat n)%Z)
   by (unfold n;rewrite Z2Nat.id;lia).
 assert (P:forall j,(j<=s)%nat ->0<subtotal (S n) (diff j f) x).
 { induction j;intro J;[apply subtotal_pos;auto;lra|].
   change (0<subtotal (S n) (backward (diff j f)) x).
   rewrite subtotal_back by (apply (diff_below _ _ 0 Neg);lia).
   replace (Z.of_nat(S n)-1)%Z with (Z.of_nat n) by lia.
   apply Rplus_lt_le_0_compat.
   - apply Rmult_lt_0_compat;[lra|apply IHj;lia].
   - apply Rmult_le_pos;[apply pow_le;lra|apply IZR_le,Bound;lia]. }
 assert (Tab:forall j z, value (table j (coefficient p) z) x=
                          value (table j (diff s f) z) x).
 { intros j;induction j;intros z;cbn [table value];[reflexivity|rewrite Poly,IHj;reflexivity]. }
 assert (E:value p x=value (table (S n) (coefficient p) 0) x).
 { apply value_ext;intros k K. destruct (Z_lt_ge_dec k (Z.of_nat (S n))).
   - rewrite table_at by lia;reflexivity.
   - rewrite !coefficient_above;try rewrite table_length;lia. }
 rewrite E,Tab,table_subtotal. apply P;lia.
Qed.
