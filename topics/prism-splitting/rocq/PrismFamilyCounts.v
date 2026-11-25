(* Family-specific lattice counts. The Pascal recurrence for unit boxes
   gives the two consecutive-coefficient ratios needed for the strict
   gap. *)
From Stdlib Require Import List ZArith Lia Ring.
From OpenMath Require Import BoundedCompositions FiniteDifferences BoxReflection.
Import ListNotations.
Open Scope Z_scope.

Definition before (b:nat) := repeat 1%nat (2*b) ++ [2%nat].
Definition after (b:nat) := repeat 1%nat (2*b+2).
Definition level (b:nat) := Z.of_nat b+1.
Definition units (n:nat) (k:Z) := latticeCount (repeat 1%nat n) k.

Lemma win_comm a b f x : window a (window b f) x=window b (window a f) x.
Proof.
 revert x;induction a;intro x;[reflexivity|].
 change (window a (window b f) x + window b f (x-Z.of_nat (S a)) = window b (window (S a) f) x). rewrite IHa.
 change (window b (window a f) x+window b f (x-Z.of_nat (S a))=
  window b (fun y=>window a f y+f(y-Z.of_nat (S a))) x).
 rewrite <-(window_shift b f (Z.of_nat (S a)) x).
 assert (L:forall (g h:Z->Z) z, window b g z+window b h z=window b (fun y=>g y+h y) z).
 { clear - b. induction b;intros;cbn [window];[reflexivity|rewrite <-IHb;ring]. }
 apply L.
Qed.
Lemma append_cap cs c x : latticeCount (cs++[c]) x=window c (latticeCount cs) x.
Proof.
 revert x;induction cs;intro x;[reflexivity|]. cbn [app latticeCount].
 transitivity (window a (window c (latticeCount cs)) x);[apply window_ext,IHcs|apply win_comm].
Qed.
Lemma zero_units n x : latticeCount (repeat 0%nat n) x=mass x.
Proof. induction n;[reflexivity|exact IHn]. Qed.
Lemma units_S n x : units (S n) x=units n x+units n(x-1).
Proof. reflexivity. Qed.
Lemma unit_positive n x : 0<=x<=Z.of_nat n -> 0<units n x.
Proof.
 assert (NN:forall m z,0<=units m z) by (intros;unfold units;rewrite <-point_count;lia).
 revert x;induction n;intros x H.
 - replace x with 0 by lia;reflexivity.
 - rewrite units_S. destruct (Z.eq_dec x 0) as [->|E].
   + specialize (IHn 0 ltac:(lia));pose proof (NN n (0-1));lia.
   + specialize (IHn (x-1) ltac:(lia));pose proof (NN n x);lia.
Qed.
Lemma units_ratio n x : x*units n x=(Z.of_nat n-x+1)*units n(x-1).
Proof.
 revert x;induction n;intro x.
 - change (x*mass x=(0-x+1)*mass (x-1)). unfold mass.
   destruct (x=?0) eqn:E,(x-1=?0) eqn:F;
   first [apply Z.eqb_eq in E|apply Z.eqb_neq in E];first [apply Z.eqb_eq in F|apply Z.eqb_neq in F];nia.
 - rewrite !units_S,Nat2Z.inj_succ. pose proof (IHn x);pose proof (IHn (x-1));nia.
Qed.

Lemma size_repeat n c : total (repeat c n)=Z.of_nat n*Z.of_nat c.
Proof. induction n;cbn [repeat total];[ring|rewrite IHn,Nat2Z.inj_succ;ring]. Qed.
Lemma total_app a b : total(a++b)=total a+total b.
Proof. induction a;cbn [app total];[ring|rewrite IHa;ring]. Qed.
Lemma ones_ok n : admissCaps (repeat 1%nat n).
Proof. induction n;constructor;auto;lia. Qed.
Lemma before_data b : (1<=b)%nat ->
 length (before b)=S (2*b) /\ admissCaps (before b) /\
 0<level b<total (before b) /\ level b<boxSize (before b).
Proof.
 intro H;unfold before,level,boxSize. rewrite length_app,repeat_length,total_app,size_repeat.
 cbn [length total];rewrite Nat2Z.inj_mul,Nat2Z.inj_add.
 split;[lia|]. split;[apply Forall_app;split;[apply ones_ok|repeat constructor;lia]|lia].
Qed.
Lemma after_data b : (1<=b)%nat ->
 length (after b)=S (2*b+1) /\ admissCaps (after b) /\
 0<level b<total (after b) /\ level b<boxSize (after b).
Proof.
 intro H;unfold after,level,boxSize. rewrite repeat_length,size_repeat,Nat2Z.inj_add,Nat2Z.inj_mul.
 split;[lia|]. split;[apply ones_ok|lia].
Qed.
Lemma map_rep {A B} (f:A->B) c n : map f (repeat c n)=repeat (f c) n.
Proof. induction n;cbn;congruence. Qed.

Lemma before_two b : interior (before b) (level b) 2=1.
Proof.
 unfold interior,before,level,innerCaps,boxSize. rewrite map_app,map_rep,length_app,repeat_length.
 change (latticeCount (repeat 0%nat (2*b)++[2%nat]) ((Z.of_nat b+1)*2-Z.of_nat(2*b+1))=1).
 rewrite append_cap,Nat2Z.inj_add,Nat2Z.inj_mul. change (Z.of_nat 2) with 2;change (Z.of_nat 1) with 1. replace ((Z.of_nat b+1)*2-(2*Z.of_nat b+1)) with 1 by ring.
 cbn [window];rewrite !zero_units;reflexivity.
Qed.
Lemma after_two b : interior (after b) (level b) 2=1.
Proof.
 unfold interior,after,level,innerCaps,boxSize. rewrite map_rep,repeat_length.
 change (latticeCount (repeat 0%nat (2*b+2)) ((Z.of_nat b+1)*2-Z.of_nat (2*b+2))=1).
 rewrite zero_units,Nat2Z.inj_add,Nat2Z.inj_mul. change (Z.of_nat 2) with 2. replace ((Z.of_nat b+1)*2-(2*Z.of_nat b+2)) with 0 by ring. reflexivity.
Qed.

Lemma before_three b : let k:=Z.of_nat b in let B:=units (2*b) in
 interior (before b) (level b) 3=B(k+2)+B(k+1)+B k+B(k-1)+B(k-2).
Proof.
 cbn zeta. unfold interior,before,level,innerCaps,boxSize. rewrite map_app,map_rep,length_app,repeat_length.
 change (latticeCount (repeat 1%nat (2*b)++[4%nat]) ((Z.of_nat b+1)*3-Z.of_nat(2*b+1))=
     units (2*b) (Z.of_nat b+2)+units (2*b) (Z.of_nat b+1)+units (2*b) (Z.of_nat b)+units (2*b)(Z.of_nat b-1)+units (2*b)(Z.of_nat b-2)).
 rewrite append_cap,Nat2Z.inj_add,Nat2Z.inj_mul. change (Z.of_nat 2) with 2;change (Z.of_nat 1) with 1. replace ((Z.of_nat b+1)*3-(2*Z.of_nat b+1)) with (Z.of_nat b+2) by ring.
 cbn [window];unfold units. change (Z.of_nat 1) with 1;change (Z.of_nat 2) with 2;change (Z.of_nat 3) with 3;change (Z.of_nat 4) with 4. replace (Z.of_nat b+2-1) with (Z.of_nat b+1) by ring. replace (Z.of_nat b+2-2) with (Z.of_nat b) by ring. replace (Z.of_nat b+2-3) with (Z.of_nat b-1) by ring. replace (Z.of_nat b+2-4) with (Z.of_nat b-2) by ring. reflexivity.
Qed.
Lemma after_three b : let k:=Z.of_nat b in let B:=units (2*b) in
 interior (after b) (level b) 3=B(k+1)+2*B k+B(k-1).
Proof.
 cbn zeta. unfold interior,after,level,innerCaps,boxSize. rewrite map_rep,repeat_length.
 change (units (2*b+2) ((Z.of_nat b+1)*3-Z.of_nat(2*b+2))=
  units (2*b) (Z.of_nat b+1)+2*units (2*b) (Z.of_nat b)+units (2*b)(Z.of_nat b-1)).
 rewrite Nat2Z.inj_add,Nat2Z.inj_mul. change (Z.of_nat 2) with 2. replace ((Z.of_nat b+1)*3-(2*Z.of_nat b+2)) with (Z.of_nat b+1) by ring.
 replace (2*b+2)%nat with (S(S (2*b))) by lia. rewrite !units_S.
 replace (Z.of_nat b+1-1) with (Z.of_nat b) by ring. ring.
Qed.

Theorem interior_gap b : (6<=b)%nat ->
 interior (after b) (level b) 3 < interior (before b) (level b) 3.
Proof.
 intro Hb;rewrite before_three,after_three;cbn zeta.
 set (k:=Z.of_nat b). set (B:=units (2*b)).
 assert (K:6<=k) by (unfold k;lia).
 assert (U:forall x,x*B x=(2*k-x+1)*B(x-1)).
 { intro x;unfold B,k;pose proof (units_ratio (2*b) x) as T;rewrite Nat2Z.inj_mul in T;exact T. }
 pose proof (U (k+2)) as U2;pose proof (U (k+1)) as U1;pose proof (U k) as V1;pose proof (U(k-1)) as V2.
 replace (k+2-1) with (k+1) in U2 by ring. replace (k+1-1) with k in U1 by ring.
 replace (k-1-1) with (k-2) in V2 by ring.
 assert (C:0<B k) by (apply unit_positive;unfold k;rewrite Nat2Z.inj_mul;lia).
 assert (E1:(k+1)*B(k+1)=k*B k) by nia.
 assert (E2:(k+2)*B(k+2)=(k-1)*B(k+1)) by nia.
 assert (E3:(k+1)*B(k-1)=k*B k) by nia.
 assert (E4:(k+2)*B(k-2)=(k-1)*B(k-1)) by nia.
 assert (Y:forall u v, (k+1)*v=k*B k -> (k+2)*u=(k-1)*v ->
       ((k+1)*(k+2))*u=(k-1)*k*B k).
 { intros u v E F. replace ((k+1)*(k+2)*u) with ((k+1)*((k+2)*u)) by ring.
   rewrite F. replace ((k+1)*((k-1)*v)) with ((k-1)*((k+1)*v)) by ring. rewrite E;ring. }
 pose proof (Y _ _ E1 E2) as L;pose proof (Y _ _ E3 E4) as M.
 assert (G:0<k*k-5*k-2) by nia.
 assert (W:0<(k*k-5*k-2)*B k) by (apply Z.mul_pos_pos;lia).
 assert (T: ((k+1)*(k+2))*(B(k+2)+B(k-2)-B k)=(k*k-5*k-2)*B k) by nia.
 assert (0<B(k+2)+B(k-2)-B k) by nia. lia.
Qed.
