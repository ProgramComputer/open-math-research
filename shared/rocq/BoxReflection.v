(* Integer reciprocity for slices with unit and double bounds. Shift
   every strict interior coordinate down by one, reflect the rising
   factorial, and then take the same finite difference on both sides. *)
From Stdlib Require Import ZArith List Lia Ring.
From OpenMath Require Import BoundedCompositions FiniteDifferences.
Import ListNotations.
Open Scope Z_scope.
Fixpoint alt (cs:list nat) (f:Z->Z->Z) (w e:Z) : Z :=
 match cs with []=>f w e | c::tail=>alt tail f w e-alt tail f (w+Z.of_nat c) (e+1) end.
Definition boxSize (cs:list nat) := Z.of_nat (length cs).
Definition admissCaps cs := Forall (fun c=>(1<=c<=2)%nat) cs.
Definition range cs w e :=
 0<=e<=boxSize cs /\ e<=w<=2*e /\ boxSize cs-e<=total cs-w<=2*(boxSize cs-e).
Lemma alt_congr cs f g : admissCaps cs -> forall w e,
 (forall v h, range cs v h -> f (w+v) (e+h)=g (w+v) (e+h)) ->
 alt cs f w e=alt cs g w e.
Proof.
 induction 1 as [|c cs Hc H IH]; intros w e E; cbn [alt].
 - specialize (E 0 0 ltac:(unfold range,boxSize;cbn;lia)). now rewrite !Z.add_0_r in E.
 - f_equal.
   + apply IH; intros v h T; apply E. unfold range,boxSize in *.
     cbn [length total]; rewrite Nat2Z.inj_succ; lia.
   + apply IH; intros v h T. replace (w+Z.of_nat c+v) with (w+(v+Z.of_nat c)) by ring.
     replace (e+1+h) with (e+(h+1)) by ring. apply E. unfold range,boxSize in *.
     cbn [length total]; rewrite Nat2Z.inj_succ; lia.
Qed.
Lemma alt_scale cs f u w e : alt cs (fun v h=>u*f v h) w e=u*alt cs f w e.
Proof. revert w e; induction cs;intros;cbn [alt];[reflexivity|rewrite !IHcs;ring]. Qed.
Definition scaled cs (t:nat) := map (fun c=>(t*c)%nat) cs.
Definition innerCaps cs (t:nat) := map (fun c=>(t*c-2)%nat) cs.
Lemma cut_outer cs t k d w e : cuts (scaled cs t) (trunc d) ((k-w)*Z.of_nat t-e)=
 alt cs (fun v h=>trunc d ((k-v)*Z.of_nat t-h)) w e.
Proof.
 revert w e;induction cs as [|c cs IH];intros;cbn [scaled map cuts alt];[reflexivity|].
 unfold scaled in IH. rewrite (IH w e),<-(IH (w+Z.of_nat c) (e+1)). f_equal. f_equal. rewrite Nat2Z.inj_mul;ring.
Qed.
Lemma cut_inner cs t k s d w e : admissCaps cs -> (2<=t)%nat ->
 cuts (innerCaps cs t) (trunc d) ((k-w)*Z.of_nat t+e-s)=
 alt cs (fun v h=>trunc d ((k-v)*Z.of_nat t+h-s)) w e.
Proof.
 intros H Ht;revert w e;induction H as [|c cs Hc H IH];intros;cbn [innerCaps map cuts alt];[reflexivity|].
 unfold innerCaps in IH. rewrite (IH w e),<-(IH (w+Z.of_nat c) (e+1)). f_equal. f_equal. rewrite Nat2Z.inj_sub by nia.
 rewrite Nat2Z.inj_mul;change (Z.of_nat 2) with 2;ring.
Qed.
Definition extension cs k d t :=
 alt cs (fun v h=>if v <? k then rise d ((k-v)*t-h) else 0) 0 0.
Lemma extension_outer cs k d t : length cs=S d -> admissCaps cs -> 0<k<total cs ->
 fac d*latticeCount (scaled cs t) (k*Z.of_nat t)=extension cs k d (Z.of_nat t).
Proof.
 intros D H K. rewrite bounded_count_formula by (unfold scaled;now rewrite length_map).
 replace (k*Z.of_nat t) with ((k-0)*Z.of_nat t-0) by ring. rewrite cut_outer.
 unfold extension;apply alt_congr;auto. intros v h T;unfold range,boxSize in T;rewrite D,Nat2Z.inj_succ in T.
 rewrite !Z.add_0_l. destruct (v <? k) eqn:E.
 - apply Z.ltb_lt in E. apply trunc_rise. nia.
 - apply Z.ltb_ge in E. apply trunc_negative. nia.
Qed.

Fixpoint parity (d:nat) : Z := match d with O=>1|S m=> -parity m end.
Lemma parity_sq d : parity d*parity d=1.
Proof. induction d;cbn [parity];[ring|nia]. Qed.
Lemma rise_first d x : rise (S d) x=(x+1)*rise d (x+1).
Proof.
 revert x;induction d;intro x;[cbn [rise];ring|].
 change (rise (S d) x*(x+Z.of_nat (S (S d)))=(x+1)*(rise d (x+1)*(x+1+Z.of_nat (S d)))).
 rewrite IHd,Nat2Z.inj_succ. ring.
Qed.
Lemma rise_reflect d x : rise d (-x)=parity d*rise d (x-Z.of_nat d-1).
Proof.
 revert x;induction d;intro x;[reflexivity|].
 change (rise d (-x)*(-x+Z.of_nat (S d))= - parity d*rise (S d) (x-Z.of_nat (S d)-1)).
 rewrite IHd,rise_first,Nat2Z.inj_succ.
 replace (x-Z.succ (Z.of_nat d)-1+1) with (x-Z.of_nat d-1) by lia.
 ring.
Qed.
Lemma reflection cs k d t : length cs=S d -> admissCaps cs -> 0<k<total cs -> (0<t)%nat ->
 parity d*extension cs k d (-Z.of_nat t)=
 alt cs (fun v h=>trunc d ((k-v)*Z.of_nat t+h-Z.of_nat (S d))) 0 0.
Proof.
 intros D H K T. unfold extension;rewrite <-alt_scale. apply alt_congr;auto.
 intros v h R. rewrite !Z.add_0_l. unfold range,boxSize in R;rewrite D,Nat2Z.inj_succ in R.
 destruct (v <? k) eqn:E.
 - apply Z.ltb_lt in E. rewrite trunc_rise by (rewrite Nat2Z.inj_succ;nia).
   replace ((k-v)* - Z.of_nat t-h) with (-((k-v)*Z.of_nat t+h)) by ring.
   rewrite rise_reflect,Z.mul_assoc,parity_sq,Z.mul_1_l.
   rewrite Nat2Z.inj_succ. replace ((k-v)*Z.of_nat t+h-Z.of_nat d-1) with ((k-v)*Z.of_nat t+h-Z.succ (Z.of_nat d)) by lia. ring.
 - apply Z.ltb_ge in E. rewrite trunc_negative by (rewrite Nat2Z.inj_succ;nia). ring.
Qed.
Lemma reflection_inner cs k d t : length cs=S d -> admissCaps cs -> 0<k<total cs -> (2<=t)%nat ->
 parity d*extension cs k d (-Z.of_nat t)=fac d*latticeCount (innerCaps cs t) (k*Z.of_nat t-Z.of_nat (S d)).
Proof.
 intros D H K T. rewrite reflection by auto with arith.
 rewrite bounded_count_formula by (unfold innerCaps;now rewrite length_map).
 replace (k*Z.of_nat t-Z.of_nat (S d)) with ((k-0)*Z.of_nat t+0-Z.of_nat (S d)) by ring.
 symmetry;apply cut_inner;auto.
Qed.
Lemma alt_zero cs w e : alt cs (fun _ _=>0) w e=0.
Proof. revert w e;induction cs;intros;cbn [alt];[reflexivity|rewrite !IHcs;ring]. Qed.
Lemma reflection_one cs k d : length cs=S d -> admissCaps cs -> 0<k<total cs -> k<boxSize cs ->
 parity d*extension cs k d (-1)=0.
Proof.
 intros D H K B. change (-1) with (-Z.of_nat 1). rewrite reflection by auto with arith.
 transitivity (alt cs (fun _ _ => 0) 0 0); [|apply alt_zero]. apply alt_congr;auto.
 intros v h R;rewrite !Z.add_0_l;apply trunc_negative.
 unfold range,boxSize in *;rewrite D in B;change (Z.of_nat 1) with 1;lia.
Qed.

Lemma diff_sub n f g x : diff n (fun y=>f y-g y) x=diff n f x-diff n g x.
Proof. revert x;induction n;intro x;cbn [diff];[reflexivity|unfold backward;rewrite !IHn;ring]. Qed.
Lemma diff_affine n a b f x :
 diff (S n) (fun y=>(a*y+b)*f y) x =
 (a*x+b)*diff (S n) f x+Z.of_nat (S n)*a*diff n f (x-1).
Proof.
 revert x;induction n;intro x.
 - cbn [diff];unfold backward;change (Z.of_nat 1) with 1;ring.
 - change (diff (S n) (fun y=>(a*y+b)*f y) x-diff (S n) (fun y=>(a*y+b)*f y) (x-1) =
    (a*x+b)*diff (S(S n)) f x+Z.of_nat (S(S n))*a*diff (S n) f(x-1)).
    rewrite !IHn.
   change ((a*x+b)*diff (S n) f x+Z.of_nat (S n)*a*diff n f (x-1)-
     ((a*(x-1)+b)*diff (S n) f(x-1)+Z.of_nat (S n)*a*diff n f(x-1-1)) =
     (a*x+b)*(diff (S n) f x-diff (S n) f(x-1))+Z.of_nat (S (S n))*a*diff (S n) f(x-1)).
   replace (Z.of_nat (S (S n))) with (Z.of_nat (S n)+1) by lia.
   change (diff (S n) f (x-1)) with (diff n f (x-1)-diff n f(x-1-1)). ring.
Qed.
Lemma diff_rise d a b x : diff (S d) (fun y=>rise d (a*y+b)) x=0.
Proof.
 revert x;induction d;intro x;[reflexivity|].
 transitivity (diff (S (S d)) (fun y=>(a*y+(b+Z.of_nat (S d)))*rise d(a*y+b)) x).
 - apply diff_ext;intro y;cbn [rise];ring.
 - rewrite diff_affine. change (diff (S (S d)) (fun y=>rise d (a*y+b)) x)
    with (diff (S d) (fun y=>rise d (a*y+b)) x - diff (S d) (fun y=>rise d(a*y+b)) (x-1)).
   rewrite !IHd;ring.
Qed.
Lemma diff_extension cs k d x : diff (S d) (extension cs k d) x=0.
Proof.
 assert (A:forall w e, diff (S d) (fun t=>alt cs (fun v h=>if v <? k then rise d ((k-v)*t-h) else 0) w e) x=0); [|apply A].
 induction cs;intros w e.
 - cbn [alt];destruct (w <? k);[apply (diff_rise d (k-w) (-e))|apply diff_zero].
 - cbn [alt];rewrite diff_sub,!IHcs;ring.
Qed.
Lemma diff_reverse n f x : diff n (fun z=>f(-z)) x=parity n*diff n f (Z.of_nat n-x).
Proof.
 revert x;induction n;intro x;cbn [diff parity];[replace (Z.of_nat 0-x) with (-x) by ring;ring|].
 unfold backward;rewrite !IHn,Nat2Z.inj_succ.
 replace (Z.of_nat n-(x-1)) with (Z.succ (Z.of_nat n)-x) by lia.
 replace (Z.succ (Z.of_nat n)-x-1) with (Z.of_nat n-x) by lia. ring.
Qed.
Definition interior cs k (z:Z) := if z <? 2 then 0 else
 latticeCount (innerCaps cs (Z.to_nat z)) (k*z-boxSize cs).
Lemma fac_pos d : 0<fac d.
Proof. induction d;cbn [fac];[lia|apply Z.mul_pos_pos;lia]. Qed.
Theorem numerator_reversal cs k d : length cs=S d -> admissCaps cs -> 0<k<total cs ->
 k<boxSize cs -> forall z,
 diff (S d) (series k (scaled cs)) z=diff (S d) (interior cs k) (Z.of_nat (S d)-z).
Proof.
 intros D H K B z. assert (Sgn:=parity_sq d).
 assert (E:forall y, fac d*series k (scaled cs) y=extension cs k d y-
                 parity d*(fac d*interior cs k (-y))).
 { intro y. unfold series,interior. destruct (y <? 0) eqn:Y.
   - apply Z.ltb_lt in Y. destruct (-y <? 2) eqn:U.
     + apply Z.ltb_lt in U. replace y with (-1) by lia.
       pose proof (reflection_one cs k d D H K B);nia.
     + apply Z.ltb_ge in U. pose proof (reflection_inner cs k d (Z.to_nat (-y)) D H K ltac:(lia)) as T.
       rewrite Z2Nat.id,Z.opp_involutive in T by lia. unfold boxSize;rewrite D. rewrite <-T, Z.mul_assoc, Sgn. ring.
   - apply Z.ltb_ge in Y. rewrite (proj2 (Z.ltb_lt (-y) 2) ltac:(lia)),point_count.
     pose proof (extension_outer cs k d (Z.to_nat y) D H K) as T. rewrite Z2Nat.id in T by lia. rewrite T. ring. }
 pose proof (diff_ext (S d) _ _ E z) as T.
 rewrite diff_scale,diff_sub,diff_extension,!diff_scale,diff_reverse in T.
 cbn [parity] in T. pose proof (fac_pos d). assert (V:parity d=1 \/ parity d= -1) by nia. destruct V as [V|V];rewrite V in T;nia.
Qed.

Lemma diff_below n f a : (forall y,y<a -> f y=0) -> forall x, x<a -> diff n f x=0.
Proof. intro H;induction n;intros x T;[apply H,T|cbn [diff];unfold backward;rewrite !IHn by lia;ring]. Qed.
Lemma diff_first n f a : (forall y,y<a -> f y=0) ->
 diff n f a=f a /\ diff n f (a+1)=f(a+1)-Z.of_nat n*f a.
Proof.
 intro H;induction n as [|n [A B]];cbn [diff];[split;[reflexivity|change (Z.of_nat 0) with 0;ring]|].
 unfold backward. rewrite A,B,(diff_below n f a H (a-1)) by lia.
 replace (a+1-1) with a by lia. rewrite A,Nat2Z.inj_succ. split;ring.
Qed.
