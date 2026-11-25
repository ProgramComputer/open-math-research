(* Weak alternation of complete real factorizations with multiplicities.
   The next coefficient is minus the sum of the roots in the monic case. *)
From Stdlib Require Import List ZArith Reals Lia Lra Psatz Ring.
From OpenMath Require Import PolynomialSeparation PositiveSeries.
Import ListNotations.
Open Scope R_scope.

Fixpoint descending (cs:list R) (x:R) :=
 match cs with []=>0|c::rest=>c*x^(length rest)+descending rest x end.
Lemma descending_snoc cs a x : descending (cs++[a]) x=x*descending cs x+a.
Proof.
 induction cs;[cbn;ring|]. cbn [app descending]. rewrite length_app;cbn [length].
 replace (length cs+1)%nat with (S(length cs)) by lia. rewrite IHcs;cbn [pow];ring.
Qed.
Lemma descending_value p x : descending (map IZR (rev p)) x=value p x.
Proof. induction p;[reflexivity|]. cbn [rev value]. rewrite map_app. cbn [map].
 rewrite descending_snoc,IHp;ring. Qed.
Fixpoint linearTail (r c:R) (cs:list R) :=
 match cs with []=>[-r*c]|a::rest=>(a-r*c)::linearTail r a rest end.
Definition linearFactor r cs := match cs with []=>[]|a::rest=>a::linearTail r a rest end.
Fixpoint expansion (xs:list R) : list R :=
 match xs with []=>[1]|r::rest=>linearFactor r (expansion rest) end.
Definition fullRealInterlace p q := exists xs ys:list R,
 map IZR (rev p)=expansion xs /\ map IZR (rev q)=expansion ys /\
 (weave xs ys \/ weave ys xs).
Lemma linearTail_length r c l : length (linearTail r c l)=S(length l).
Proof. revert c;induction l;intro;cbn;auto. Qed.
Lemma linearTail_value r c l x : descending (linearTail r c l) x=
 (x-r)*descending l x-r*c*x^(length l).
Proof. revert c;induction l;intro;cbn [linearTail descending length pow];[ring|].
 rewrite linearTail_length,IHl;cbn [pow];ring. Qed.
Lemma linearFactor_value r l x : descending (linearFactor r l) x=(x-r)*descending l x.
Proof. destruct l;cbn [linearFactor descending];[ring|].
 rewrite linearTail_length,linearTail_value;cbn [pow];ring. Qed.
Lemma expansion_len xs : exists l, expansion xs=1::l /\ length l=length xs.
Proof.
 induction xs as [|r xs [l [E L]]];[exists [];auto|].
 exists (linearTail r 1 l);cbn [expansion];rewrite E;split;[reflexivity|rewrite linearTail_length,L;reflexivity].
Qed.
Lemma expansion_roots xs t : descending (expansion xs) t=0 <-> In t xs.
Proof.
 induction xs as [|r xs IH];[cbn;split;[lra|contradiction]|].
 cbn [expansion In];rewrite linearFactor_value. split.
 - intro E;apply Rmult_integral in E as [E|E];[left;lra|right;now apply IH].
 - intros [E|E];[subst;ring|apply IH in E;rewrite E;ring].
Qed.
Lemma full_implies_weaker p q : fullRealInterlace p q -> interlace p q.
Proof.
 intros [xs [ys [P [Q W]]]];exists xs,ys;repeat split.
 - intro H;rewrite <-descending_value,P;apply expansion_roots,H.
 - intro H;apply expansion_roots;rewrite <-P,descending_value;exact H.
 - intro H;rewrite <-descending_value,Q;apply expansion_roots,H.
 - intro H;apply expansion_roots;rewrite <-Q,descending_value;exact H.
 - exact W.
Qed.
Fixpoint rootSum (l:list R) : R := match l with []=>0|a::r=>a+rootSum r end.
Lemma next_rootSum xs : nth 1 (expansion xs) 0= -rootSum xs.
Proof. induction xs as [|x xs IH];[cbn;ring|].
 destruct (expansion_len xs) as [l [E _]]. rewrite E in IH;cbn [expansion];rewrite E.
 destruct l;cbn [linearFactor linearTail nth rootSum] in *;lra.
Qed.
Lemma weave_lengths xs ys : weave xs ys -> (length ys<=length xs<=S(length ys))%nat.
Proof. induction 1;cbn;lia. Qed.
Lemma weave_sum ys xs : weave ys xs -> (forall y,In y ys -> y<=1) ->
 rootSum ys<=rootSum xs+1.
Proof.
 revert ys;induction xs as [|x xs IH];intros ys W B.
 - pose proof (weave_lengths _ _ W) as L. destruct ys as [|y [|z tail]];cbn in *;try lia;try lra.
   specialize (B y ltac:(auto));lra.
 - inversion W as [|y ys' vs O Tail];subst.
   inversion Tail as [|z zs us O' Tail'];subst.
   specialize (IH _ Tail' (fun t H=>B t (or_intror H))).
   specialize (O x (or_introl eq_refl)). cbn [rootSum];lra.
Qed.
Lemma sum_obstruction p q pc qc a b :
 rev p=1%Z::pc::a -> rev q=1%Z::qc::b ->
 length b=S(length a) -> (qc+1<pc)%Z ->
 (forall x, value q x=0 -> x<=1) -> ~fullRealInterlace p q.
Proof.
 intros P Q L G B [xs [ys [X [Y W]]]].
 assert (BX:forall t, In t ys -> t<=1).
 { intros t H;apply B;rewrite <-descending_value,Y;apply expansion_roots,H. }
 assert (LX:length ys=S(length xs)).
 { destruct (expansion_len xs) as [u [A U]],(expansion_len ys) as [v [C V]].
   rewrite A,P in X;rewrite C,Q in Y.
   apply (f_equal (@length R)) in X;apply (f_equal (@length R)) in Y.
   rewrite !length_map in X,Y;cbn [length] in *;lia. }
 assert (T:weave ys xs) by (destruct W as [W|W];[pose proof (weave_lengths _ _ W);lia|exact W]).
 pose proof (weave_sum _ _ T BX) as S. pose proof (next_rootSum xs) as A;pose proof (next_rootSum ys) as C.
 rewrite <-X,P in A;rewrite <-Y,Q in C;cbn [map nth] in A,C.
 apply IZR_lt in G;rewrite plus_IZR in G;lra.
Qed.

(* Arbitrary nonzero leading scalars allow the usual, unnormalized
   polynomials in the definition of complete real factorizations. *)
Definition interlaceUpToScale (p q:list Z) := exists c d xs ys,
 c<>0 /\ d<>0 /\ map IZR (rev p)=map (Rmult c) (expansion xs) /\
 map IZR (rev q)=map (Rmult d) (expansion ys) /\ (weave xs ys \/ weave ys xs).

Lemma remove_scalar p tail c roots : rev p=1%Z::tail ->
 map IZR (rev p)=map (Rmult c) (expansion roots) ->
 map IZR (rev p)=expansion roots.
Proof.
 intros P E. destruct (expansion_len roots) as [u [U L]].
 assert (C:c=1).
 { rewrite P,U in E;injection E as A B;cbn in A;lra. }
 subst c;rewrite E. clear E U L. induction (expansion roots) as [|v vs IH];cbn;[reflexivity|].
 rewrite Rmult_1_l,IH;reflexivity.
Qed.

Lemma monic_interlace p q s t : rev p=1%Z::s -> rev q=1%Z::t ->
 interlaceUpToScale p q -> fullRealInterlace p q.
Proof.
 intros P Q [c [d [xs [ys [_ [_ [A [B W]]]]]]]].
 exists xs,ys;split;[eapply remove_scalar;eassumption|].
 split;[eapply remove_scalar;eassumption|exact W].
Qed.
