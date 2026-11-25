(* Real prism slices and their dilations. The center allows an explicit
   affine extrapolation to every point of the hyperplane. Its final
   coordinate is determined by the other coordinates. *)
From Stdlib Require Import List Reals ZArith Lia Lra Psatz Ring.
From OpenMath Require Import BoundedCompositions BoxReflection.
From PrismSplit Require Import PrismFamilyCounts.
Import ListNotations.
Open Scope R_scope.

Definition rsum := fold_right Rplus 0.
Definition plane n k (p:list R*R) := length (fst p)=n /\ rsum (fst p)+snd p=k.
Definition slice n c k (p:list R*R) := plane n k p /\
 Forall (fun x=>0<=x<=1) (fst p) /\ 0<=snd p<=c.
Definition mix t x y := x+t*(y-x).
Fixpoint mixList t (xs ys:list R) :=
 match xs,ys with x::a,y::b=>mix t x y::mixList t a b|_,_=>[] end.
Definition mixPoint t (p q:list R*R) :=
 (mixList t (fst p) (fst q),mix t (snd p) (snd q)).
Definition hull (S:list R*R->Prop) (p:list R*R) := forall A:list R*R->Prop,
 (forall u,S u -> A u) -> (forall t u v,A u -> A v -> A (mixPoint t u v)) -> A p.
Definition chart k (u:list R) := (u,k-rsum u).

Lemma mix_length t u v : length u=length v -> length(mixList t u v)=length u.
Proof. revert v;induction u;intros [|y v] H;cbn in *;try discriminate;auto. Qed.
Lemma sum_mix t u v : length u=length v -> rsum (mixList t u v)=mix t (rsum u) (rsum v).
Proof. revert v;induction u;intros [|y v] H;try discriminate;cbn [mixList rsum fold_right];
 [unfold mix;ring|].
 rewrite IHu by (injection H;auto). unfold mix;ring.
Qed.
Lemma repeat_sum n c : rsum (repeat c n)=INR n*c.
Proof. induction n;[cbn;ring|]. change (c+rsum(repeat c n)=INR(S n)*c).
 rewrite IHn,S_INR;ring. Qed.
Lemma mix_undo t x y : 0<t -> mix (/t) x (mix t x y)=y.
Proof. intro H;unfold mix;field;lra. Qed.
Lemma undo_list t u v : 0<t -> length u=length v -> mixList (/t) u (mixList t u v)=v.
Proof. intro H;revert v;induction u;intros [|y v] E;try discriminate;cbn;[reflexivity|].
 rewrite mix_undo,IHu;auto;injection E;auto. Qed.
Definition dev (xs:list R) := rsum(map (fun x=>Rabs(x-1/2)) xs).
Lemma dev_pos xs : 0<=dev xs.
Proof. induction xs;[cbn;lra|]. change (0<=Rabs(a-1/2)+dev xs). pose proof (Rabs_pos(a-1/2));lra. Qed.
Lemma dev_bound xs x : In x xs -> Rabs(x-1/2)<=dev xs.
Proof. induction xs;[contradiction|]. intros H;change (Rabs (x-1/2)<=Rabs(a-1/2)+dev xs);destruct H as [<-|H];
 [pose proof (dev_pos xs);lra|pose proof (IHxs H);pose proof (Rabs_pos(a-1/2));lra]. Qed.
Lemma segment_bound u c y :
 1<=c -> let M:=1+dev u+Rabs(y-c/2) in let t:= /(2*M) in
 0<t /\ (forall x, In x u -> 0<=mix t (1/2) x<=1) /\ 0<=mix t (c/2) y<=c.
Proof.
 intro C;cbn zeta;set (M:=1+dev u+Rabs(y-c/2)).
 assert (D:0<=dev u) by apply dev_pos. pose proof (Rabs_pos(y-c/2)) as Y.
 assert (M0:0<M) by (unfold M;lra). assert (T:0< /(2*M)) by (apply Rinv_0_lt_compat;lra).
 assert (E: /(2*M)*(2*M)=1) by (apply Rinv_l;lra).
 assert (B:forall v,Rabs v<=M -> -1/2<= /(2*M)*v<=1/2).
 { intros v V. pose proof (Rle_abs v). pose proof (Rle_abs (-v)).
   rewrite Rabs_Ropp in H0. split; nra. }
 split;[exact T|]. split.
 - intros x X;pose proof (dev_bound u x X) as A;specialize (B (x-1/2) ltac:(unfold M;lra));unfold mix;lra.
 - specialize (B (y-c/2) ltac:(unfold M;lra));unfold mix;lra.
Qed.
Lemma mix_repeat_forall t u :
 (forall x,In x u ->0<=mix t (1/2) x<=1) -> Forall (fun y=>0<=y<=1) (mixList t (repeat (1/2) (length u)) u).
Proof.
 induction u;intro H;cbn;constructor.
 - apply H;left;reflexivity.
 - apply IHu;intros x X;apply H;right;exact X.
Qed.

(* The graph has n freely chosen real coordinates, with affine inverse fst. *)
Theorem slice_chart n c k : 1<=c -> 2*k=INR n+c ->
 (forall p,hull (slice n c k) p <-> plane n k p) /\
 (forall u,length u=n -> plane n k (chart k u) /\ fst (chart k u)=u) /\
 (forall p,plane n k p -> chart k (fst p)=p) /\
 (forall t u v,length u=n -> length v=n ->
    chart k (mixList t u v)=mixPoint t (chart k u) (chart k v)).
Proof.
 intros C K. split.
 - intros [u y];split.
   + intro G;apply (G (plane n k));[intros v [V _];exact V|].
     intros t [l z] [r w] [A B] [D E]. unfold plane,mixPoint in *;cbn [fst snd] in *.
     rewrite mix_length,sum_mix by congruence;unfold mix;split;[assumption|nra].
   + intros [U V] A incl closed. cbn [fst snd] in U,V.
     set (o:=(repeat (1/2) n,c/2)).
     assert (S:slice n c k o).
     { unfold slice,plane,o;cbn [fst snd]. rewrite repeat_length,repeat_sum. repeat split;try lra.
       apply Forall_forall;intros x X;apply repeat_spec in X;subst;lra. }
     pose proof (segment_bound u c y C) as [T [T1 T2]];cbn zeta in T,T1,T2.
     set (t:=/(2*(1+dev u+Rabs(y-c/2)))) in *.
     assert (M:slice n c k (mixPoint t o (u,y))).
     { unfold slice,plane,mixPoint,o;cbn [fst snd]. rewrite mix_length,sum_mix by (rewrite repeat_length;lia).
       rewrite repeat_length,repeat_sum. split;[split;[reflexivity|unfold mix;nra]|]. split;[rewrite <-U;apply mix_repeat_forall,T1|exact T2]. }
     assert (Z:=closed (/t) o _ (incl _ S) (incl _ M)).
     unfold mixPoint,o in Z;cbn [fst snd] in Z.
     rewrite undo_list,mix_undo in Z;auto;rewrite repeat_length;lia.
 - split;[intros u U;unfold plane,chart;cbn;intuition lra|].
   split;[intros [u y] [_ V];unfold chart;cbn in *;f_equal;lra|].
   intros t u v U V;unfold chart,mixPoint;cbn [fst snd];rewrite sum_mix by congruence.
   f_equal;unfold mix;ring.
Qed.

Lemma after_caps_chart b : after b=repeat 1%nat (2*b+1)++[1%nat].
Proof. unfold after. change [1%nat] with (repeat 1%nat 1). rewrite <-repeat_app.
 replace (2*b+1+1)%nat with (2*b+2)%nat by lia. reflexivity.
Qed.
Theorem family_affine_charts b : forall (n c:nat),
 ((n=2*b /\ c=2) \/ (n=2*b+1 /\ c=1))%nat ->
 (forall p,hull (slice n (INR c) (IZR(level b))) p <-> plane n (IZR(level b)) p) /\
 (forall u,length u=n -> plane n (IZR(level b)) (chart (IZR(level b)) u) /\ fst(chart (IZR(level b)) u)=u) /\
 (forall p,plane n (IZR(level b)) p -> chart (IZR(level b)) (fst p)=p) /\
 (forall t u v,length u=n -> length v=n -> chart (IZR(level b)) (mixList t u v)=
  mixPoint t (chart (IZR(level b)) u) (chart (IZR(level b)) v)).
Proof.
 intros n c [[-> ->]|[-> ->]];apply slice_chart;unfold level;rewrite ?plus_IZR,<-?INR_IZR_INZ,?plus_INR,?mult_INR;cbn;lra.
Qed.

Definition dilate t (p:list R*R) := (map (fun z=>t*z) (fst p),t*snd p).
Definition inDilation n c k (t:R) p := exists q, slice n c k q /\ dilate t q=p.
Definition scaledSlice n c k t (p:list R*R) :=
 length(fst p)=n /\ rsum(fst p)+snd p=t*k /\ Forall (fun x=>0<=x<=t) (fst p) /\
 0<=snd p<=t*c.
Lemma sum_scale t u : rsum (map (fun x=>t*x) u)=t*rsum u.
Proof. induction u;cbn [map rsum fold_right];[ring|rewrite IHu;ring]. Qed.
Lemma scale_back u t : t<>0 -> map (fun x=>t*x) (map (fun x=>/t*x) u)=u.
Proof. intro T;induction u;cbn;[reflexivity|rewrite IHu;f_equal;field;exact T]. Qed.
Lemma zero_list t u : Forall (fun x=>0<=x<=0) u -> map (fun x=>0*x) (repeat t (length u))=u.
Proof. induction 1;cbn;[reflexivity|rewrite IHForall;f_equal;lra]. Qed.
Lemma dilation_iff n c k t p : 0<=t -> 1<=c -> 2*k=INR n+c ->
 (inDilation n c k t p <-> scaledSlice n c k t p).
Proof.
 intros T C K;destruct p as [u y];split.
 - intros [[v z] [[ [N V] [A B]] E]]. unfold dilate in E;cbn in E;injection E as U Y;subst.
   unfold scaledSlice;cbn [fst snd] in *;rewrite length_map,sum_scale. repeat split;try nra;auto.
   apply Forall_forall;intros x X;apply in_map_iff in X as [w [<- W]].
   rewrite Forall_forall in A;specialize (A w W);split;nra.
 - intros [N [V [A B]]];cbn [fst snd] in *;destruct (Req_dec t 0) as [->|T0].
   + exists (repeat (1/2) n,c/2);split.
     * unfold slice,plane;cbn [fst snd];rewrite repeat_length,repeat_sum. repeat split;try lra.
       apply Forall_forall;intros x X;apply repeat_spec in X;subst;lra.
     * unfold dilate;cbn [fst snd];rewrite <-N,zero_list by exact A;f_equal;lra.
   + exists (map (fun x=>/t*x) u,/t*y);split.
     * unfold slice,plane;cbn [fst snd];rewrite length_map,sum_scale;split;[split;[auto|replace (/t*rsum u+/t*y) with (/t*(rsum u+y)) by ring;rewrite V;field;exact T0]|].
       assert (P:0< /t) by (apply Rinv_0_lt_compat;lra).
       assert (M:/t*t=1) by (apply Rinv_l;exact T0).
       split;[|split;nra]. apply Forall_forall;intros x X;apply in_map_iff in X as [w [<- W]].
       rewrite Forall_forall in A;specialize (A w W);split;nra.
     * unfold dilate;cbn [fst snd];rewrite scale_back by assumption;f_equal;field;assumption.
Qed.
Lemma admiss_chart n t c xs y :
 admissible (repeat t n++[c]) (xs++[y]) <->
 length xs=n /\ Forall (fun x=>(x<=t)%nat) xs /\ (y<=c)%nat.
Proof.
 revert xs;induction n as [|n IH];intros [|x xs].
 - cbn [repeat app admissible length];intuition auto using Forall_nil.
 - destruct xs;cbn [repeat app admissible length];intuition discriminate.
 - destruct n;cbn [repeat app admissible length];intuition discriminate.
 - cbn [repeat app admissible length];rewrite IH. split.
   + intros [X [N [A Y]]];subst;repeat split;auto.
   + intros [N [A Y]];inversion A;intuition lia.
Qed.
Lemma real_total xs : rsum (map INR xs)=IZR(total xs).
Proof. induction xs;cbn [total map rsum fold_right];[reflexivity|rewrite IHxs,plus_IZR,INR_IZR_INZ;reflexivity]. Qed.
Lemma nat_bounds_real xs t : Forall (fun x=>(x<=t)%nat) xs <->
 Forall (fun x=>0<=x<=INR t) (map INR xs).
Proof.
 rewrite !Forall_forall;split.
 - intros A w W;apply in_map_iff in W as [z [<- Z0]]. split;[apply pos_INR|apply le_INR,A,Z0].
 - intros A z Z0;apply INR_le. apply (A _ (in_map INR _ _ Z0)).
Qed.
Theorem integer_dilation n c k t xs y : (1<=c)%nat -> 2*IZR k=INR n+INR c ->
 (In (xs++[y]) (points (scaled (repeat 1%nat n++[c]) t) (k*Z.of_nat t)) <->
 inDilation n (INR c) (IZR k) (INR t) (map INR xs,INR y)).
Proof.
 intros C K;rewrite points_spec,dilation_iff by (try apply pos_INR;try exact K;change (INR 1<=INR c);apply le_INR;lia).
 unfold scaled;rewrite map_app,map_rep,Nat.mul_1_r. cbn [map].
 rewrite admiss_chart,total_app. unfold scaledSlice;cbn [fst snd];rewrite length_map,real_total.
 cbn [total]. rewrite Z.add_0_r,nat_bounds_real.
 assert (S: (total xs+Z.of_nat y=k*Z.of_nat t)%Z <-> IZR (total xs)+INR y=INR t*IZR k).
 { rewrite !INR_IZR_INZ,<-plus_IZR,Rmult_comm,<-mult_IZR;split;[intros ->;reflexivity|apply eq_IZR]. }
 assert (B:(y<=t*c)%nat <-> 0<=INR y<=INR t*INR c).
 { rewrite <-mult_INR;split;[intro;split;auto using pos_INR,le_INR|intros [_ E];apply INR_le,E]. }
 tauto.
Qed.

Lemma mapped_integers xs : map IZR (map Z.of_nat xs)=map INR xs.
Proof. induction xs;cbn;[reflexivity|rewrite IHxs,INR_IZR_INZ;reflexivity]. Qed.

(* Every signed lattice point of a true dilation is represented, including t=0. *)
Theorem signed_integer_dilation n c k t zs z : (1<=c)%nat -> 2*IZR k=INR n+INR c ->
 (inDilation n (INR c) (IZR k) (INR t) (map IZR zs,IZR z) <->
 exists xs y, zs=map Z.of_nat xs /\ z=Z.of_nat y /\
 In (xs++[y]) (points (scaled (repeat 1%nat n++[c]) t) (k*Z.of_nat t))).
Proof.
 intros C K;split.
 - intro D;pose proof D as B.
   apply dilation_iff in B;[|apply pos_INR|change (INR 1<=INR c);apply le_INR,C|exact K].
   destruct B as [_ [_ [F [Y T]]]];cbn [fst snd] in F,Y.
   assert (L:map Z.of_nat (map Z.to_nat zs)=zs).
   { clear -F;induction zs as [|s zs IH];cbn in *;[reflexivity|].
     inversion F as [|? ? [P _] H];subst;rewrite IH by assumption.
     f_equal;apply Z2Nat.id;apply le_IZR;exact P. }
   assert (V:Z.of_nat (Z.to_nat z)=z) by (apply Z2Nat.id,le_IZR;exact Y).
   exists (map Z.to_nat zs),(Z.to_nat z);split;[symmetry;exact L|].
   split;[symmetry;exact V|]. apply (proj2 (integer_dilation _ _ _ _ _ _ C K)).
   rewrite <-mapped_integers,L,(INR_IZR_INZ (Z.to_nat z)),V;exact D.
 - intros [xs [y [-> [-> M]]]];rewrite mapped_integers,<-(INR_IZR_INZ y).
   apply (proj1 (integer_dilation _ _ _ _ _ _ C K)),M.
Qed.
