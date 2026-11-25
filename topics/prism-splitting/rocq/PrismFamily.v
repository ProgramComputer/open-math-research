(* Combine the strict coefficient gap and Vieta with a uniform upper
   bound on split roots. The exceptional first member uses the two
   isolating intervals in PrismDisproof. *)
From Stdlib Require Import List ZArith Reals Lia Lra Psatz Ring.
From OpenMath Require Import BoundedCompositions FiniteDifferences BoxReflection NumeratorTable
 PolynomialSeparation PositiveSeries MonicRoots.
From PrismSplit Require Import PrismEndpoint PrismDisproof PrismFamilyCounts PrismAffine.
Import ListNotations.
Open Scope R_scope.

Lemma inverse_power x n : x<>0 -> (/x)^n*x^n=1.
Proof. intro X;induction n;[cbn;ring|]. cbn [pow]. replace (/x * (/x)^n * (x*x^n))
 with ((/x*x)*((/x)^n*x^n)) by ring. rewrite IHn;field;assumption.
Qed.
Lemma reciprocal_value p x : x<>0 -> value (rev p) (/x)*x^(length p)=x*value p x.
Proof.
 intro X;induction p as [|c p IH];[cbn;ring|]. cbn [rev length pow value].
 rewrite value_append,length_rev. cbn [value].
 pose proof (inverse_power x (length p) X).
 replace ((value (rev p) (/x)+(/x)^(length p)*(IZR c+/x*0))*(x*x^(length p)))
 with (x*(value (rev p)(/x)*x^(length p))+x*IZR c*((/x)^(length p)*x^(length p))) by ring.
 rewrite H. nra.
Qed.

Lemma positive_reciprocal cs k d : length cs=S d -> admissCaps cs -> (0<k<total cs)%Z ->
 (k<boxSize cs)%Z -> interior cs k 2=1%Z -> forall x,1<x -> 0<value (hlist cs k) x.
Proof.
 intros D H K B I x X. set (L:=fun z=>interior cs k (z+2)%Z).
 set (g:=diff (S d) L).
 assert (Shift:forall z,g z=diff (S d) (interior cs k) (z+2)%Z).
 { intro z;unfold g,L.
   transitivity (diff (S d) (fun y=>interior cs k (y- -2)%Z) z).
   - apply diff_ext;intro y;f_equal;ring.
   - rewrite diff_shift;f_equal;ring. }
 assert (R:rev(hlist cs k)=table d g 0).
 { unfold hlist;rewrite D. replace (S d-1)%nat with d by lia. apply rev_table.
   intros j J;unfold hcoeff;rewrite D,(numerator_reversal cs k d D H K B),Shift. f_equal;lia. }
 assert (M:forall z, g z=coefficient (rev(hlist cs k)) z).
 { rewrite R;intro z;symmetry;apply table_num. intros y [T|T].
   - apply (diff_below _ _ 0);[intros z0 Z0;unfold L;apply interior_below;lia|lia].
   - rewrite Shift. replace (y+2)%Z with (Z.of_nat(S d)-(Z.of_nat d-1-y))%Z by lia.
     rewrite <-(numerator_reversal cs k d D H K B).
     apply (diff_below _ _ 0);[intros z0 Z0;unfold series;rewrite (proj2 (Z.ltb_lt _ _) Z0);reflexivity|lia]. }
 assert (V:0<value (rev(hlist cs k)) (/x)).
 { apply (positive_numerator_at_fraction (S d) L).
   - intro z;unfold L,interior;destruct (_ <? _)%Z;[lia|rewrite <-point_count;lia].
   - intros z Z0;unfold L;apply interior_below;lia.
   - unfold L;change (0<interior cs k 2)%Z;rewrite I;lia.
   - exact M.
   - split;[apply Rinv_0_lt_compat;lra|]. apply (Rmult_lt_reg_r x);[lra|]. rewrite Rinv_l by lra;lra. }
 pose proof (reciprocal_value (hlist cs k) x ltac:(lra)).
 assert (0<x^(length(hlist cs k))) by (apply pow_lt;lra). nra.
Qed.

Definition beforeH b := hlist (before b) (level b).
Definition afterH b := hlist (after b) (level b).

Theorem family_large b : (6<=b)%nat ->
 numerator (S(2*b)) (level b) (scaled (before b)) (beforeH b) /\
 numerator (S(2*b+1)) (level b) (scaled (after b)) (afterH b) /\
 ~ interlaceUpToScale (beforeH b) (afterH b).
Proof.
 intro Hb;destruct (before_data b ltac:(lia)) as [D [H [K B]]].
 destruct (after_data b ltac:(lia)) as [E [J [L C]]].
 split;[apply hlist_full;assumption|]. split;[apply hlist_full;assumption|].
 set (n:=(2*b-2)%nat).
 assert (T:length (before b)=S(S(S n))) by (unfold n;lia).
 assert (U:length (after b)=S(S(S(S n)))) by (unfold n;lia).
 destruct (hlist_top _ _ n T H K B (before_two b)) as [p [Lp P]].
 destruct (hlist_top _ _ (S n) U J L C (after_two b)) as [q [Lq Q]].
 intro W;apply (monic_interlace _ _ _ _ P Q) in W;revert W.
 eapply (sum_obstruction _ _ _ _ p q).
 - exact P.
 - exact Q.
 - lia.
 - pose proof (interior_gap b Hb);lia.
 - intros x V;destruct (Rle_dec x 1);[assumption|].
   pose proof (positive_reciprocal _ _ _ E J L C (after_two b) x ltac:(lra));unfold afterH in V;lra.
Qed.

(* b=a-1. The finite disproof and the generic tail give one all-size statement. *)
Theorem full_prism_family (a:nat) : (6<=a)%nat ->
 let b:=(a-1)%nat in exists p q,
 numerator (S(2*b)) (level b) (scaled (before b)) p /\
 numerator (S(2*b+1)) (level b) (scaled (after b)) q /\ ~interlaceUpToScale p q.
Proof.
 intro H;cbn zeta. destruct (Nat.eq_dec a 6) as [->|E].
 - exists P,Q. destruct explicit_split as [T [U G]].
   assert (F:forall i, scaled (before 5) i=unsplit i).
   { intro i;unfold scaled,before,unsplit;rewrite map_app,map_rep. cbn [map].
     rewrite Nat.mul_1_r,(Nat.mul_comm i 2);reflexivity. }
   assert (A:forall i, scaled (after 5) i=split i).
   { intro i;unfold scaled,after,split;rewrite map_rep,Nat.mul_1_r;reflexivity. }
   assert (N:forall s k u v h, (forall i,u i=v i) -> numerator s k u h -> numerator s k v h).
   { intros s k u v h E V z. transitivity (diff s (series k u) z).
     - apply diff_ext;intro t;unfold series;rewrite E;reflexivity.
     - apply V. }
   split;[apply (N 11%nat 6%Z unsplit);[symmetry;apply F|exact T]|].
   split;[apply (N 12%nat 6%Z split);[symmetry;apply A|exact U]|].
   intro W;apply G,full_implies_weaker. eapply monic_interlace;[reflexivity|reflexivity|exact W].
 - exists (beforeH (a-1)),(afterH (a-1));apply family_large;lia.
Qed.

(* n is the number of free real coordinates in the affine hull. *)
Theorem geometric_prism_family a (Ha:(6<=a)%nat) : let b:=(a-1)%nat in
 (forall n c, ((n=2*b /\ c=2) \/ (n=2*b+1 /\ c=1))%nat ->
  (forall p, hull (slice n (INR c) (IZR(level b))) p <-> plane n (IZR(level b)) p) /\
  (forall t zs z, inDilation n (INR c) (IZR(level b)) (INR t) (map IZR zs,IZR z) <->
   exists xs y, zs=map Z.of_nat xs /\ z=Z.of_nat y /\
     In (xs++[y]) (points (scaled (repeat 1%nat n++[c]) t) (level b*Z.of_nat t)))) /\
 (exists p q, numerator (S(2*b)) (level b) (scaled (before b)) p /\
 numerator (S(2*b+1)) (level b) (scaled (after b)) q /\ ~interlaceUpToScale p q).
Proof.
 cbn zeta;set (b:=(a-1)%nat);split;[|exact (full_prism_family a Ha)].
 intros n c D;split;[exact (proj1 (family_affine_charts b n c D))|].
 intros t zs z;apply signed_integer_dilation;destruct D as [[-> ->]|[-> ->]];try lia;
 unfold level;rewrite ?plus_IZR,<-?INR_IZR_INZ,?plus_INR,?mult_INR;cbn;lra.
Qed.
