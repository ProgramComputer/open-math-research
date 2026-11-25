From Stdlib Require Import Reals Reals.Ranalysis5 ZArith List Lia Lra Psatz Ring.
From OpenMath Require Import FiniteDifferences PolynomialSeparation.
From PrismSplit Require Import PrismEndpoint.
Import ListNotations.
Open Scope R_scope.

Fixpoint homogeneous (cs:list Z) (u v:R) : R :=
 match cs with []=>0 | c::rest=>IZR c * v^(length rest) + u * homogeneous rest u v end.

Definition weights : list Z :=
 [3826409662044539905758361;189774123324390903743071153;90973528792663334802337284;
  19031301363764499912342772;2260675907813810193257166;166465899991791793927982;
  7765872328799004829108;223600554184004506692;3620781643320313313;25123906039461097]%Z.

Lemma bernstein_certificate x :
  784^9 * value P x = homogeneous weights (x+840) (-56-x).
Proof. unfold weights, P; cbn [value homogeneous length]; ring. Qed.

Lemma homogeneous_nonneg cs u v : Forall (fun c=> (0<=c)%Z) cs -> 0<=u -> 0<=v ->
 0<=homogeneous cs u v.
Proof.
 intros H Hu Hv. induction H; cbn [homogeneous]; [lra|].
 apply Rplus_le_le_0_compat; apply Rmult_le_pos; auto using pow_le,
   IZR_le.
Qed.

Lemma unsplit_positive x : -840 < x < -56 -> 0 < value P x.
Proof.
 intro H. assert (W:0<homogeneous weights (x+840) (-56-x)).
 { 
   change (0 < IZR 3826409662044539905758361 * (-56-x)^9 +
             (x+840)*homogeneous (tl weights) (x+840) (-56-x)).
   apply Rplus_lt_le_0_compat.
   - apply Rmult_lt_0_compat; [apply IZR_lt; lia|apply pow_lt; lra].
   - apply Rmult_le_pos; [lra|]. apply homogeneous_nonneg; try lra.
     repeat constructor; lia. }
 pose proof (bernstein_certificate x). nra.
Qed.

(* Two split roots are exhibited with no unsplit root anywhere between them. *)
Lemma split_crossings : exists l r:R, -840<l /\ l< -838 /\ -57<r /\ r< -56 /\
 value Q l=0 /\ value Q r=0.
Proof.
 assert (A:0<value Q (-840)) by (unfold Q; cbn [value]; lra).
 assert (B:value Q (-838)<0) by (unfold Q; cbn [value]; lra).
 assert (C:value Q (-57)<0) by (unfold Q; cbn [value]; lra).
 assert (D:0<value Q (-56)) by (unfold Q; cbn [value]; lra).
 destruct (IVT_interv (fun x=> -value Q x) (-840) (-838)) as [l [[L1 L2] L]].
 - intros x _; apply continuity_pt_opp, continuous_value.
 - lra.
 - lra.
 - lra.
 - destruct (IVT_interv (value Q) (-57) (-56)) as [r [[R1 R2] R0]]; try lra;
   [intros;apply continuous_value|].
   exists l,r. assert (l <> -840) by (intro E; subst; lra).
   assert (l <> -838) by (intro E; subst; lra).
   assert (r <> -57) by (intro E; subst; lra).
   assert (r <> -56) by (intro E; subst; lra). repeat split; lra.
Qed.

(* The order is arbitrary: even a different dimensional normalization cannot
   restore interlacing. Any polynomial representing the normalized actual counts
   has exactly the canonical roots on the negative real axis. *)
Theorem prism_split_disproof : forall i j p q,
 numerator i 6 unsplit p -> numerator j 6 split q -> ~interlace p q.
Proof.
 intros i j p q Hp Hq [xs [ys [Hx [Hy Hweave]]]].
 assert (Sep:separates ys xs) by
   (destruct Hweave as [W|W]; [exact (proj2 (weave_separates _ _ W))|
                               exact (proj1 (weave_separates _ _ W))]).
 destruct split_crossings as [l [r [L1 [L2 [R1 [R2 [EL ER]]]]]]].
 assert (T:forall z, z<0 -> (value q z=0 <-> value Q z=0)) by
   (intros;apply (same_negative_zeros j 12 6 split);auto using split_full_series).
 assert (Hl:In l ys) by (apply Hy; apply (proj2 (T l ltac:(lra))); exact EL).
 assert (Hr:In r ys) by (apply Hy; apply (proj2 (T r ltac:(lra))); exact ER).
 destruct (Sep l r Hl Hr ltac:(lra)) as [z [Hz Hzrange]].
 apply Hx in Hz. apply (proj1 (same_negative_zeros i 11 6 unsplit p P z Hp
        unsplit_full_series ltac:(lra))) in Hz.
 pose proof (unsplit_positive z ltac:(lra)); lra.
Qed.

Corollary explicit_split : numerator 11 6 unsplit P /\ numerator 12 6 split Q /\ ~interlace P Q.
Proof. repeat split; auto using unsplit_full_series,split_full_series.
 exact (prism_split_disproof 11 12 P Q unsplit_full_series split_full_series).
Qed.
