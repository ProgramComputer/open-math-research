From Stdlib Require Import List ZArith Lia Ring.
Import ListNotations.
Open Scope Z_scope.

(* A coordinate is an integer in [0,b], hence uniquely a natural number. *)
Fixpoint window (b : nat) (f : Z -> Z) (x : Z) : Z :=
  match b with O => f x | S k => window k f x + f (x-Z.of_nat (S k)) end.

Fixpoint latticeCount (bounds : list nat) (target : Z) : Z :=
  match bounds with
  | [] => if target =? 0 then 1 else 0
  | b :: bs => window b (latticeCount bs) target
  end.

Fixpoint points (bounds : list nat) (target : Z) : list (list nat) :=
  match bounds with
  | [] => if target =? 0 then [[]] else []
  | b :: bs => flat_map (fun i => map (cons i) (points bs (target-Z.of_nat i))) (seq 0 (S b))
  end.

Fixpoint admissible (bounds xs : list nat) : Prop :=
  match bounds,xs with
  | [],[] => True
  | b::bs,x::ys => (x <= b)%nat /\ admissible bs ys
  | _,_ => False
  end.
Fixpoint total (xs:list nat) : Z :=
  match xs with [] => 0 | x::ys => Z.of_nat x + total ys end.

Lemma points_spec bs x t : In x (points bs t) <-> admissible bs x /\ total x = t.
Proof.
  revert x t; induction bs as [|b bs IH]; intros x t; cbn [points].
  - destruct (t =? 0) eqn:E.
    + apply Z.eqb_eq in E; subst; destruct x; simpl; intuition discriminate.
    + apply Z.eqb_neq in E; destruct x; simpl; intuition congruence.
  - rewrite in_flat_map. split.
    + intros [i [Hi Hx]]. apply in_seq in Hi. apply in_map_iff in Hx.
      destruct Hx as [ys [<- Hys]]. apply IH in Hys. simpl. intuition lia.
    + destruct x as [|i ys]; cbn [admissible total]; [tauto|].
      intros [[Hi Hy] Ht]. exists i. split; [apply in_seq; lia|].
      apply in_map. apply IH. intuition lia.
Qed.

Lemma window_ext b f g : (forall x, f x = g x) -> forall x, window b f x = window b g x.
Proof. intro E; induction b; simpl; intros; rewrite ?IHb, ?E; reflexivity. Qed.

Lemma point_count bs t : Z.of_nat (length (points bs t)) = latticeCount bs t.
Proof.
  revert t; induction bs as [|b bs IH]; intro t; cbn [points latticeCount].
  - destruct (t =? 0); reflexivity.
  - induction b as [|b Hb].
    + simpl. rewrite app_nil_r, length_map, Z.sub_0_r. apply IH.
    + rewrite seq_S, flat_map_app, length_app, Nat2Z.inj_add. simpl flat_map.
      rewrite app_nil_r, length_map, IH. simpl window. rewrite <- Hb. reflexivity.
Qed.

Fixpoint rise (d:nat) (x:Z) : Z :=
  match d with O => 1 | S m => rise m x * (x+Z.of_nat (S m)) end.
Definition trunc (d:nat) (x:Z) := if x <? 0 then 0 else rise d x.
Fixpoint fac (d:nat) : Z := match d with O=>1|S m=>Z.of_nat (S m)*fac m end.
Fixpoint cuts (caps:list nat) (f:Z->Z) (x:Z) : Z :=
  match caps with []=>f x|b::bs=>cuts bs f x - cuts bs f (x-Z.of_nat b-1) end.

Lemma rise_step m x : rise (S m) x - rise (S m) (x-1) = Z.of_nat (S m) * rise m x.
Proof.
  induction m as [|m IH]; [cbn [rise]; ring|].
  change (rise (S m) x * (x+Z.of_nat (S (S m))) -
     rise (S m) (x-1) * (x-1+Z.of_nat (S (S m))) = Z.of_nat (S (S m)) * rise (S m) x).
  replace (x-1+Z.of_nat (S (S m))) with (x+Z.of_nat (S m)) by lia.
  change (rise (S m) x * (x+Z.of_nat (S (S m))) -
     rise (S m) (x-1) * (x+Z.of_nat (S m)) = Z.of_nat (S (S m)) *
     (rise m x * (x+Z.of_nat (S m)))).
  replace (Z.of_nat (S (S m))) with (Z.of_nat (S m)+1) by lia.
  replace (rise (S m) (x-1)) with (rise (S m) x-Z.of_nat (S m)*rise m x) by lia.
  cbn [rise].
  ring.
Qed.

Lemma rise_zero m : rise m 0 = fac m.
Proof. induction m; cbn [rise fac]; [reflexivity|rewrite IHm; ring]. Qed.

Lemma trunc_step m x : trunc (S m) x - trunc (S m) (x-1) = Z.of_nat (S m) * trunc m x.
Proof.
  unfold trunc. destruct (x <? 0) eqn:E; destruct (x-1 <? 0) eqn:F.
  - ring.
  - apply Z.ltb_lt in E; apply Z.ltb_ge in F; lia.
  - apply Z.ltb_ge in E; apply Z.ltb_lt in F. replace x with 0 by lia.
    rewrite !rise_zero. cbn [fac]. ring.
  - apply rise_step.
Qed.

Lemma window_scale b c f x :
  window b (fun y=>c*f y) x = c*window b f x.
Proof. induction b; cbn [window]; [reflexivity|rewrite IHb; ring]. Qed.
Lemma window_diff b f x : window b (fun y=>f y-f(y-1)) x = f x-f(x-Z.of_nat b-1).
Proof.
  induction b as [|b IH]; cbn [window].
  - replace (x-Z.of_nat 0-1) with (x-1) by lia. reflexivity.
  - rewrite IH. replace (x-Z.of_nat (S b)) with (x-Z.of_nat b-1) by lia. ring.
Qed.

Lemma window_shift b f h x : window b (fun y=>f(y-h)) x = window b f (x-h).
Proof. induction b; simpl; [reflexivity|rewrite IHb; f_equal; f_equal; lia]. Qed.
Lemma window_linear b f g x : window b (fun y=>f y-g y) x = window b f x-window b g x.
Proof. induction b; cbn [window]; [reflexivity|rewrite IHb; ring]. Qed.
Lemma window_cuts b cs f x :
   window b (cuts cs f) x = cuts cs (window b f) x.
Proof.
  revert x; induction cs as [|c cs IH]; intro x; [reflexivity|].
  cbn [cuts]. rewrite window_linear, IH.
  replace (window b (fun y => cuts cs f (y-Z.of_nat c-1)) x)
    with (window b (fun y=> cuts cs f (y-(Z.of_nat c+1))) x)
    by (apply window_ext; intro y; f_equal; lia).
  rewrite window_shift, IH. f_equal. f_equal. lia.
Qed.
Lemma cuts_slide cs f h x :
   cuts cs (fun y=>f(y-h)) x = cuts cs f (x-h).
Proof.
  revert x; induction cs as [|c cs IH]; intro x; simpl; [reflexivity|].
  rewrite !IH. f_equal. f_equal. lia.
Qed.
Lemma cuts_sub cs f g x : cuts cs (fun y=>f y-g y) x = cuts cs f x-cuts cs g x.
Proof. revert x; induction cs; intro x; simpl; [reflexivity|rewrite !IHcs; ring]. Qed.
Lemma cuts_scale cs c f x : cuts cs (fun y=>c*f y) x = c*cuts cs f x.
Proof. revert x; induction cs; intro x; simpl; [reflexivity|rewrite !IHcs; ring]. Qed.
Lemma cuts_ext cs f g : (forall x, f x=g x) -> forall x, cuts cs f x=cuts cs g x.
Proof. intro E; induction cs; intro x; simpl; [apply E|rewrite !IHcs; reflexivity]. Qed.

Lemma count_one b x : latticeCount [b] x = cuts [b] (trunc 0) x.
Proof.
  change (window b (fun y=>if y =? 0 then 1 else 0) x= cuts [b] (trunc 0) x).
  transitivity (window b (fun y=>trunc 0 y - trunc 0 (y-1)) x).
  - apply window_ext; intro y. unfold trunc. simpl rise.
    destruct (y =? 0) eqn:E; destruct (y <? 0) eqn:F; destruct (y-1 <? 0) eqn:G;
    first [reflexivity| apply Z.eqb_eq in E | apply Z.eqb_neq in E];
    first [apply Z.ltb_lt in F|apply Z.ltb_ge in F];
    first [apply Z.ltb_lt in G|apply Z.ltb_ge in G]; lia.
  - apply window_diff.
Qed.

Theorem bounded_count_formula d caps : length caps = S d -> forall x,
   fac d * latticeCount caps x = cuts caps (trunc d) x.
Proof.
  revert caps; induction d as [|d IH]; intros caps H x; destruct caps as [|c cs]; try discriminate.
  - destruct cs; [rewrite count_one; cbn [fac]; ring|discriminate].
  - cbn [length] in H; injection H as H. cbn [fac latticeCount].
    rewrite <- Z.mul_assoc, <- window_scale.
    erewrite window_ext by (intro y; apply IH; exact H).
    rewrite window_cuts, <- cuts_scale.
    transitivity (cuts cs (fun y=>trunc (S d) y - trunc (S d) (y-(Z.of_nat c+1))) x).
    + apply cuts_ext. intro y. rewrite <- window_scale.
      transitivity (window c (fun z=>trunc (S d) z-trunc (S d) (z-1)) y).
      * apply window_ext; intro z; symmetry; apply trunc_step.
      * rewrite window_diff. f_equal. f_equal. lia.
    + rewrite cuts_sub, cuts_slide. change (cuts cs (trunc (S d)) x - cuts cs (trunc (S d)) (x-(Z.of_nat c+1)) = cuts cs (trunc (S d)) x -
        cuts cs (trunc (S d)) (x-Z.of_nat c-1)). f_equal. f_equal. lia.
Qed.

Lemma distinct_cons (i:nat) (ys:list (list nat)) :
  NoDup ys -> NoDup (map (cons i) ys).
Proof. induction 1; simpl; constructor; auto.
  intro Hx; apply in_map_iff in Hx as [y [E Hy]]. injection E as E; subst; auto.
Qed.

Theorem points_nodup cs t : NoDup (points cs t).
Proof.
  revert t; induction cs as [|b bs IH]; intro t; cbn [points].
  - destruct (t=?0); repeat constructor; simpl; tauto.
  - generalize (seq_NoDup (S b) 0). generalize (seq 0 (S b)). intros indices H.
    induction H as [|i indices Hout Hin Hrec]; simpl; [constructor|].
    apply NoDup_app; [apply distinct_cons, IH|exact Hrec|].
    intros p Hp Htail. apply in_map_iff in Hp as [xs [<- Hxs]].
    apply in_flat_map in Htail as [j [Hj Htail]]. apply in_map_iff in Htail as [ys [E _]].
    injection E as E F. subst; auto.
Qed.

(* Compress equal coordinate bounds into iterated differences in the index j. *)
Fixpoint iterDiff (n:nat) (f:nat->Z) (j:nat) : Z :=
 match n with O=>f j | S k=>iterDiff k f j - iterDiff k f (S j) end.

Lemma repeat_cuts n b f x j : cuts (repeat b n) f (x-Z.of_nat j*(Z.of_nat b+1)) =
 iterDiff n (fun k=>f(x-Z.of_nat k*(Z.of_nat b+1))) j.
Proof.
  revert j; induction n as [|n IH]; intro j; cbn [repeat cuts iterDiff]; [reflexivity|].
  rewrite <- !IH. f_equal. f_equal. rewrite Nat2Z.inj_succ. ring.
Qed.

Lemma repeat_cuts_zero n b f x : cuts (repeat b n) f x =
 iterDiff n (fun k=>f(x-Z.of_nat k*(Z.of_nat b+1))) O.
Proof. rewrite <- repeat_cuts. f_equal; ring. Qed.

Lemma rise_root d x : -Z.of_nat d <= x < 0 -> rise d x = 0.
Proof.
 induction d as [|d IH]; intro H; [lia|].
 cbn [rise]. destruct (Z.eq_dec x (-Z.of_nat (S d))) as [->|E].
 - ring.
 - rewrite IH by lia. ring.
Qed.
Lemma trunc_rise d x : -Z.of_nat d <= x -> trunc d x=rise d x.
Proof.
 intro H; unfold trunc. destruct (x <? 0) eqn:E; [|reflexivity].
 symmetry. apply rise_root; apply Z.ltb_lt in E; lia.
Qed.
Lemma trunc_negative d x : x < 0 -> trunc d x=0.
Proof. intro H; unfold trunc.
 destruct (x <? 0) eqn:E; [reflexivity|apply Z.ltb_ge in E; lia]. Qed.

Lemma cuts_app xs ys f x : cuts (xs++ys) f x = cuts xs (cuts ys f) x.
Proof. revert x; induction xs; intro x; simpl; [reflexivity|rewrite !IHxs; reflexivity]. Qed.
