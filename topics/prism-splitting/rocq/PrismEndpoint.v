From Stdlib Require Import ZArith List Lia Ring.
From OpenMath Require Import BoundedCompositions FiniteDifferences.
Import ListNotations.
Open Scope Z_scope.

Definition unsplit (t:nat) := repeat t 10 ++ [(2*t)%nat].
Definition split (t:nat) := repeat t 12.
Definition P : list Z := [1;661;31846;312146;927706;960774;347986;38686;901;1].
Definition Q : list Z := [1;912;62767;878932;3834832;6169360;3834832;878932;62767;912;1].

Lemma difference10 f : iterDiff 10 f O =
 1*f 0%nat -10*f 1%nat +45*f 2%nat -120*f 3%nat +210*f 4%nat
  -252*f 5%nat +210*f 6%nat -120*f 7%nat +45*f 8%nat -10*f 9%nat
  +1*f 10%nat.
Proof. cbn [iterDiff]; ring. Qed.

Lemma difference12 f : iterDiff 12 f O =
 1*f 0%nat -12*f 1%nat +66*f 2%nat -220*f 3%nat +495*f 4%nat
  -792*f 5%nat +924*f 6%nat -792*f 7%nat +495*f 8%nat -220*f 9%nat
  +66*f 10%nat -12*f 11%nat +1*f 12%nat.
Proof. cbn [iterDiff]; ring. Qed.

(* Name the arbitrary dilation before evaluating the finitely many
   literal indices. Each truncated product either vanishes or is polynomial. *)
Ltac certify_expansion t :=
 remember (Z.of_nat t) as T;
 assert (0 <= T) by lia;
 repeat match goal with
 | |- context[Z.of_nat ?n] => is_ground n;
        let k := (eval vm_compute in (Z.of_nat n)) in change (Z.of_nat n) with k
 end;
 repeat first [rewrite trunc_negative by lia | rewrite trunc_rise by lia];
 cbn [rise]; ring.

Theorem unsplit_expansion (t:nat) :
 fac 10 * latticeCount (unsplit t) (6*Z.of_nat t) = combination 10 P (Z.of_nat t).
Proof.
 rewrite bounded_count_formula by (unfold unsplit; rewrite length_app, repeat_length; reflexivity).
 unfold unsplit. rewrite cuts_app, repeat_cuts_zero, difference10.
 cbn [cuts]. rewrite Nat2Z.inj_mul. unfold P; cbn [combination].
 certify_expansion t.
Qed.

Theorem split_expansion (t:nat) :
 fac 11 * latticeCount (split t) (6*Z.of_nat t) = combination 11 Q (Z.of_nat t).
Proof.
 rewrite bounded_count_formula by (unfold split; rewrite repeat_length; reflexivity).
 unfold split. rewrite repeat_cuts_zero, difference12. unfold Q; cbn [combination].
 certify_expansion t.
Qed.

Theorem unsplit_full_series : numerator 11 6 unsplit P.
Proof. apply (normalize_counts 10), unsplit_expansion. Qed.
Theorem split_full_series : numerator 12 6 split Q.
Proof. apply (normalize_counts 11), split_expansion. Qed.
