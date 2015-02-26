Require Import Braun.monad.monad.

Require Import Braun.common.sequence.
Require Import Braun.common.list_util.

Require Import Braun.common.braun.
Require Import Braun.common.util.

(* This is a hack way to simply declare how expensive a function is *)

Program Fixpoint cinterleave (A:Set) (e:list A) (o:list A) :
  {! xs !:! list A
     !<! c !>!
     xs = interleave e o
   /\ c = (length e) + (length o) !} :=
  interleave e o.

Next Obligation.
  eauto.
Qed.

Fixpoint tln_time n :=
  match n with
    | O =>
      3
    | S n' =>
      15 + n' + 2 * tln_time n'
  end.

Lemma tln_time_bigger:
  forall tn,
    3 <= tln_time tn.
Proof.
  induction tn as [|tn]; simpl; omega.
Qed.

Lemma tln_time_split:
  forall sn tn,
    tln_time sn + tln_time tn <= 2 * tln_time (sn + tn).
Proof.
  induction sn as [|sn]; simpl; intros tn.
  remember (tln_time_bigger tn) as P. omega.

  assert (tln_time sn + tln_time tn <= 2 * tln_time (sn + tn)) as LE.
  auto. omega.
Qed.

(* COMMENT: This is a <= because s and t may not be equal in size, so
doubling is the wrong operation. Maybe if I used Braun-ness in the
correctness, then I could change the function to use something like
div2, but I'm not sure. *)

Definition to_list_naive_result (A:Set) b (xs:list A) (c:nat) :=
  SequenceR b xs
  /\ c <= tln_time (length xs).

Load "to_list_naive_gen.v".

Next Obligation.
Proof.
  unfold to_list_naive_result. simpl.
  split. eauto. auto.
Qed.

Next Obligation.
Proof.
  clear am0 H7 am H6.
  unfold to_list_naive_result in *.
  destruct H1 as [SEQt ANt].
  destruct H2 as [SEQs ANs].
  clear H0. simpl length.
  rewrite <- interleave_length_split.
  remember (length sl) as sn.
  remember (length tl) as tn.
  split; eauto.
  clear SEQs SEQt A x s t sl tl Heqtn Heqsn.
  remember (sn + tn + 15) as p.
  replace (an1 + (an0 + p)) with
          (p + (an1 + an0)); try omega.
  replace (tln_time (S (sn + tn))) with
          (p + 2 * tln_time (sn + tn)); try (simpl; omega).
  apply Plus.plus_le_compat_l.
  apply Le.le_trans with (tln_time sn + tln_time tn); try omega.
  apply tln_time_split.
Qed.
