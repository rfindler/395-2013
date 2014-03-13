Require Import Braun.tmonad.monad.

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
      0
    | S n' =>
      1 + n' + 2 * tln_time n'
  end.

Lemma tln_time_split:
  forall sn tn,
    tln_time sn + tln_time tn <= 2 * tln_time (sn + tn).
Proof.
  induction sn as [|sn]; simpl; intros tn.

  omega.
  assert (tln_time sn + tln_time tn <= 2 * tln_time (sn + tn)) as LE.
  auto. omega.
Qed.

(* COMMENT: This is a <= because s and t may not be equal in size, so
doubling is the wrong operation. Maybe if I used Braun-ness in the
correctness, then I could change the function to use something like
div2, but I'm not sure. *)

Program Fixpoint to_list_naive (A:Set) b :
  {! xs !:! list A
     !<! c !>!
     SequenceR b xs
   /\ c <= tln_time (length xs) !} :=
  match b with
    | bt_mt =>
      <== nil
    | bt_node x s t =>
      sl <- to_list_naive A s ;
      tl <- to_list_naive A t ;
      xs' <- cinterleave A sl tl ;
      += 1 ;
      <== (cons x xs')
  end.

Next Obligation.
  clear am0 H8 H9.
  clear am H10 H11.
  rewrite <- interleave_length_split.
  remember (length sl) as sn.
  remember (length tl) as tn.
  split; eauto.
  remember (sn + tn + 1) as p.
  replace (an1 + (an0 + p)) with
          (p + (an1 + an0)); try omega.
  replace (S (sn + tn + (tln_time (sn + tn) + (tln_time (sn + tn) + 0)))) with
          (p + 2 * tln_time (sn + tn)); try omega.
  apply Plus.plus_le_compat_l.
  apply Le.le_trans with (tln_time sn + tln_time tn); try omega.
  apply tln_time_split.
Qed.
