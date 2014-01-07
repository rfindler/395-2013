Require Import Braun.tmonad.monad.

Require Import Braun.logical.sequence.
Require Import Braun.logical.list_util.

Require Import Braun.common.braun.

(* This is a hack way to simply declare how expensive a function is *)

Program Fixpoint cinterleave (A:Set) (e:list A) (o:list A) :
  {! xs !:! list A
     !<! c !>!
     xs = interleave e o
   /\ c = length xs !} :=
  interleave e o.

Next Obligation.
  exists (length (interleave e o)).
  auto.
Qed.

Program Fixpoint to_list_naive (A:Set) b :
  {! xs !:! list A
     !<! c !>!
     SequenceR b xs
   /\ c = 2 * (length xs) !} :=
  match b with
    | bt_mt =>
      <== nil
    | bt_node x s t =>
      sl <- to_list_naive A s ;
      tl <- to_list_naive A t ;
      xs' <- cinterleave A sl tl ;
      ++ ;
      <== (cons x xs')
  end.

Next Obligation.
  rename H0 into SRt.
  rename H1 into SRs.
  rewrite <- interleave_length_split.
  split. eauto.
  remember (length sl) as sn.
  remember (length tl) as tn.

  (* xxx this just isn't right *)
  admit.
Qed.
