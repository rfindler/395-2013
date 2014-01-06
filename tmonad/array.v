Require Import Braun.tmonad.monad.
Require Import Braun.tmonad.insert.

Require Import Braun.logical.sequence.

Require Import Braun.common.braun.
Require Import Braun.common.array.
Require Import Braun.common.util.
Require Import Braun.common.log.

Section make_array_naive.
  Variable A : Set.

  Program Fixpoint make_array_naive xs : {! b !:! @bin_tree A
                                            !<! c !>!
                                            let n := length xs in
                                            Braun b n
                                            /\ c = man_time n
                                            /\ SequenceR b xs
                                         !} :=
    match xs with
      | nil      => <== bt_mt
      | (cons x xs') => ++ ;
                       bt <- make_array_naive xs';
                       i <- insert x bt;
                       <== i
    end.

  Next Obligation.
  Proof.
    remember (H (length xs') H0) as IND.
    destruct IND as [BT [SEQ XN]].
    repeat constructor; auto.
    admit.
  Qed.
End make_array_naive.
