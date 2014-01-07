Require Import Braun.tmonad.monad.
Require Import Braun.tmonad.insert.

Require Import Braun.logical.sequence.

Require Import Braun.common.braun.
Require Import Braun.common.array.
Require Import Braun.common.util.
Require Import Braun.common.log.

Section make_array_naive.
  Variable A : Set.

  Program Fixpoint make_array_naive xs : 
    {! b !:! @bin_tree A
       !<! c !>!
       let n := length xs in
       Braun b n
       /\ c = man_time n
       /\ SequenceR b xs !} :=
    match xs with
      | nil      => 
        <== bt_mt
      | (cons x xs') => 
        bt  <- make_array_naive xs';
        bt' <- insert x bt;
        <== bt'  
    end.

  Next Obligation.
  Proof.
    remember (H (length xs') H0) as IND.
    destruct IND as [BT [SEQ XN]].
    repeat constructor; auto.
    
    assert (xn = cl_log (S (length xs'))); [| omega].
    remember (H (length xs') H0).
    subst.
    assert (fl_log (length xs') + 1 = S (fl_log (length xs'))); [omega | ].
    rewrite H1.
    apply fl_log_cl_log_relationship.
    
  Qed.
End make_array_naive.
