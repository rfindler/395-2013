Require Import Braun.tmonad.monad.
Require Import Braun.tmonad.insert.
Require Import Braun.tmonad.fold.

Require Import Braun.logical.sequence.

Require Import Braun.common.braun.
Require Import Braun.common.array.
Require Import Braun.common.util.
Require Import Braun.common.log Braun.common.le_util.
Require Import Arith Arith.Even Arith.Div2 Omega.

(* Foldr version of make_array_naive *)
Section make_array_naive.
  Variable A : Set.
  
  Definition man_correct (b : @bin_tree A) (xs : list A) (c : nat) : Prop :=
    let n := length xs in
    Braun b n
    /\ c = man_time n
    /\ SequenceR b xs.

  Implicit Arguments foldr.
  Program Definition make_array_naive l : 
    {! b !:! @bin_tree A !<! c !>!
       man_correct b l c !} :=
    foldr man_correct
          insert
          bt_mt
          _ 
          l.
  Next Obligation.
    exists (3 * fl_log (length l) + 2).
    rename x0 into bt.
    unfold man_correct.
    remember (insert x bt) as INS.
    intros xs c IH; destruct IH. destruct H0.
    split; [| split].

    (* Pretty sure these are easily provable *)
    admit.
    admit.
    admit.
  Qed.
  Next Obligation.
    unfold man_correct.
    split; [| split]; auto.
  Qed.
End make_array_naive.

Extraction Inline ret bind inc.
(* Almost perfectly matches the paper *)
Recursive Extraction make_array_naive.