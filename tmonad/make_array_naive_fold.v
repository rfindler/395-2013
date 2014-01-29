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

  Program Definition make_array_naive l : 
    {! b !:! @bin_tree A !<! c !>!
       man_correct b l c !} :=
    foldr man_correct
          (fun x y => x <- insert x y; <== x)
          bt_mt
          _ 
          l.
  Next Obligation.
    clear xm H1.
    rename H into IR.
    rename H0 into MC.

    unfold insert_result in IR.
    destruct MC as [BRy [ACCCeq SR]].
    unfold man_correct.
    remember (IR (length xs) BRy) as IRlxs.
    destruct IRlxs as [BRx0 [SRimpl EQxn]].
    simpl.
    repeat split;auto.
    admit. (* running time; pending running time decision of fold *)
  Qed.
  Next Obligation.
    unfold man_correct.
    repeat split; auto.
    admit. (* running time; pending running time decision of fold *)
  Qed.
End make_array_naive.
