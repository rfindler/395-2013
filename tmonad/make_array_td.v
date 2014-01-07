Require Import Braun.tmonad.monad.
Require Import Braun.tmonad.insert.

Require Import Braun.logical.sequence.
Require Import Braun.logical.list_util.

Require Import Braun.common.braun.
Require Import Braun.common.array.
Require Import Braun.common.util.
Require Import Braun.common.log.

Program Fixpoint unravel (A:Set) (xs:list A) :
  {! eo !:! ((list A) * (list A))
     !<! c !>!
     xs = interleave (fst eo) (snd eo) 
   /\ c = length xs !} :=
  match xs with
    | nil =>
      <== (nil, nil)
    | (cons x xs') =>
      moe <- unravel A xs' ;
      ++ ;
      <== ( (cons x (snd moe)), (fst moe) )
  end.

Next Obligation.
  simpl. rename l into e. rename l0 into o.
  split; try omega.
  apply interleave_case2.
Qed.

Program Fixpoint make_array_td (A:Set) xs {measure (length xs)} :
  {! b !:! @bin_tree A
     !<! c !>!
     let n := length xs in
     Braun b n
     /\ c = mat_time n
     /\ SequenceR b xs !} :=
  match xs with
    | nil      =>
      <== bt_mt
    | (cons x xs') =>
      eo <- unravel A xs' ;
      oa <- make_array_td A (snd eo) ;
      ea <- make_array_td A (fst eo) ;
      <== (bt_node x oa ea)
  end.

Obligations.

(* XXX This is very interesting, Obligations 2 and 3 are wrong because
they drop the relation between eo and the argument, so I can't use
theorems about interleave. *)

Admit Obligations.
