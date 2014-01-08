Require Import Braun.tmonad.monad.

Require Import Braun.logical.sequence.
Require Import Braun.logical.list_util.

Require Import Braun.common.braun.
Require Import Braun.common.array.
Require Import Braun.common.util.
Require Import Braun.common.log.

Program Fixpoint unravel (A:Set) (xs:list A) :
  {! eo !:! ((list A) * (list A))
     !<! c !>!
     let (e, o) := eo in
     xs = interleave e o 
     /\ length o <= length e <= length o + 1
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
  simpl.
  rewrite interleave_case2.
  split. auto. omega.
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
      oa <- make_array_td A (fst eo) ;
      ea <- make_array_td A (snd eo) ;
      ++ ; 
      <== (bt_node x oa ea)
  end.

Next Obligation.
  simpl. rewrite <- interleave_length_split.
  omega.
Qed.

Next Obligation.
  simpl. rewrite <- interleave_length_split.
  omega.
Qed.
 
Next Obligation.
  simpl in *.
  rename l into e. rename l0 into o.
  rewrite <- interleave_length_split.
  split; [|split].

  (* braun *)
  replace (S (length e + length o)) with (length e + length o + 1); try omega.
  eauto.

  (* running time *)
  rewrite <- braun_implies_mat_time; omega.

  (* correctness *)
  eauto.
Qed.
