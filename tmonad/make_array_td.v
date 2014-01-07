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

(* XXX admit to automatically resolve wf *)
Lemma unravel_length_evens:
  forall A xs,
    length (fst (proj1_sig (unravel A xs))) <= length xs.
Proof.
Admitted.
Hint Resolve unravel_length_evens.

Lemma interleave_braun:
  forall A e o xs,
  xs = @interleave A e o ->
  length e <= length o <= length e + 1.
Proof.
Admitted.
Hint Resolve interleave_braun.

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
      let eoc := unravel A xs' in
      eo <- eoc ;
      oa <- make_array_td A (fst eo) ;
      ea <- make_array_td A (snd eo) ;
      <== (bt_node x oa ea)
  end.

Obligations.

(* XXX This is very interesting, Obligations 2 and 3 are wrong because
they drop the relation between eo and the argument, so I can't use
theorems about interleave. *)

Obligation 4.
 simpl in *.
 rename l into e. rename l0 into o.
 rename H into Be.
 rename H6 into SRe.
 rename H0 into Bo.
 rename H4 into SRo.
 clear make_array_td.
 remember (interleave e o) as xs.
 rename Heqxs into EQxs.
 rewrite EQxs.
 rewrite <- interleave_length_split.
 split; [|split].

 (* braun *)
 replace (S (length e + length o)) with (length e + length o + 1); try omega.
 eapply B_node; eauto.

 (* XXX running time *)
 admit.

 (* correctness *)
 eauto.
Qed.

Admit Obligations.
