Require Import Braun.tmonad.monad.
Require Import Braun.tmonad.insert.

Require Import Braun.logical.sequence.
Require Import Braun.logical.list_util.

Require Import Braun.common.braun.
Require Import Braun.common.array.
Require Import Braun.common.util.
Require Import Braun.common.log.

Definition unravel_prop (A:Set) (xs:list A) (eo:((list A) * (list A))) :=
  let (e, o) := eo in
  xs = interleave e o 
  /\ length o <= length e <= length o + 1.
Hint Unfold unravel_prop.

Program Fixpoint unravel (A:Set) (xs:list A) :
  {! eo !:! ((list A) * (list A))
     !<! c !>!
     unravel_prop A xs eo
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
  destruct H as [EQ BP]. subst.
  split; [split|]; try omega.
  apply interleave_case2.
Qed.

(* XXX This proof, and the need for it, stinks. *)

Theorem unravel' (A:Set) (xs:list A) :
  {! eo !:! (sig (unravel_prop A xs))
     !<! c !>!
     c = length xs !}.
Proof.
  destruct (unravel A xs) as [[e o] P].
  assert (unravel_prop A xs (e,o)) as UP; eauto.
  destruct P as [n [[P_EQ P_BP] P_len]]; eauto.
Defined.

(* COMMENT: Here's what is going on: 

Suppose that (unravel A xs') were used and the name we give to it is
eoc. If we write (fst eoc), then Program will change

let eoc := ... in

into

let eoc := (_0 ...) in

and infer an obligation that we can transform the monad result into a
"fst"-able thing. This proof is easy (proj1_sig). The problem, though,
is that this makes it so when we do

recursive_call (fst eoc)

then recursive_call gets to see the result of the inference on _0,
which has lost the property that was in proj2_sig, which is what
justifies recursion based on the measure.

The trick I've pulled here is to transform

(sig A (P1 /\ P2))

into

(sig (sig A P1) P2)

so that only one thing gets pulled out.

Neither version interferes with proving correctness, however. This
seems to /not/ be a problem with the monad definition, but an
annoyance of Program's default rules for constructing measure
contexts. Maybe there's a way to change the monad to get in the way of
these rules, but I'm worried that it would be too invasive.

One idea is that this version of unravel is more pure because it looks
like:

(sig (sig ResultType CorrectCondition) (exists nat : TimeCondition))

This pushes the CorrectCondition outside of "exists nat" and
modularizes the two pieces. Maybe we should change the monad to
require these two pieces separately.

*)

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
      eo <- unravel' A xs' ;
      oa <- make_array_td A (fst eo) ;
      ea <- make_array_td A (snd eo) ;
      ++ ; 
      <== (bt_node x oa ea)
  end.

Next Obligation.
  destruct H as [EQ BP]. subst.
  simpl. rewrite <- interleave_length_split.
  omega.
Qed.

Next Obligation.
  destruct H as [EQ BP]. subst.
  simpl. rewrite <- interleave_length_split.
  omega.
Qed.
 
Next Obligation.
  destruct H6 as [EQ BP]. subst.
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
