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

(* XXX This proof, and the need for it, stinks. *)

Theorem unravel' (A:Set) (xs:list A) :
  {! eo !:! (sig (fun eo => xs = interleave (fst eo) (snd eo)))
     !<! c !>!
     c = length xs !}.
Proof.
  destruct (unravel A xs) as [[e o] P].
  simpl in *.
  assert (xs = interleave e o) as EQ.

  destruct P as [n [P_EQ P_len]]; eauto.

  assert { eo | xs = interleave (fst eo) (snd eo) } as ANS.
  exists (e,o). simpl. auto.

  exists ANS.
  destruct P as [n [P_EQ P_len]]; eauto.
Defined.

Lemma interleave_both:
  forall (A:Set) (e:list A) o,
    length e < S (length (interleave e o))
    /\ length o < S (length (interleave e o)).
Proof.
  intros A. induction e as [|e]; intros o.

  rewrite interleave_nil2.
  simpl. omega.

  rewrite <- interleave_case2.
  simpl.
  rewrite <- interleave_length_swap.
  destruct (IHe o). omega.
Qed.
Hint Resolve interleave_both.

Lemma interleave_braun:
  forall A e o xs,
  xs = @interleave A e o ->
  length e <= length o <= length e + 1.
Proof.
  intros A. induction e as [|e]; intros o xs EQ.

  rewrite interleave_nil2 in *. subst xs.
  simpl. 
Admitted.
Hint Resolve interleave_braun.

Lemma interleave_evens:
  forall (A:Set) (e:list A) o,
    length e < S (length (interleave e o)).
Proof.
  intros A e o. destruct (interleave_both A e o). auto.
Qed.
Hint Resolve interleave_evens.

Lemma interleave_odds:
  forall (A:Set) (e:list A) o,
    length o < S (length (interleave e o)).
Proof.
  intros A e o. destruct (interleave_both A e o). auto.
Qed.
Hint Resolve interleave_odds.

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
      eo <- (unravel' A xs') ;
      oa <- make_array_td A (fst eo) ;
      ea <- make_array_td A (snd eo) ;
      <== (bt_node x oa ea)
  end.

Next Obligation.
  simpl. auto.
Qed.

Next Obligation.
  simpl. auto.
Qed.
 
Next Obligation.
 simpl in *.
 rename l into e. rename l0 into o.
 rename H into Be.
 rename H5 into SRe.
 rename H0 into Bo.
 rename H3 into SRo.
 clear make_array_td.
 remember (interleave e o) as xs.
 rename Heqxs into EQxs.
 rewrite EQxs.
 rewrite <- interleave_length_split.
 split; [|split].

 (* braun *)
 replace (S (length e + length o)) with (length e + length o + 1); try omega.
 eapply B_node.

 (* XXX running time *)
 admit.

 (* correctness *)
 eauto.
Qed.
