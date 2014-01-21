(*
  This file represents my current state as far as using
  the script to generate Coq code. The currently generated
  obligations are problematic (hence the admits below).

  I'm not sure if the fault is in the monad constructors
  or in the generated code (or both).
*)

Require Import Braun.common.braun Braun.common.util Braun.common.same_structure.
Require Import Braun.common.log Braun.logical.sequence Braun.logical.list_util.
Require Import Braun.tmonad.monad.
Require Import Program.
Require Import Omega.

Definition insert_result (A : Set) (i : A) (b:@bin_tree A)
           (b':@bin_tree A) c :=
     (forall n,
        Braun b n ->
        (Braun b' (S n) /\
         (forall xs, SequenceR b xs -> SequenceR b' (i::xs)) /\
         c = 9 * fl_log n + 6)).

Load "insert_gen.v".

Next Obligation.
  unfold insert_result.
  intros n B.
  invclr B.
  repeat constructor; auto.

  (* correctness *)
  intros xs SR.
  invclr SR.
  apply SR_singleton.
Qed.

Next Obligation.
  remember True as T.
  apply T.
Qed.

Next Obligation.
  admit.
Defined.

Lemma same_tree_same_size :
  forall A (s:@bin_tree A) n m,
    Braun s n ->
    Braun s m ->
    n = m.
Proof.
  intros A s n m Bn Bm.
  apply (@same_structure_same_size _ s s); eauto.
Qed.
Hint Rewrite same_tree_same_size.

Next Obligation.
  admit.
Qed.
