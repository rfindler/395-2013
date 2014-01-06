Require Import Braun.tmonad.monad.
Require Import Braun.tmonad.insert.

Require Import Braun.logical.sequence.

Require Import Braun.common.braun.
Require Import Braun.common.array.

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
      | nil      => bt_mt
      | (cons x xs') => ++ ;
                       bt <- make_array_naive xs';
                       insert x bt
    end.

  Next Obligation.
  Proof.
    exists 0; auto.
  Qed.
  Next Obligation.
  Proof.
    exists (log.fl_log (length xs')).
    intros.
    destruct H as [HBraun H2]; destruct H2 as [HTime HCorrect].

    split; [| split].
    (* Satisfies Braun Invariant  *)
    admit.

    (* Has man_time running time *)
    admit.

    (* Represents the original list *)
    admit.
  Qed.
End make_array_naive.
