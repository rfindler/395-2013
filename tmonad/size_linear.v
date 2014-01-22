Require Import Braun.tmonad.monad.
Require Import Braun.common.braun Braun.common.util.
Require Import Omega.

Section size_linear.
  Variable A : Set.

  Definition size_linear_result (bt : @bin_tree A) (n:nat) c := 
       n = c /\ (forall m, Braun bt m -> m = n).

  Load "size_linear_gen.v".

  Admit Obligations.

(*
  Next Obligation.
  Proof.
    split; [auto |].
    intros m B.
    invclr B.
    auto.
  Qed.

  Next Obligation.
  Proof.
    split; [omega|].
    intros m B. 
    invclr B.
    auto.
  Qed.
*)
End size_linear.
