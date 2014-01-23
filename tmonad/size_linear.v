Require Import Braun.tmonad.monad.
Require Import Braun.common.braun Braun.common.util.
Require Import Omega.

Section size_linear.
  Variable A : Set.

  Definition size_linear_rt n : nat :=
    match n with 
      | 0   => 3
      (* Placeholder, Obviously wrong! *)
      | S n => 0
    end.

  Definition size_linear_result (bt : @bin_tree A) (n:nat) c :=
    c = size_linear_rt n /\ (forall m, Braun bt m -> m = n).

  Load "size_linear_gen.v".

  Next Obligation.
  Proof.
    split; [auto |].
    intros m B.
    invclr B.
    auto.
  Qed.

  Next Obligation.
  Proof.
    (* Why are there duplicated premises? 
  A : Set
  x : A
  l : bin_tree
  r : bin_tree
  lsize : nat
  xm : nat
  H3 : size_linear_result l lsize xm
  rsize : nat
  xm0 : nat
  H2 : size_linear_result r rsize xm0
  xn : nat
  H0 : size_linear_result r rsize xn
  xn0 : nat
  H1 : size_linear_result l lsize xn0
  ============================
   size_linear_result (bt_node x l r) (lsize + rsize + 1) (xn0 + (xn + 10))
     *)
    

    split.
    (* Need to figure out what this supposed to be first *)
    admit.

    intros m B. 
    invclr B.
    destruct H2; destruct H3.
    auto.
  Qed.
End size_linear.
