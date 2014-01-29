Require Import Braun.tmonad.monad Braun.common.big_oh.
Require Import Braun.common.braun Braun.common.util.
Require Import Omega.

Section size_linear.
  Variable A : Set.

  Definition size_linear_rt n : nat := 13 * n + 3.

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
    clear xm0 H2 xm H3.
    rename H0 into SLRr.
    rename H1 into SLRl.

    destruct SLRr as [XNeq Br].
    destruct SLRl as [XN0eq Bl].
    subst xn xn0.
    unfold size_linear_result.

    split.
    (* Need to figure out what this supposed to be first *)
    unfold size_linear_rt.
    omega.

    intros m B. 
    invclr B.
    auto.
  Qed.

  Theorem size_linear_rt_is_linear : big_oh size_linear_rt (fun n => n).
  Proof.
    exists 1.
    exists 16.
    intros n LE.
    unfold size_linear_rt.
    omega.
  Qed.

End size_linear.
