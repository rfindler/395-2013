Require Import Braun.tmonad.monad.
Require Import Braun.common.braun Braun.common.util.
Require Import Omega.

Section size_linear.
  Variable A : Set.

  Program Fixpoint size_linear (bt : @bin_tree A) : 
    {! n !:! nat !<! c !>!
       n = c /\ (forall m, Braun bt m -> m = n) !} :=
    match bt with
      | bt_mt =>
        <== 0
      | bt_node x l r =>
        ++ ;
          lsize <- size_linear l;
          rsize <- size_linear r;
          <== lsize + rsize + 1
    end.
  Next Obligation.
  Proof.
    split; [auto |].
    intros m B.
    invclr B.
    auto.
  Qed.
  Next Obligation.
    split; [omega|].
    intros m B. invclr B.
    apply H1 in H8.
    apply H2 in H9.
    subst. auto.
  Qed.
End size_linear.
