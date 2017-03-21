Require Import Braun.monad.monad Braun.common.big_oh.
Require Import Braun.common.braun Braun.common.util.
Require Import Omega.

Section size_linear.
  Variable A : Set.

  Definition size_linear_rt n : nat := 13 * n + 3.

  Definition size_linear_result (bt : @bin_tree A) (res:nat) c :=
    c = size_linear_rt res /\
    (forall m,
       Braun bt m ->
       m = res).

  (* the blank line above is important for the paper to build *)
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
    clear am0 H2 am H3.
    rename H0 into SLRr.
    rename H1 into SLRl.

    destruct SLRr as [XNeq Br].
    destruct SLRl as [XN0eq Bl].
    subst an an0.

    split.
    unfold size_linear_rt.
    omega.

    intros m B. 
    invclr B.
    auto.
  Qed.

  Theorem size_linear_rt_is_linear : big_oh size_linear_rt (fun n => n).
  Proof.
    unfold size_linear_rt; auto.
  Qed.

End size_linear.
