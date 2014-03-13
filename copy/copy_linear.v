Require Import Braun.tmonad.monad Braun.common.index Braun.insert.insert_log.
Require Import Braun.common.braun Braun.common.util Braun.common.big_oh.
Require Import Arith Arith.Even Arith.Div2 Omega.
Require Import Program.Wf.

Section copy_linear.

  Definition copy_linear_time (n:nat) := 17*n+3.

  Definition copy_linear_result (A:Set) (x:A) (n:nat) (b:@bin_tree A) (c:nat):=
    Braun b n /\ 
    (forall i y, IndexR b i y -> y = x) /\
    c = copy_linear_time (n).

  Load "copy_linear_gen.v".

  Next Obligation.
  Proof.
    repeat constructor;auto.
    intros i y IR.
    inversion IR.
  Qed.

  Next Obligation.
  Proof.
    clear H2 am0 H3 am. 
    destruct H0 as [Br [IRr EQxn]].
    destruct H1 as [Bl [IRl EQxn0]].

    unfold copy_linear_result.
    subst.

    repeat split; auto.

    replace (S n') with (div2 (S n')+ div2(n') + 1).
    repeat constructor;auto.

    rewrite (div_ceil_floor_sum n') at 3.
    replace (n'+1) with (S n');[|omega].
    omega.
    
    intros i y IR. invclr IR; eauto.

    unfold copy_linear_time.
    replace (17 * div2 (S n') + 3 + (17 * div2 n' + 3 + 14))
    with (17 * (div2 n' + div2 (n'+1)) + 20).
    rewrite <- (div_ceil_floor_sum n').
    omega.
    
    rewrite mult_plus_distr_l.
    replace (S n') with (n'+1); omega.
  Qed.

  Theorem copy_linear_linear : big_oh copy_linear_time (fun n => n).
  Proof.
    unfold copy_linear_time; auto.
  Qed.
  
End copy_linear.
