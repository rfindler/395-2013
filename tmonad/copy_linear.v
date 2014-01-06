Require Import Braun.tmonad.monad Braun.logical.index Braun.tmonad.insert.
Require Import Braun.common.braun Braun.common.util.
Require Import Arith Arith.Even Arith.Div2 Omega.
Require Import Program.Wf.

Set Implicit Arguments.

Section copy_linear.

  Variable A : Set.
  Variable x : A.

  Program Fixpoint copy_linear (n:nat) {wf lt n}
  :  {! b !:! bin_tree !<! c !>!  
        Braun b n /\ 
        (forall i y, IndexR b i y -> y = x) /\
        c = n !} := 
    match n with 
      | 0 => <== bt_mt
      | S n' => 
        (l <- copy_linear (div2 n);
         r <- copy_linear (div2 n');
         ++;
         <== (bt_node x l r))
    end.

  Next Obligation.
  Proof.
    repeat constructor;auto.
    intros i y IR.
    inversion IR.
  Qed.

  Next Obligation.
  Proof.
    repeat constructor; auto.
    replace (S n') with (div2 (S n')+ div2(n') + 1).
    repeat constructor;auto.

    apply (ind_0_1_SS (fun n' =>  div2 (S n') <= div2 n' + 1));auto;try (simpl;omega).
    intros n IND.
    replace (div2 (S (S (S n)))) with (S (div2 (S n)));[|auto].
    replace (div2 (S (S n))) with (S (div2 n));[|auto].
    replace (S (div2 n) + 1) with (S (div2 n + 1));[|omega].
    apply le_n_S.
    assumption.

    rewrite (div_ceil_floor_sum n') at 3.
    replace (n'+1) with (S n');[|omega].
    omega.
    
    intros i y IR. invclr IR; eauto.

    rewrite (div_ceil_floor_sum n') at 3.
    replace (n'+1) with (S n');[|omega].
    omega.
Qed.

End copy_linear.
