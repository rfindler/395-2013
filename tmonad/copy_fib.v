Require Import Braun.tmonad.monad Braun.logical.index.
Require Import Braun.common.braun Braun.common.log Braun.common.util.
Require Import Arith Arith.Even Arith.Div2 Omega.
Require Import Program.Wf.

Set Implicit Arguments.


Section copy_fib.

  Variable A : Set.
  Variable x : A.

  Program Fixpoint fib (n : nat) {measure n} : nat :=
    match n with
      | 0 => 0
      | 1 => 1
      | (S (S n')) => fib (S n') + fib n'
    end.

  Program Fixpoint rt_copy_fib (n : nat) {measure n}: nat :=
    match n with 
      | 0 => 1
      | (S n') => if (even_odd_dec n)
                  then (S ((rt_copy_fib (div2 n)) + (rt_copy_fib (div2 n'))))
                  else (S (rt_copy_fib (div2 n)))
    end. 

  Program Fixpoint copy_fib (n : nat) {measure n}
  : {! t !:! bin_tree !<! c !>!
     Braun t n /\
     (forall i y, IndexR t i y -> y = x) /\
     c = rt_copy_fib n!} :=
    match n with
      | 0 => (++ ; <== bt_mt)
      | _ => if (even_odd_dec n)
             then (l <- (copy_fib (div2 n));
                   r <- (copy_fib ((div2 n) - 1));
                   ++; <== (bt_node x l r))
             else (t <- (copy_fib (div2 n));
                   ++; <== (bt_node x t t))
      end.

  Next Obligation.
  Proof.
    split. constructor.
    split. intros i y H. inversion H.
    compute. reflexivity.
  Qed.

  Next Obligation.
    apply lt_div2. 
    induction n; [unfold not in H; assert (0 = 0)|]; omega.
  Qed.

  Next Obligation.
    destruct n;  [unfold not in H; assert (0 = 0)|]; try omega.
    apply lt_trans with (m := div2 (S n)).
    replace (div2 (S n) - 1) with (pred (div2 (S n))); try omega.
    apply lt_pred_n_n.
    destruct n; [invclr H0; invclr H4|unfold div2; omega].
    apply lt_div2. omega.
  Qed.

  Next Obligation.
    (* even case *)
    rename H0 into E.
    rename H10 into Bl.
    rename H11 into IRl.
    rename H7 into Br.
    rename H8 into IRr.
    clear H1 H5 H2 H3.
    rename H into NEQ.

    split. 

    (* Braunness *)
    replace n with ((div2 n) + (div2 n - 1) + 1).
    constructor; try assumption. 
    split. 
    replace (div2 n - 1) with (pred (div2 n)); try omega.
    replace (div2 n - 1 + 1) with (div2 n); try constructor.
    destruct n as [|n']; [unfold not in NEQ; assert (0 = 0)|]; try omega.
    assert (div2 (S n') <> 0) as NEQ'. unfold not. intros NEQ'.
    destruct n'; simpl in NEQ'. invclr E. rename H0 into O. invclr O. invclr NEQ'.
    omega.
    rewrite even_double; try assumption. 
    unfold double.
    destruct n as [|n']; [unfold not in NEQ; assert (0 = 0)|]; try omega.
    assert (div2 (S n') <> 0); try omega.
    unfold not. intros EQ.
    destruct n'. inversion E. rename H0 into O. inversion O. 
    inversion EQ.

    split.

    (* correct elems *)
    intros i y IR. inversion IR; eauto.

    (* running time *)
    destruct n as [|n']; [unfold not in NEQ; assert (0 = 0)|]; try omega.
    WfExtensionality.unfold_sub rt_copy_fib (rt_copy_fib (S n')).
    destruct (even_odd_dec (S n')).
    repeat fold_sub rt_copy_fib. 
     
    rewrite plus_assoc. rewrite plus_comm. simpl.
    apply eq_S.
    destruct n'. inversion e. inversion H0. 
    replace (S (div2 n') - 1) with  (div2 (S n')). 
    reflexivity.
    replace (S (div2 n') - 1) with (div2 n').
    
    inversion e. inversion H0.
    symmetry. apply even_div2. assumption. omega.

    apply not_even_and_odd in E. contradiction. assumption.
  Qed.    

  Next Obligation.
    apply lt_div2. destruct n. inversion H0. omega.
  Qed.

  Next Obligation.
    (* odd case *)

    split. 
    
    (* Braunness *)
    replace n with ((div2 n) + (div2 n) + 1). 
    constructor; try assumption.
    split; [constructor | intuition].
    rewrite odd_double; try assumption. 
    unfold double. rewrite plus_comm. omega.
    
    split.

    (* correct elems *)
    intros; inversion H3; auto. eapply H2. apply H11. eapply H2. apply H11.

    (* running time *)
    destruct n as [|n']; [unfold not in H; assert (0 = 0)|]; try omega.
    WfExtensionality.unfold_sub rt_copy_fib (rt_copy_fib (S n')).
    destruct (even_odd_dec (S n')).
    apply not_even_and_odd in e. contradiction. assumption.
    fold_sub rt_copy_fib. 
    destruct n'. compute. reflexivity.
    rewrite <- even_div2.
    rewrite odd_div2. omega.
    inversion o. inversion H6. assumption.
    inversion o. assumption.
Qed.
End copy_fib.
