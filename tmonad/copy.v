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
    destruct n; [invclr H0; invclr H2|unfold div2; omega].
    apply lt_div2; omega.
  Qed.

  Next Obligation.
    (* even case *)

    split. 

    (* Braunness *)
    replace n with ((div2 n) + (div2 n - 1) + 1).
    constructor; try assumption. 
    split. 
    replace (div2 n - 1) with (pred (div2 n)); try omega.
    replace (div2 n - 1 + 1) with (div2 n); try constructor.
    destruct n as [|n']; [unfold not in H; assert (0 = 0)|]; try omega.
    assert (div2 (S n') <> 0). unfold not. intros.
    destruct n'. inversion H0. inversion H7. inversion H4. omega.
    rewrite even_double; try assumption. 
    unfold double.
    destruct n as [|n']; [unfold not in H; assert (0 = 0)|]; try omega.
    assert (div2 (S n') <> 0); try omega.
    unfold not. intros.
    destruct n'. inversion H0. inversion H7. inversion H4. 

    
    split.

    (* correct elems *)
    intros. inversion H4; eauto.

    (* running time *)
    destruct n as [|n']; [unfold not in H; assert (0 = 0)|]; try omega.
    WfExtensionality.unfold_sub rt_copy_fib (rt_copy_fib (S n')).
    destruct (even_odd_dec (S n')).
    repeat fold_sub rt_copy_fib. 
     
    rewrite plus_assoc. rewrite plus_comm. simpl.
    apply eq_S.
    destruct n'. inversion e. inversion H6. 
    replace (S (div2 n') - 1) with  (div2 (S n')). 
    reflexivity.
    replace (S (div2 n') - 1) with (div2 n').
    
    inversion e. inversion H6.
    symmetry. apply even_div2. assumption. omega.

    apply not_even_and_odd in H0. contradiction. assumption.
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
    intros; inversion H3; auto. eapply H2. apply H9. eapply H2. apply H9.

    (* running time *)
    destruct n as [|n']; [unfold not in H; assert (0 = 0)|]; try omega.
    WfExtensionality.unfold_sub rt_copy_fib (rt_copy_fib (S n')).
    destruct (even_odd_dec (S n')).
    apply not_even_and_odd in e. contradiction. assumption.
    fold_sub rt_copy_fib. 
    destruct n'. compute. reflexivity.
    rewrite <- even_div2.
    rewrite odd_div2. omega.
    inversion o. inversion H4. assumption.
    inversion o. assumption.
Qed.

End copy_fib.

Section copy2.

  Variable A:Set.
  Variable x:A.

  Definition copy_rt n := cl_log (n + 1) + fl_log n.
  Lemma copy_rt_Sn : forall n, copy_rt (div2 n) + 2 = copy_rt (n + 1).
  Proof.
    intros n.
    unfold copy_rt.
    replace (n+1+1) with (S (n+1));[|omega].
    replace (n+1) with (S n);[|omega].
    rewrite <- fl_log_div2.
    rewrite cl_log_div2'.
    replace (div2 (S (S n))) with (div2 n+1); [|simpl;omega].
    omega.
  Qed.


  Program Fixpoint copy2 (n:nat) {wf lt n}
  :  {! pr !:! bin_tree * bin_tree !<! c !>! 
      let (s,t) := pr in
      Braun s (n+1) /\
      Braun t n /\
      (forall i y, IndexR s i y -> y = x) /\
      (forall i y, IndexR t i y -> y = x) /\
      c = copy_rt n !} :=
    match n with 
      | 0 => (++ ; <== (bt_node x bt_mt bt_mt, bt_mt))
      | S n' => 
        pr <- (copy2 (div2 n'));
          match pr with
            | (s,t) =>
              if (even_odd_dec n')
              then ( ++; ++; <== (bt_node x s t, bt_node x t t))
              else ( ++; ++; <== (bt_node x s s, bt_node x s t))
          end
    end.

  Next Obligation.
  Proof.
    (* zero case *)
    replace 1 with (0+0+1);[|omega].
    split; [|split]; try repeat constructor; 
    (* proof of correct elems *)
    intros i y IR; invclr IR.
    auto.
    invclr H4.
    invclr H4.
  Qed.

  Next Obligation.
  Proof. 
    (* even case *)
    apply even_double in H; unfold double in H.

    (* proof of braun preservation *)
    replace (S (n'+1)) with ((div2 n' + 1)+(div2 n')+1);[|omega].
    replace (S n') with (div2 n' + div2 n' + 1);[|omega].
    repeat constructor; try omega; try assumption.

    (* proof of correct elems *)
    intros i y IR. clear H. invclr IR; eauto.
    intros i y IR. clear H. invclr IR; eauto.

    (* proof of running time *)
    rewrite <- H.
    apply copy_rt_Sn.
  Qed.

  Next Obligation.
  Proof.
    (* odd case *)
    apply odd_double in H; unfold double in H.

    (* proof of braun preservation *)
    replace (S (n'+1)) with ((div2 n'+1) + (div2 n'+1) + 1);[|omega].
    replace (S n') with ((div2 n'+1) + (div2 n') + 1);[|omega].
    repeat constructor; try omega; try assumption.

    (* proof of correct elems *)
    intros i y IR. clear H. invclr IR; eauto.
    intros i y IR. clear H. invclr IR; eauto.

    (* proof of running time *)
    replace (div2 n' + 1 + div2 n' + 1) with (n'+1);[|omega].
    apply copy_rt_Sn.
  Qed.

  Program Definition copy (n:nat)
  :  {! b !:! bin_tree !<! c !>!  
        Braun b n /\ 
        (forall i y, IndexR b i y -> y = x) /\
        c = copy_rt n !} := 
    c <- (copy2 n) ;
    match c with
      | (t1,t2) => <== t2
    end.

End copy2.
