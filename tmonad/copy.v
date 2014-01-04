Require Import Braun.tmonad.monad Braun.logical.index.
Require Import Braun.common.braun Braun.common.log Braun.common.util.
Require Import Arith Arith.Even Arith.Div2 Omega.

Set Implicit Arguments.

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
