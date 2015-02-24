Require Import Braun.monad.monad Braun.common.index.
Require Import Braun.common.braun Braun.common.log Braun.common.util.
Require Import Braun.common.big_oh Braun.common.le_util.
Require Import Braun.fib.fib.
Require Import Arith Arith.Even Arith.Div2 Omega.
Require Import Program.Wf Init.Wf.

Include WfExtensionality.

Set Implicit Arguments.

Section copy_fib.

  Variable A : Set.

  Program Fixpoint rt_copy_fib (n : nat) {measure n}: nat :=
    match n with 
      | 0 => 3
      | (S n') => if (even_odd_dec n)
                  then (19 + ((rt_copy_fib (div2 n)) + (rt_copy_fib (div2 n'))))
                  else (13 + (rt_copy_fib (div2 n)))
    end.

 
  Definition fib_log n := fib (cl_log n).

  Definition copy_fib_result (x : A) (n : nat) (t : bin_tree) (c : nat) :=
     Braun t n /\
     (forall i y, IndexR t i y -> y = x) /\
     c = rt_copy_fib n.

  Load "copy_fib_log_gen.v".

  Next Obligation.
  Proof.
    split. constructor.
    split. intros i y H. inversion H.
    compute. reflexivity.
  Qed.

  Next Obligation.
  Proof.
    apply lt_div2. 
    induction n; [unfold not in H; assert (0 = 0)|]; omega.
  Qed.

  Next Obligation.
  Proof.
    destruct n;  [unfold not in H; assert (0 = 0)|]; try omega.
    apply lt_trans with (m := div2 (S n)).
    replace (div2 (S n) - 1) with (pred (div2 (S n))); try omega.
    apply lt_pred_n_n.
    destruct n; [ invclr H0; invclr H3|unfold div2; omega].
    apply lt_div2. omega.
  Qed.

  Next Obligation.
  Proof.
    (* even case *)
    rename H0 into E.
    clear H5 H4 am0 am.
    rename H into NEQ.
    invclr H2.
    rename H into Br.
    invclr H0.
    rename H into IRr.
    invclr H3.
    rename H into Bl.
    invclr H0.
    rename H into IRl.

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
    unfold_sub rt_copy_fib (rt_copy_fib (S n')).
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
  Proof.
    apply lt_div2. destruct n. inversion H0. omega.
  Qed.

  Next Obligation.
  Proof.
    (* odd case *)
    clear H3.
    rename H0 into On.
    rename H into NEQ.
    invclr H2.
    rename H into Brt.
    invclr H0.
    rename H into Irt.
  
    split. 
    
    (* Braunness *)
    replace n with ((div2 n) + (div2 n) + 1). 
    constructor; try assumption.
    split; [constructor | intuition].
    rewrite odd_double; try assumption. 
    unfold double. rewrite plus_comm. omega. 

    split.

    (* correct elems *)
    intros i y HIr; inversion HIr; auto; apply Irt with (i := i0); auto.

    (* running time *)
    destruct n as [|n']; [unfold not in NEQ; assert (0 = 0)|]; try omega.
    unfold_sub rt_copy_fib (rt_copy_fib (S n')).
    destruct (even_odd_dec (S n')).
    apply not_even_and_odd in e. contradiction. assumption.
    fold_sub rt_copy_fib. 
    destruct n'. compute. reflexivity.
    rewrite <- even_div2.
    rewrite odd_div2. omega.
    inversion o. inversion H0. assumption.
    inversion o. assumption.
  Qed.
     
  Program Fixpoint p (n : nat) {measure n} : nat :=
    match n with
      | 0 => 0
      | 1 => 1
      | _ => 1 + p (div2 n) + p (div2 (div2 n))
    end.

  Next Obligation.
  Proof.
    apply lt_div2; intuition.
  Qed.

  Next Obligation.
  Proof.
    apply lt_trans with (m := (div2 n)).
    apply lt_div2. 
    destruct n as [|n]; [unfold not in H0; intuition|].
    destruct n as [|n]; [unfold not in H; intuition|].
    simpl; omega.
    apply lt_div2; intuition.
  Qed.
    
  (* This ugliness is because Program doesn't allow *)
  (* mutual recursion on well-founded arguments. *)

  Inductive fg_arg : Type :=
  | g_arg (a:nat)
  | f_arg (a:nat).
  
  Definition fg_val (a : fg_arg) : nat :=
    match a with
      | g_arg n => n
      | f_arg n => n
    end.

  Program Fixpoint h (a : fg_arg) {measure (fg_val a)} : nat :=
    match a with
      | f_arg n =>
        match n with
          | 0 => 3
          | 1 => 16
          | _ => 19 + h (f_arg (div2 n)) + h (g_arg (div2 n))
        end
      | g_arg n =>
        match n with
          | 0 => 3
          | 1 => 16
          | _ => 13 + h (f_arg (div2 n))
        end
    end.

  Next Obligation.
  Proof.
    intuition.  
  Qed.

  Next Obligation.
  Proof.
    intuition.
  Qed.

  Next Obligation.
  Proof.
    intuition.
  Qed.

  Definition f n := h (f_arg n).
  Definition g n := h (g_arg n).


  Lemma fg_monotone : forall m n, m <= n -> 
                                  (f m <= f n /\ g m <= g n).
  Proof.
    intros m n.
    generalize dependent m.
    generalize dependent n.
    apply (well_founded_induction lt_wf
                                  (fun (n : nat) =>
                                     forall m, (m <= n
                                               ->  (f m <= f n /\ g m <= g n)))).
    intros n H m Hmn.
    split.

    (* f *)
    destruct m as [|m]; destruct n as [|n].
    compute; omega.
    destruct n as [|n].
    compute; omega.
    unfold f.
    unfold_sub h (h (f_arg (S (S n)))).
    replace (h (f_arg 0)) with 3; [omega|compute;omega]. 
    inversion Hmn.
    destruct m as [|m]; destruct n as [|n].
    auto.
    unfold f.
    unfold_sub h (h (f_arg (S (S n)))).
    replace (h (f_arg 1)) with 16; [|compute;omega].
    destruct (div2 n); [compute;omega|].
    unfold_sub h (h (f_arg (S (S n0)))); omega.
    inversion Hmn; inversion H1.
    unfold f.
    unfold_sub h (h (f_arg (S (S n)))).
    unfold_sub h (h (f_arg (S (S m)))).
    rewrite <- plus_assoc. rewrite <- plus_assoc. 
    apply plus_le_compat_l.
    replace (h (f_arg (S (div2 m)))) with (f (S (div2 m))); [|auto].
    replace (h (f_arg (S (div2 n)))) with (f (S (div2 n))); [|auto].
    replace (h (g_arg (S (div2 m)))) with (g (S (div2 m))); [|auto].
    replace (h (g_arg (S (div2 n)))) with (g (S (div2 n))); [|auto].
    assert (f (S (div2 m)) <= f (S (div2 n)) /\ g (S (div2 m)) <= g (S (div2 n))).
    apply H.
    intuition. 
    apply le_n_S; apply div2_monotone; intuition.
    inversion H0.
    apply plus_le_compat; assumption.

    (* g *)
    destruct m as [|m]; destruct n as [|n].
    compute; omega.
    destruct n as [|n].
    compute; omega.
    unfold g.
    unfold_sub h (h (g_arg (S (S n)))).
    replace (h (g_arg 0)) with 3; [omega|compute;omega].
    inversion Hmn.
    destruct m as [|m]; destruct n as [|n].
    auto.
    unfold g.
    unfold_sub h (h (g_arg (S (S n)))).
    replace (h (g_arg 1)) with 16; [|compute; omega].
    simpl; repeat apply le_n_S. 
    replace 3 with (f 0); [|compute; omega].
    replace (h (f_arg (S (div2 n)))) with (f (S (div2 n))).
    assert ((S (div2 n)) < (S (S n))). apply le_lt_trans with (m := div2 (S (S n))); auto.
    apply H with (m := 0) in H0; intuition.
    intuition. 
    replace (h (g_arg 1)) with 16; [omega|compute;omega].
    intuition.
    unfold g.
    unfold_sub h (h (g_arg (S (S n)))).
    unfold_sub h (h (g_arg (S (S m)))).
    apply plus_le_compat_l.
    replace (h (f_arg (S (div2 m)))) with (f (S (div2 m))); [|auto].
    replace (h (f_arg (S (div2 n)))) with (f (S (div2 n))); [|auto].
    assert (f (S (div2 m)) <= f (S (div2 n)) /\ g (S (div2 m)) <= g (S (div2 n))).
    apply H.
    intuition. 
    apply le_n_S; apply div2_monotone; intuition.
    inversion H0.
    auto.
  Qed.
  
  Hint Resolve fg_monotone.
  
  Lemma f_monotone :  forall m n, m <= n -> f m <= f n.
  Proof.
    intros m n H.
    apply fg_monotone in H.
    inversion H.
    auto.
  Qed.
  
  Lemma g_monotone : forall m n, m <= n -> g m <= g n.
  Proof.
    intros m n H.
    apply fg_monotone in H.
    inversion H.
    auto.
  Qed.

  Lemma g_lt_f : forall n, n > 1 -> g n < f n.
  Proof.
    intros n NE.    
    unfold g.
    unfold f.
    destruct n as [|n]; try intuition.
    destruct n as [|n]; try intuition.
    unfold_sub h (h (g_arg (S (S n)))).
    unfold_sub h (h (f_arg (S (S n)))).
    rewrite <- plus_assoc.
    simpl; repeat apply lt_n_S.
    intuition.
  Qed.

  Lemma even_pred : forall n, n <> 0 -> even n -> odd (n - 1).
  Proof.
    intros n NE.
    destruct n.
    unfold not in NE; intuition.
    intros E.
    simpl. inversion E.
    replace (n - 0) with n; try omega.
    auto.
  Qed.

  Lemma odd_pred : forall n, odd n -> even (n - 1).
  Proof.
    intros n E.
    destruct n; inversion E.
    simpl.
    replace (n - 0) with n; try omega.
    auto.
  Qed.

  Lemma even_div2_minus : forall m, even m -> m > 1
                                    -> ((even (div2 m) /\ odd (div2 (m - 1))) \/
                                        (odd (div2 m) /\ even (div2 (m - 1)))).
  Proof.
    intros m em NE.
    assert (div2 (m - 1) = (div2 m) - 1) as HD.
    inversion em; auto.
    rewrite <- odd_div2; simpl; [|auto].
    repeat rewrite <- minus_n_O; reflexivity.
    destruct (even_odd_dec (div2 m)).
    left.
    split; [assumption|].
    rewrite HD; apply even_pred; [|assumption].
    destruct m as [|m]; [inversion NE|].
    destruct m as [|m]; [inversion NE; inversion H0|].
    simpl; omega.
    right.
    split; [|rewrite HD; apply odd_pred]; assumption.
  Qed.    

  Lemma even_div2_SS_odd : forall n, even (div2 (S (S n))) -> odd (div2 n).
  Proof.
    intros n E.
    apply even_pred in E.
    simpl in E.
    replace (div2 n - 0) with (div2 n) in E; [auto|omega].
    simpl; omega.
  Qed.

  Lemma rtcf_f_g : forall n,
                     n > 1 ->
                     (even n -> rt_copy_fib n <= f n) /\
                     (odd n -> rt_copy_fib n <= g n).
  Proof.
    apply (well_founded_induction lt_wf
                                  (fun (n : nat) =>
                                     n > 1 ->
                                     (even n -> rt_copy_fib n <= f n) /\
                                     (odd n -> rt_copy_fib n <= g n))).
    intros n H n1.
    split.
    
    (* even case *)
    intros He.
    unfold_sub rt_copy_fib (rt_copy_fib n).
    destruct n as [|n]; [intuition|].
    destruct (even_odd_dec (S n));
      [|apply not_even_and_odd in He; intuition].
    repeat fold_sub rt_copy_fib.
    remember (S n) as m.
    assert ((even (div2 m) /\ odd (div2 (m - 1))) \/
            (odd (div2 m) /\ even (div2 (m - 1)))) as mOE;
      [apply even_div2_minus; auto|].
    inversion mOE as [L|R].

    (* even: even/odd *)
    subst.
    unfold f.
    unfold_sub h (h (f_arg (S n))).
    destruct n as [|n]; [inversion n1; intuition|].
    repeat fold_sub h.
    replace (h (f_arg (S (div2 n)))) with (f (S (div2 n))); auto.
    replace (h (g_arg (S (div2 n)))) with (g (S (div2 n))); auto.
    replace (1 + f (S (div2 n)) + g (S (div2 n))) with 
            (S (f (S (div2 n)) + g (S (div2 n)))); [|omega].
    assert ((S (div2 n) < (S (S n)))) as HL; [intuition|].
    rewrite <- plus_assoc; apply plus_le_compat_l.
    do 4 (destruct n as [|n]; [compute; omega|]).
    apply H in HL; [|simpl;omega]. 
    inversion HL as [E O].
    replace (div2 (S (S (S (S (S (S n))))))) with (S (div2 (S (S (S (S n))))));
      [|simpl;omega].
    apply plus_le_compat.
    apply E; intuition.
    rewrite <- even_div2; [|inversion e; inversion H1; assumption].
    apply le_trans with (m := (g (div2 (S (S (S (S n))))))).
    assert ((div2 (S (S (S (S n))))) < (S (S (S (S (S (S n))))))) as HL2; 
      [intuition|].
    apply H in HL2; [|simpl;omega]. inversion HL2 as [E2 O2].
    apply O2; inversion L; apply even_div2_SS_odd in H0; assumption.
    apply g_monotone; intuition.

    (* even: odd/even *)
    subst.
    replace (S n - 1) with n in mOE; [|omega].
    replace (S n - 1) with n in R; [|omega].
    unfold f.
    unfold_sub h (h (f_arg (S n))).
    destruct n as [|n]; [inversion n1; intuition|].
    repeat fold_sub h.
    replace (h (f_arg (S (div2 n)))) with (f (S (div2 n))); auto.
    replace (h (g_arg (S (div2 n)))) with (g (S (div2 n))); auto.
    replace (1 + f (S (div2 n)) + g (S (div2 n))) with 
            (S (f (S (div2 n)) + g (S (div2 n)))); [|omega].
    assert ((div2 (S n)) < (S (S n))) as HL; [intuition|].
    destruct n as [|n]; [compute; omega|].
    destruct n as [|n]; [invclr He; invclr H1; invclr H2; invclr H1|].
    destruct n as [|n]; [compute; omega|].
    destruct n as [|n]; 
      [invclr He; invclr H1; invclr H2; invclr H1; invclr H2; invclr H1|].
    apply H in HL; [|simpl;omega]. 
    inversion HL as [E O].
    repeat apply le_n_S.
    rewrite plus_comm; apply plus_le_compat.
    apply le_trans with (m := (f (div2 (S (S (S (S (S n)))))))).
    apply E. inversion R; assumption.
    apply f_monotone.
    rewrite <- even_div2;
      [omega|inversion e; inversion H1; auto].
    replace (S (div2 (S (S (S (S n)))))) with (div2 (S (S (S (S (S (S n))))))); 
      [|simpl;omega].
    assert ((div2 (S (S (S (S (S (S n))))))) < (S (S (S (S (S (S n)))))))
      as HL2; [intuition|].
    apply H in HL2; [|simpl;omega]. 
    inversion HL2 as [E2 O2].
    apply O2; inversion R; assumption.

    (* odd case *)
    intros Ho.
    unfold_sub rt_copy_fib (rt_copy_fib n).
    destruct n as [|n]; [invclr Ho|].
    destruct (even_odd_dec (S n));
      [apply not_even_and_odd in e; intuition|].
    fold_sub rt_copy_fib.
    apply le_trans with (m := (13 + f (div2 (S n)))).
    repeat apply le_n_S. 
    assert ((div2 (S n)) < S n) as L; auto.
    destruct n as [|n]; [compute; omega|].
    destruct n as [|n]; [invclr Ho; invclr H1; invclr H2|].
    destruct n as [|n]; [compute; omega|].
    apply H in L; [|simpl;omega].
    remember (div2 (S (S (S (S n))))) as m.
    assert (even m \/ odd m); [apply even_or_odd|].
    inversion L as [E O]. 
    inversion H0.
    apply E; auto.
    subst.
    apply le_trans with (m := g (div2 (S (S (S (S n)))))). 
    apply O; auto.
    apply lt_le_weak; auto.
    apply g_lt_f; simpl; omega.
    unfold g.
    unfold_sub h (h (g_arg (S n))). 
    fold_sub h.
    destruct n as [|n']; [inversion n1; intuition|].
    replace (h (f_arg (S (div2 n')))) with (f (S (div2 n'))); 
      [apply le_n_S|]; auto.
  Qed.

  Lemma g_le_f : forall (n : nat), g n <= f n.
  Proof.
    intros n.
    destruct n; [compute; omega|].
    destruct n; [compute; omega|].
    unfold g. unfold f.
    unfold_sub h (h (g_arg (S (S n)))).
    unfold_sub h (h (f_arg (S (S n)))).
    omega.
  Qed.
  
  Lemma rtcf_big_oh_f : big_oh rt_copy_fib f.
  Proof.
    exists 2.
    exists 1.
    intros n LT.
    remember (rtcf_f_g LT).
    clear Heqa.
    destruct a as [EV OD].
    destruct (even_or_odd n) as [E|O].
    apply EV in E.
    omega.
    apply OD in O. 
    unfold mult.
    rewrite plus_0_r.
    apply (le_trans (rt_copy_fib n)
                    (g n)
                    (f n)).
    omega.
    apply g_le_f.
  Qed.  

  Lemma f_big_oh_p : big_oh f p.
  Proof.
    exists 1.
    exists 32.
    unfold f.
    apply (well_founded_induction 
             lt_wf
             (fun n => 1 <= n -> h (f_arg n) <= 32 * p n)).
    intros n IND LT.
    destruct n; intuition.
    clear LT.
    destruct n; [compute; omega|].
    destruct n; [compute; omega|].
    destruct n; [compute; omega|].
    unfold_sub h (h (f_arg (S (S (S (S n)))))).
    unfold_sub h (h (g_arg (S (S (div2 n))))).
    unfold_sub p (p (S (S (S (S n))))).
    replace (19 + h (f_arg (S (S (div2 n)))) + (13 + h (f_arg (S (div2 (div2 n))))))
    with (32 + (h (f_arg (S (S (div2 n)))) + h (f_arg (S (div2 (div2 n))))));
      [|omega].
    replace (32 * (1 + p (S (S (div2 n))) + p (S (div2 (div2 n)))))
    with  (32 + (32 * p (S (S (div2 n))) + 32 * p (S (div2 (div2 n)))));
      [|omega].
    apply plus_le_compat_l.
    apply plus_le_compat; apply IND; intuition.
    apply lt_n_S.
    apply le_lt_trans with (m := div2 n);
      intuition.
  Qed.

  Lemma l1 : forall (a b c d : nat),
               a < 4 * b -> c < 4 * d
               -> 1 + a + c < 4 * (b + d).
  Proof.
    intros; omega.
  Qed.  

  Lemma p_lt_fl : forall (n : nat), n <> 0
                                    -> p n < 4 * (fib (cl_log n)).
  Proof.
    apply (well_founded_induction 
             lt_wf
             (fun n => n <> 0
                       -> p n < 4 * (fib (cl_log n)))).
    intros n IH N0.
    destruct n as [|n]; [intuition|].
    destruct n as [|n]; [compute; omega|].
    destruct n as [|n]; [compute; omega|].
    destruct n as [|n]; [compute; omega|].
    unfold_sub cl_log (cl_log (S (S (S (S n))))).
    unfold_sub cl_log (cl_log (S (S (div2 n)))).
    remember (cl_log (S (div2 (div2 n)))) as m.
    rewrite fib_SS.
    unfold_sub p (p (S (S (S (S n))))).
    subst.
    replace (S (cl_log (S (div2 (div2 n)))))
    with (cl_log (S (S (div2 n))));
      [|unfold_sub cl_log (cl_log (S (S (div2 n)))); auto].
    apply l1. 
    apply IH; intuition.
    apply IH; [|omega].
    apply lt_n_S. 
    apply le_lt_trans with (m := (div2 n)); intuition.
  Qed.

  Lemma p_big_oh_fl : big_oh p fib_log.
  Proof.
    exists 1.
    exists 4.
    intros n LE.
    unfold fib_log.
    apply lt_le_weak.
    apply p_lt_fl.
    intuition.
  Qed.

  Lemma rtcf_big_oh_fib_log : big_oh rt_copy_fib fib_log.
  Proof.
    apply big_oh_trans with (g := f).
    apply rtcf_big_oh_f.
    apply big_oh_trans with (g := p).
    apply f_big_oh_p.
    apply p_big_oh_fl.
  Qed.

End copy_fib.
