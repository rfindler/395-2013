Require Import Braun.tmonad.monad Braun.logical.index.
Require Import Braun.common.braun Braun.common.log Braun.common.util.
Require Import Arith Arith.Even Arith.Div2 Omega.
Require Import Program.Wf Init.Wf.

Include WfExtensionality.

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

  Definition fib_log n := fib (cl_log n).

  Lemma minus_plus': forall n m p : nat, m <= n -> p = n - m -> n = m + p.
  Proof.
    intros. subst. apply le_plus_minus. auto.
  Qed.

      
  Lemma fib_monotone : forall (n : nat) (m : nat), m < n -> fib m <= fib n.
  Proof.
    apply (well_founded_induction lt_wf
                                  (fun (n : nat) =>
                                     forall (m : nat), m < n -> fib m <= fib n)).
    intros x0 H m H0.
    destruct x0 as [|n'].
    inversion H0.
    destruct n' as [|n''].
    inversion H0; [compute; omega|inversion H2].
    unfold_sub fib (fib (S (S n''))).
    destruct m as [|m'].
    replace (fib 0) with 0; [|compute;auto].
    apply le_0_n.
    destruct m' as [|m''].
    apply le_plus_trans.
    destruct n'' as [|n''']; [|apply H]; try omega.
    destruct n'' as [|n''']; [intuition|]. 
    apply le_plus_trans.
    inversion H0; auto.
  Qed.

  Hint Resolve fib_monotone.
  
  Lemma div2_monotone' : forall (n : nat) (m : nat), m <= n -> div2 m <= div2 n.
    apply (well_founded_induction lt_wf
                                  (fun (n : nat) =>
                                     forall (m : nat),
                                       
                                       m <= n -> div2 m <= div2 n)).
    intros n IH m Hm.
    unfold div2.
    destruct m as [|m']; destruct n as [|n']; try auto.
    destruct n' as [|n'']; try auto.
    apply le_0_n.
    destruct m' as [|m'']; try auto.
    inversion Hm.
    destruct n' as [|n'']; destruct m' as [|m'']; try auto.
    inversion Hm; inversion H0.
    apply le_0_n.
    repeat fold div2.
    apply le_n_S.
    apply IH; auto.
    apply le_S_n; apply le_S_n; assumption.
  Qed.

  Hint Resolve div2_monotone'.

  Lemma cl_log_monotone' : forall (n : nat) (m : nat), m <= n -> cl_log m <= cl_log n.
    apply (well_founded_induction lt_wf
                                  (fun (n : nat) =>
                                     forall (m : nat), 
                                       m <= n -> cl_log m <= cl_log n)).
    intros n IH m Hm.
    destruct m as [|m'].
    destruct n as [|n'].
    compute; auto;
    unfold_sub cl_log (cl_log (S n')).
    replace (cl_log 0) with 0; [omega|compute;auto].
    destruct n as [|n'].
    replace (cl_log 0) with 0; [omega|compute;auto].
    unfold_sub cl_log (cl_log (S n')).
    destruct n' as [|n'']. 
    inversion Hm; auto.
    unfold_sub cl_log (cl_log (S m')).
    destruct m' as [|m''].
    replace (cl_log 0) with 0; [omega|compute;auto].
    apply le_n_S.
    apply IH.
    apply lt_n_S; auto.
    apply le_n_S; repeat apply le_S_n in Hm; auto.
  Qed.

  Lemma mle_2_and_3 : forall a b, 3 * a < 2 * b -> 3 * (b + a) < 2 * (b + a + b).
  Proof.
    intros.
    simpl. intuition.
  Qed.

  Lemma mle_9_and_6 : forall a b, 3 * a <= 2 * b -> 9 * a <= 6 * b.
  Proof.
    simpl. intuition.
  Qed.

  Hint Resolve mle_2_and_3.
  Hint Resolve mle_9_and_6.
  
  Lemma fib_S : forall (n : nat), n > 3 -> 3 * fib n < 2 * (fib (S n)).
  Proof.
    apply (well_founded_induction lt_wf
                                  (fun (n : nat) =>
                                     n > 3 -> 3 * fib n < 2 * (fib (S n)))).
    intros n IH g2.
    destruct n as [|n]; [compute; auto|].
    destruct n as [|n]; [inversion g2 as [|q G qq]; inversion G|].
    unfold_sub fib (fib (S (S (S n)))).
    unfold_sub fib (fib (S (S n))).
    destruct n as [|n]; [compute; auto|].
    destruct n as [|n]; [inversion g2 as [|q1 G q2]; inversion G; omega|].
    destruct n as [|n]; [compute; auto|].
    destruct n as [|n]; [compute; auto|].
    apply mle_2_and_3.
    apply IH; auto.
    omega.
  Qed.

  Hint Resolve fib_S.

  Lemma fib_log_div2 : forall (n : nat), 
                         n > 16 -> 3 * fib (cl_log (div2 n)) < 2 * fib (cl_log n).
  Proof.
    intros n g16.
    unfold_sub cl_log (cl_log n).
    do 16 (destruct n as [|n]; [inversion g16; try omega|]).
    fold_sub cl_log.
    unfold div2. fold div2.
    apply fib_S.
    unfold gt.
    apply lt_le_trans with (m := cl_log 8); [compute; auto|]. 
    apply cl_log_monotone'. 
    intuition.
  Qed.

  Hint Resolve fib_log_div2.

  Lemma rtcf_div2_le : forall (n : nat), (rt_copy_fib (div2 n)) <= rt_copy_fib n.
  Proof.
    apply (well_founded_induction lt_wf).
    intros.
    unfold_sub rt_copy_fib (rt_copy_fib x0);
      destruct x0 as [|n']; 
      try destruct (even_odd_dec (S n'));
      repeat fold_sub rt_copy_fib;
      intuition.
  Qed.    

  Lemma rtcf_div2_S_lt : forall (n : nat), (rt_copy_fib (div2 (S n))) < rt_copy_fib (S n).
  Proof.
    apply (well_founded_induction lt_wf).
    intros.
    unfold_sub rt_copy_fib (rt_copy_fib (S x0));
    destruct (even_odd_dec (S x0));
    repeat fold_sub rt_copy_fib;
    destruct x0 as [|n']; 
    intuition.
  Qed.

  Lemma rtcf_div2_S_lt' 
  : forall (n : nat), even (S n) -> (rt_copy_fib (div2 (S n)) + rt_copy_fib (div2 n)) < rt_copy_fib (S n).
  Proof.
    apply (well_founded_induction lt_wf
                                  (fun (n : nat) =>
                                     even (S n) ->
                                     rt_copy_fib (div2 (S n)) + rt_copy_fib (div2 n) < rt_copy_fib (S n))).
    intros.
    unfold_sub rt_copy_fib (rt_copy_fib (S x0));
    destruct (even_odd_dec (S x0));
    repeat fold_sub rt_copy_fib;
    destruct x0 as [|n'];
    intuition.
    inversion H0. inversion H2.
    apply not_even_and_odd in H0; try assumption. contradiction.
Qed.     
    
  Lemma lt_S_ab : forall a b c, a < c -> b < c -> S (a + b) < 6 * c.
  Proof.
    intros. omega.
  Qed.


  Lemma cl_log_a : forall n, cl_log (S (div2 n)) < cl_log (S (S n)).
  Proof.
    apply (well_founded_induction lt_wf
                                  (fun (n : nat) =>
                                     cl_log (S (div2 n)) < cl_log (S (S n)))).
    intros. 
    unfold_sub cl_log (cl_log (S (S x0))). omega.
  Qed.

  Lemma le_div2 : forall n, div2 n <= n.
    induction n; auto.
    unfold div2.
    destruct n as [|n'].
    omega.
    fold div2.
    intuition.
  Qed.
  
  Lemma rtcf_math : forall a b, 3 * a < 2 * b -> a < b.
  Proof.
    intros. omega.
  Qed.

  (* This ugliness is because Program doesn't allow
     mutual recursion on well-founded arguments. *)

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
          | 0 => 1
          | 1 => 2
          | _ => 1 + h (f_arg (div2 n)) + h (g_arg (div2 n))
        end
      | g_arg n =>
        match n with
          | 0 => 1
          | 1 => 1
          | _ => 1 + h (f_arg (div2 n))
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


  Lemma f_monotone : forall m n, m < n -> f m <= f n.
    Admitted.

  Lemma g_monotone : forall m n, m < n -> g m <= g n.
    Admitted.

  Lemma g_lt_f : forall n, g n < f n.
    Admitted.

  Lemma even_div2_minus : forall m, even m
                                    -> ((even (div2 m) /\ odd (div2 (m - 1))) \/
                                       (odd (div2 m) /\ even (div2 (m - 1)))).
    Admitted.

  Lemma even_div2_SS_odd : forall n, even (div2 (S (S n))) -> odd (div2 n).
    Admitted.

  Hint Resolve g_lt_f.

  (* Clean up this proof! *)
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
    (* even/odd *)
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
    destruct n as [|n]; [compute; omega|].
    destruct n as [|n]; [invclr He; invclr H1; invclr H2; invclr H1|].
    destruct n as [|n]; [compute; omega|].
    destruct n as [|n]; 
      [invclr He; invclr H1; invclr H2; invclr H1; invclr H2; invclr H1|].
    apply H in HL. inversion HL as [E O].
    apply le_n_S.
    apply plus_le_compat.
    simpl.
    apply E. intuition.
    rewrite <- even_div2.
    apply le_trans with (m := (g (div2 (S (S (S (S n))))))).
    assert ((div2 (S (S (S (S n))))) < (S (S (S (S (S (S n))))))) as HL2; 
      [intuition|].
    apply H in HL2. inversion HL2 as [E2 O2].
    apply O2.
    inversion L. apply even_div2_SS_odd in H0. assumption.
    simpl; omega.
    apply g_monotone. intuition.
    inversion e. inversion H1. assumption.
    simpl; omega.
    (* odd/even *)
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
    apply H in HL. inversion HL as [E O].
    apply le_n_S.
    rewrite plus_comm.
    apply plus_le_compat.
    apply le_trans with (m := (f (div2 (S (S (S (S (S n)))))))).
    apply E. inversion R; assumption.
    apply f_monotone.
    rewrite <- even_div2. omega.
    inversion e. inversion H1. auto.
    replace (S (div2 (S (S (S (S n)))))) with (div2 (S (S (S (S (S (S n))))))).
    assert ((div2 (S (S (S (S (S (S n))))))) < (S (S (S (S (S (S n)))))))
      as HL2; [intuition|].
    apply H in HL2. inversion HL2 as [E2 O2].
    apply O2. inversion R; assumption.
    simpl; omega.
    auto.
    simpl; omega.
    auto.

    (* odd case *)
    intros Ho.
    unfold_sub rt_copy_fib (rt_copy_fib n).
    destruct n as [|n]; [invclr Ho|].
    destruct (even_odd_dec (S n));
      [apply not_even_and_odd in e; intuition|].
    fold_sub rt_copy_fib.
    apply le_trans with (m := (1 + f (div2 (S n)))).
    apply le_n_S. 
    assert ((div2 (S n)) < S n) as L; auto.
    destruct n as [|n]; [compute; omega|].
    destruct n as [|n]; [inversion Ho;auto|].
    destruct n as [|n]; [compute; omega|].
    apply H in L.
    remember (div2 (S (S (S (S n))))) as m.
    assert (even m \/ odd m). apply even_or_odd.
    inversion L as [E O]. 
    inversion H0.
    apply E; auto.
    subst.
    apply le_trans with (m := g (div2 (S (S (S (S n)))))). apply O; auto.
    apply lt_le_weak. auto.
    simpl; omega.
    unfold g.
    unfold_sub h (h (g_arg (S n))). 
    fold_sub h.
    destruct n as [|n']; [inversion n1; intuition|].
    replace (h (f_arg (S (div2 n')))) with (f (S (div2 n'))); 
      [apply le_n_S|]; auto.
Qed.

    

    

    
    
(*
 
Proof idea that seemed like it would work, but didn't:

Show, for n > n_0,
even n -> rtcf n <= N_E * fib_log n
odd n  -> rtcf n <= N_O * fib_log n
using,
A * fib_log (div2 n) < B * fib_log n

That seemed like a good idea since actually N_E can
be significantly larger that N_O (about double or so), 
so there's a chance the even case could go through.

But in order for that to work, it turns out that you need
A/B = the golden ratio, exactly (I think, checked on paper).
Which you can't have in coq and besides that is
true only in the limit, so now I am really stuck.

*) 

  Lemma rtcf_is_O_fib_log 
  : exists (N : nat), forall (n : nat), n > 8 -> rt_copy_fib n <= N * fib_log n.
  Proof.
    exists 6.
    unfold fib_log.
    apply (well_founded_induction lt_wf
                                  (fun (n : nat) =>
                                     n > 8 ->
                                     rt_copy_fib n <= 6 * fib (cl_log n))).
    intros n IH nG.
    unfold_sub rt_copy_fib (rt_copy_fib n).
    destruct (even_odd_dec n) as [e|o];
    repeat fold_sub rt_copy_fib.
    
    Focus 2.

    (* odd case *)
    do 18 (destruct n as [|n]; [compute; omega|]).
    eapply le_lt_trans.
    apply IH. auto. 
    unfold div2; fold div2; repeat apply lt_n_S; apply lt_0_Sn.
    apply mult_lt_compat_l; try omega.
    apply rtcf_math.
    apply fib_log_div2.
    repeat apply lt_n_S; omega.

    (* even case *)
    destruct n as [|n]; [compute; omega|].
    fold_sub rt_copy_fib.
    admit.

  Qed.    

    

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
    destruct n; [ invclr H0; invclr H4|unfold div2; omega].
    apply lt_div2. omega.
  Qed.

  Next Obligation.
    (* even case *)
    rename H0 into E.
    rename H2 into Bl.
    rename H3 into IRl.
    rename H1 into Br.
    rename H5 into IRr.
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
    apply lt_div2. destruct n. inversion H0. omega.
  Qed.

  Next Obligation.
    (* odd case *)
    rename H into NEQ.
    rename H1 into Brt.
    rename H2 into Irt.
    rename H0 into On.
    clear H4 H5.

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
End copy_fib.
