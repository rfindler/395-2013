Require Import Braun.common.braun Braun.common.log Braun.common.util Braun.common.log_sq.
Require Import Braun.tmonad.monad.
Require Import Coq.Program.Wf Arith.Even Arith.Div2 Arith.

Set Implicit Arguments.

Lemma recur_ok : forall m', div2 (m' - 1) < S m'.
Proof.
  intros.
  apply (le_lt_trans (div2 (m' - 1))
                     (div2 m')
                     (S m')); auto.
  destruct m'; auto.
  replace (S m' - 1) with m';[|omega].
  auto.
Qed.
Hint Resolve recur_ok.

Program Fixpoint diff A (b : @bin_tree A) (m : nat) {wf lt m} 
: {! n !:! nat !<! c !>! 
   (Braun b m     -> (n = 0 /\ c = fl_log m)) 
   /\
   (Braun b (m+1) -> (n = 1 /\ c = fl_log m + 1)) !} :=
  match b,m with
    | bt_mt, 0 => <== 0
    | bt_node x bt_mt bt_mt, 0 => ++; <== 1
    | bt_node x s t, (S m') =>
      if (even_odd_dec m)
      then o <- diff t (div2 (m'-1)); ++; <== o
      else o <- diff s (div2 m');     ++; <== o
    | _ , _ => <== 999
  end.

Next Obligation.
Proof.
  repeat constructor; auto; simpl in H; inversion H.
Qed.

Next Obligation.
  repeat constructor; auto; inversion H; intuition.
Qed.

Next Obligation.
  clear diff.
  constructor; intros.

  inversion H2; subst.

  rewrite <- H6 in H.
  assert (s_size = t_size+1);[apply braun_invariant_even_size; assumption|subst].

  replace (div2 (m' - 1)) with t_size in H0.
  apply H0 in H9.
  inversion H9.
  constructor;auto.
  rewrite H4.
  replace (t_size + 1 + t_size + 1) with ((t_size+1)+(t_size+1));[|omega].
  rewrite fl_log_even.
  omega.

  replace (t_size + 1 + t_size + 1) with (S (t_size+t_size+1)) in H6;[|omega].
  inversion H6.
  replace (t_size+t_size + 1 - 1) with (t_size+t_size);[|omega].
  rewrite double_div2.
  reflexivity.

  inversion H2; subst.

  replace (S m') with (s_size+t_size) in H;[|omega].

  assert (odd (s_size+t_size+1)).
  replace (s_size+t_size+1) with (S (s_size+t_size));[|omega].
  constructor.
  assumption.

  assert (s_size = t_size);[apply braun_invariant_odd_size;assumption|subst].

  replace (div2 (m' - 1) + 1) with t_size in H1.
  apply H1 in H9.
  inversion H9.
  constructor;auto.

  rewrite H5.
  
  rewrite fl_log_div2'.

  replace (div2 (m'-1)) with (div2 m').
  omega.

  assert (m'-1 = (t_size-1)+(t_size-1)) as MONEDEF;[omega|].
  assert (even (m'-1)).
  rewrite MONEDEF.
  apply double_is_even.
  replace (div2 m') with (div2 (S (m'-1))).
  symmetry.
  apply even_div2.
  assumption.
  replace (S (m'-1)) with m';[|omega].
  reflexivity.

  assert (t_size+t_size = S m') as SMDOUBLED;[omega|].

  replace (m'-1) with ((S m') - 2);[|omega].
  rewrite <- SMDOUBLED.
  replace (t_size+t_size-2) with ((t_size-1)+(t_size-1));[|omega].
  rewrite double_div2.
  omega.
Qed.

Next Obligation.
Proof.
  constructor.
  intros BT.
  invclr BT.

  replace (S m') with (s_size+t_size+1) in H.
  replace t_size with s_size in *;[|apply braun_invariant_odd_size;assumption].

  replace (div2 m') with s_size in H0.
  apply H0 in H7.
  inversion H7.
  constructor;auto.
  subst xn.
  symmetry.
  apply fl_log_odd.
  
  replace m' with (s_size+s_size);[|omega].
  symmetry.
  apply double_div2.

  intros BT.
  invclr BT.

  assert (even (s_size+t_size+1)).
  replace (s_size+t_size+1) with (S (s_size+t_size));[|omega].
  constructor.
  replace (s_size+t_size) with (S m');[|omega].
  assumption.

  assert (s_size = t_size+1) as ST;[apply braun_invariant_even_size;assumption|subst].
  
  replace (div2 m' + 1) with (t_size+1) in H1.
  apply H1 in H7.
  inversion H7.
  constructor;auto.
  subst xn.
  rewrite fl_log_div2'.
  omega.

  replace m' with (t_size+t_size);[|omega].
  rewrite double_div2.
  reflexivity.
Qed.

Lemma q : forall A (b:@bin_tree A), (Braun b 0) -> bt_mt = b.
Proof.
  intros.
  inversion H.
  reflexivity.
  replace (s_size+t_size+1) with (S (s_size+t_size)) in H0;[|omega].
  inversion H0.
Qed.

Next Obligation. 
Proof.
  (* show that the last case cannot happen (under the braun tree assumptions) *)
  clear diff.
  constructor; intros.

  destruct m; destruct b.
  intuition.
  inversion H2.
  rewrite plus_comm in H6.
  simpl in H6.
  inversion H6.
  inversion H2.
  assert False.
  unfold not in H0.
  apply (H0 a b1 b2 m).
  constructor;auto.
  intuition.

  destruct m; destruct b.
  simpl in H2.
  inversion H2.
  simpl in H2.
  inversion H2.

  assert False;[|intuition].
  replace s_size with 0 in *; [|omega].
  replace t_size with 0 in *; [|omega].
  replace b1 with (@bt_mt A) in *; [|apply q; assumption].
  replace b2 with (@bt_mt A) in *; [|apply q; assumption].
  unfold not in H.
  apply (H a).
  auto.

  replace (S m + 1) with (S (m+1));[|omega].
  inversion H2.
  assert False;[|intuition].
  unfold not in H0.
  apply (H0 a b1 b2 m).
  auto.
Qed.

Next Obligation.
Proof. intuition. inversion H0. Qed.

Next Obligation.
Proof. intuition. inversion H0. inversion H0. Qed.

Next Obligation.
Proof. intuition. inversion H0. inversion H0. Qed.

Program Fixpoint size A (b : @bin_tree A) 
: {! n !:! nat !<! c !>! 
     forall m,
       (Braun b m -> (n = m /\ c = sum_of_logs n))
         !} := 
  match b with 
    | bt_mt => <== 0
    | bt_node _ s t =>
      (++;
       m <- size t ; 
       zo <- diff s m;
       <== (1 + 2 * m + zo))
  end.

Next Obligation.
Proof.
  inversion H.
  constructor;auto.
Qed.  

Next Obligation.
Proof.

  invclr H1.
  rename H into SIZE_SAME.
  rename H2 into SIZE_DIFF.
  rename H8 into BRAUNS.
  rename H9 into BRAUNT.

  assert (m=t_size /\ xn0 = sum_of_logs m) as STUFF;[apply H0;assumption|].
  clear H0. invclr STUFF.

  assert (s_size = t_size \/ s_size = t_size + 1) as TWOCASES;[omega|].
  inversion TWOCASES;subst s_size; clear H6 TWOCASES.

  remember BRAUNS as DIFFRES. clear HeqDIFFRES.
  apply SIZE_SAME in DIFFRES; clear SIZE_SAME SIZE_DIFF.
  invclr DIFFRES.

  constructor; try omega.
  replace (S (t_size + (t_size + 0) + 0)) with (t_size+t_size+1);[|omega].

  rewrite <- sum_of_logs_odd.
  rewrite fl_log_odd.
  omega.

  remember BRAUNS as DIFFRES. clear HeqDIFFRES.
  apply SIZE_DIFF in DIFFRES; clear SIZE_SAME SIZE_DIFF.
  invclr DIFFRES.
  
  constructor; try omega.
  replace (S (t_size + (t_size + 0) + 1)) with (t_size + 1 + t_size + 1);[|omega].
  rewrite <- sum_of_logs_even.
  rewrite <- cl_log_even.
  replace (t_size + 1) with (S t_size);[|omega].
  rewrite <- fl_log_cl_log_relationship.
  omega.
Qed.
