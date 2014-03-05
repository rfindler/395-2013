Require Import Braun.common.braun Braun.common.log Braun.common.util Braun.common.log_sq.
Require Import Braun.tmonad.monad.
Require Import Coq.Program.Wf Arith.Even Arith.Div2 Arith.

Definition diff_result (A:Set) (b : @bin_tree A) m n c :=
   (Braun b m     -> (n = 0 /\ c = fl_log m)) 
   /\
   (Braun b (m+1) -> (n = 1 /\ c = fl_log m + 1)).

(* this is generated from the rkt code, but 
   tweaked to have the same constants as the
   hand-written version *)
Program Fixpoint diff {A:Set} (b:@bin_tree A) (m:nat) {measure m}
: {! res !:! nat !<! c !>!
     diff_result A b m res c !} :=
  match b, m with
    | bt_mt, _ => 
      += 0; 
      <== 0
    | bt_node x _ _, 0 => 
      += 1; 
      <== 1
    | bt_node x s t, S m' => 
      if (even_odd_dec m)
      then (o <- diff t (div2 (m' - 1));
            += 1; 
            <== o)
      else (o <- diff s (div2 m');
            += 1; 
            <== o)
  end.

Next Obligation.
  unfold diff_result in *.
  replace (m+1) with (S m); try omega.
  split; intros B; invclr B.
  split; auto.
Qed.

Next Obligation.
  unfold diff_result in *.
  simpl.
  split; intros B; invclr B; omega.
Qed.

Next Obligation.
  clear am H2 diff.
  rename H1 into BTxn.
  rename H into E.
  destruct BTxn as [BT1 BT2].

  unfold diff_result in *.
  apply even_2n in E. destruct E as [mm EQ].
  unfold double in EQ.
  split; intros B; invclr B;
  rename H3 into BP; rename H4 into Bs; rename H5 into Bt;
  rename H2 into EQ'.

  replace m' with (s_size + t_size) in *; try omega.
  clear EQ'.
  replace s_size with (t_size + 1) in *; try omega.  
  replace (t_size + 1 + t_size - 1) with (2 * t_size) in *; try omega.
  replace (div2 (2 * t_size)) with t_size in *; try omega.
  apply BT1 in Bt.
  destruct Bt as [Bt_o Bt_xn].
  subst. split; auto.
  apply braun_invariant_implies_fl_log_property.
  auto.
  symmetry. apply div2_double.

  replace s_size with t_size in *; try omega.
  clear BP s_size.
  assert (t_size + t_size = mm + mm) as EQ''; try omega.
  clear EQ'. rewrite <- EQ'' in EQ. clear EQ''.
  destruct t_size as [|t_size]; try omega.
  simpl in EQ. replace m' with (t_size + S t_size) in *; try omega.
  clear EQ.
  replace (t_size + S t_size - 1) with (2 * t_size) in *; try omega.
  rewrite div2_double in *.
  replace (t_size + 1) with (S t_size) in *; try omega.
  apply BT2 in Bt.
  destruct Bt as [Bt_o Bt_xn].
  subst. split; auto.
  rewrite <- fl_log_even.
  replace (t_size + 1 + (t_size + 1)) with (S (t_size + S t_size)); omega.
Qed.

Next Obligation.
  clear am H2 diff.
  rename H1 into BT.
  rename H into O.

  destruct BT as [BT1 BT2].
  apply odd_S2n in O. destruct O as [mm EQ].
  unfold double in EQ. 
  replace m' with (2 * mm) in *; try omega.
  clear EQ.
  rewrite div2_double in *.
  split; intros B; invclr B;
  rename H3 into BP; rename H4 into Bs; rename H5 into Bt;
  rename H2 into EQ.

  replace mm with t_size in *; try omega.
  replace s_size with t_size in *; try omega.
  clear EQ s_size.
  apply BT1 in Bs.
  destruct Bs as [Bt_o Bt_xn]. subst.
  split; auto.
  rewrite <- fl_log_odd.
  replace (t_size + t_size + 1) with (S (2 * t_size)); omega.

  replace s_size with (t_size + 1) in *; try omega.
  replace mm with t_size in *; try omega.
  apply BT2 in Bs.
  destruct Bs as [Bt_o Bt_xn]. subst.
  split; auto.
  rewrite <- fl_log_odd.
  replace (t_size + t_size + 1) with (S (2 * t_size)); omega.
Qed.

Definition size_result (A:Set) (b : @bin_tree A) n c :=
  forall m,
    (Braun b m -> (n = m /\ c = sum_of_logs n)).

(* this is generated from the rkt code, but 
   tweaked to have the same constants as the
   hand-written version *)
Program Fixpoint size {A:Set} (b:@bin_tree A)
: {! res !:! nat !<! c !>!
     size_result A b res c !} :=
  match b with
    | bt_mt => 
      += 0; 
      <== 0
    | bt_node _ s t => 
      m <- size t;
      zo <- diff s m;
      += 1; 
      <== (1 + (2 * m) + zo)
  end.

Next Obligation.
Proof.
  unfold size_result.
  intros m H.
  inversion H.
  constructor;auto.
Qed.  

Next Obligation.
Proof.
  clear H2 am0.
  clear H3 am.
  rename H0 into DIFF_RES.
  rename H1 into REC.

  destruct DIFF_RES as [SIZE_SAME SIZE_DIFF].

  unfold size_result in *.

  intros m0 BTb.

  invclr BTb.
  rename H2 into LT.
  rename H4 into BRAUNS.
  rename H5 into BRAUNT.

  remember (REC t_size BRAUNT) as QQ.
  destruct QQ; subst.
  clear HeqQQ REC BRAUNT.

  assert (s_size = t_size \/ s_size = t_size + 1) as TWOCASES;[omega|].
  destruct TWOCASES as [EQ|EQ]; subst.

  apply SIZE_SAME in BRAUNS. destruct BRAUNS as [EQo EQxn]. subst.
  split; try omega.
  replace (S (t_size + (t_size + 0) + 0)) with (t_size+t_size+1);[|omega].
  rewrite <- sum_of_logs_odd.
  rewrite fl_log_odd.
  omega.

  apply SIZE_DIFF in BRAUNS. destruct BRAUNS as [EQo EQxn]. subst.
  split; try omega.
  replace (S (t_size + (t_size + 0) + 1)) with (t_size + 1 + t_size + 1);[|omega].
  rewrite <- sum_of_logs_even.
  rewrite <- cl_log_even.
  replace (t_size + 1) with (S t_size);[|omega].
  rewrite <- fl_log_cl_log_relationship.
  omega.
Qed.
