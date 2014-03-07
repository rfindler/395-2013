Require Import Braun.common.braun Braun.common.log Braun.common.util Braun.common.log_sq.
Require Import Braun.tmonad.monad Braun.common.big_oh.
Require Import Coq.Program.Wf Arith.Even Arith.Div2 Arith Init.Wf.

Include WfExtensionality.

Program Fixpoint diff_time m {measure m} :=
  match m with
    | 0 => 4
    | S m' =>
      if (even_odd_dec m)
      then 13 + diff_time (div2 (m' - 1))
      else 11 + diff_time (div2 m')
  end.

Definition diff_result (A:Set) (b : @bin_tree A) m n c :=
   (Braun b m     -> (n = 0 /\ c = diff_time m))
   /\
   (Braun b (m+1) -> (n = 1 /\ c = diff_time m)).

Load "diff_gen.v".

Next Obligation.
  unfold diff_result in *.
  replace (m+1) with (S m); try omega.
  split; intros B; invclr B.
  split; auto.
Qed.

Next Obligation.
  unfold diff_result in *.
  simpl.
  unfold_sub diff_time (diff_time 0).
  split; intros B; invclr B; omega.
Qed.

Lemma diff_time_nz_even : 
  forall m', even (S m') -> diff_time (S m') = 13+diff_time (div2 (m'-1)).
  intros m' EV.
  unfold_sub diff_time (diff_time (S m')).
  fold diff_time.
  dispatch_if x x'; auto.
  assert False; intuition.
  apply (not_even_and_odd (S m')); auto.
Qed.

Next Obligation.
  clear am H2 diff.
  rename H1 into BTxn.
  rename H into E.
  destruct BTxn as [BT1 BT2].

  unfold diff_result in *.
  rewrite diff_time_nz_even; auto.

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
  omega. unfold mult. 
  replace (t_size + (t_size + 0)) with (t_size+t_size); try omega.
  symmetry. apply double_div2.

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
  omega.
Qed.

Lemma diff_time_nz_odd : 
  forall m', odd (S m') -> diff_time (S m') = 11+diff_time (div2 m').
  intros m' EV.
  unfold_sub diff_time (diff_time (S m')).
  fold diff_time.
  dispatch_if x x'; auto.
  assert False; intuition.
  apply (not_even_and_odd (S m')); auto.
Qed.

Next Obligation.
  clear am H2 diff.
  rename H1 into BT.
  rename H into O.

  unfold diff_result in *.
  rewrite diff_time_nz_odd; auto.

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
  omega.

  replace s_size with (t_size + 1) in *; try omega.
  replace mm with t_size in *; try omega.
  apply BT2 in Bs.
  destruct Bs as [Bt_o Bt_xn]. subst.
  split; auto.
  omega.
Qed.

Program Fixpoint diff_time2 m {measure m} :=
  match m with
    | 0 => 4
    | S m' => 13 + diff_time2 (div2 m')
  end.

Lemma diff_time12 : big_oh diff_time diff_time2.
Proof.
  exists 0. exists 1.
  intros n LT; clear LT.
  unfold mult; rewrite plus_0_r.
  apply (well_founded_induction
           lt_wf
           (fun n => diff_time n <= diff_time2 n)).
  clear n; intros n IND.
  destruct n.
  compute.
  omega.
  remember (even_or_odd (S n)) as EO; destruct EO; clear HeqEO.

  rewrite diff_time_nz_even; auto.
  unfold_sub diff_time2 (diff_time2 (S n)).
  apply le_plus_right.
  apply (le_trans (diff_time (div2 (n - 1)))
                  (diff_time2 (div2 (n - 1)))
                  (diff_time2 (div2 n))).
  apply IND; auto.
  destruct n.
  compute.
  omega.
  replace (S n - 1) with n;[|omega].
  inversion e; subst.
  inversion H0; subst.
  rewrite <- even_div2; auto.

  rewrite diff_time_nz_odd; auto.
  unfold_sub diff_time2 (diff_time2 (S n)).
  apply (le_trans (11 + diff_time (div2 n))
                  (11 + diff_time2 (div2 n))
                  (13 + diff_time2 (div2 n))).
  apply le_plus_right.
  apply IND;auto.
  apply le_plus_left.
  omega.
Qed.

Lemma diff_time2_big_oh_fl_log : big_oh diff_time2 fl_log.
Proof.
  exists 1. exists 17.
  apply (well_founded_induction
           lt_wf
           (fun n => 1 <= n -> diff_time2 n <= 17 * fl_log n)).
  intros n IND LT.
  destruct n; intuition.
  clear LT.  
  destruct n.
  compute.
  omega.
  destruct n.
  compute.
  omega.
  remember (S (S n)) as m.
  unfold_sub diff_time2 (diff_time2 (S m)).
  unfold_sub fl_log (fl_log (S m)).
  subst m.
  replace (div2 (S (S n))) with (S (div2 n));[|unfold div2;omega].
  apply (le_trans (13 + diff_time2 (S (div2 n)))
                  (13 + 17 * fl_log (S (div2 n)))
                  (17 * S (fl_log (S (div2 n))))); try omega.
  apply le_plus_right.
  apply IND; auto.
  omega.
Qed.

Theorem size_big_oh_fl_log : big_oh diff_time fl_log.
  apply (big_oh_trans diff_time diff_time2 fl_log).
  apply diff_time12.
  apply diff_time2_big_oh_fl_log.
Qed.

Program Fixpoint size_time n {measure n} :=
  match n with
    | 0 => 3
    | S n' => 
      13 + diff_time (div2 n') + size_time (div2 n')
  end.

Definition size_result (A:Set) (b : @bin_tree A) n c :=
  forall m,
    (Braun b m -> (n = m /\ c = size_time n)).

Load "size_log_sq_gen.v".

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
  unfold_sub size_time (size_time (S (m + (m + 0) + zo))).

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
  replace (t_size + (t_size + 0) + 0) with (t_size + t_size); [|omega].
  rewrite double_div2.
  split; try omega.

  apply SIZE_DIFF in BRAUNS. destruct BRAUNS as [EQo EQxn]. subst.
  replace (t_size + (t_size + 0) + 1) with (S (t_size + t_size)); [|omega].
  rewrite div2_with_odd_argument.
  split; try omega.
Qed.

Program Fixpoint size_time2 n {measure n} :=
  match n with
    | 0 => 0
    | S n' => 
      1 + diff_time (div2 n') + size_time2 (div2 n')
  end.

Lemma size_time12 : big_oh size_time size_time2.
  exists 1.
  exists 17.
  apply (well_founded_ind
           lt_wf
           (fun n =>  1 <= n -> size_time n <= 17 * size_time2 n)).
  intros n IND LT.
  destruct n; intuition.
  clear LT.
  destruct n. compute. omega.
  destruct n. compute. omega.
  remember (S (S n)) as m.
  unfold_sub size_time (size_time (S m)).
  unfold_sub size_time2 (size_time2 (S m)).
  subst m.
  replace (div2 (S (S n))) with (S (div2 n)); [|simpl;omega].
  rewrite mult_plus_distr_l.
  rewrite mult_plus_distr_l.
  apply (le_trans (13 + diff_time (S (div2 n)) + size_time (S (div2 n)))
                  (13 + diff_time (S (div2 n)) + 17 * size_time2 (S (div2 n)))
                  (17 * 1 + 17 * diff_time (S (div2 n)) + 17 * size_time2 (S (div2 n))));
    try omega.
  apply le_plus_right.
  apply IND;auto.
  omega.
Qed.

Definition size_time3 n := fl_log n * diff_time n.

Lemma size_time23 : big_oh size_time2 size_time3.
  exists 0.
  exists 1.
  intros n LT.
  unfold mult.
  rewrite plus_0_r.
  clear LT.
  unfold size_time3.
  apply (well_founded_induction
           lt_wf
           (fun n => size_time2 n <= fl_log n * diff_time n)).
  clear n. intros n IND.
  destruct n.
  compute. 
  omega.
  unfold_sub size_time2 (size_time2 (S n)).
  rewrite fl_log_div2'.
  replace (S (fl_log (div2 n))) with (1 + fl_log (div2 n));[|omega].
  rewrite mult_plus_distr_r.
  replace (1 * diff_time (S n)) with (diff_time (S n)); [|omega].
  apply (le_trans (1 + diff_time (div2 n) + size_time2 (div2 n))
                  (diff_time (S n) + size_time2 (div2 n))
                  (diff_time (S n) + fl_log (div2 n) * diff_time (S n))).
  apply le_plus_left.
  unfold_sub diff_time (diff_time (S n)).
  dispatch_if x x'; fold_sub diff_time.
  inversion x; subst.
  destruct n.
  inversion H0.
  replace (S n - 1) with n;[|omega].
  inversion H0.
  subst.
  rewrite <- even_div2; auto.
  omega.
  omega.
  
  apply le_plus_right.
  apply (le_trans (size_time2 (div2 n))
                  (fl_log (div2 n) * diff_time (div2 n))
                  (fl_log (div2 n) * diff_time (S n))).
  apply IND;auto.
  apply le_mult_right.
  unfold_sub diff_time (diff_time (S n)).
  dispatch_if x x'; fold_sub diff_time; try omega.
  inversion x; subst.
  destruct n.
  compute.
  omega.
  inversion H0; subst.
  replace (S n - 1) with n; [|omega].
  rewrite <- even_div2; auto.
  omega.
Qed.

Theorem size_logsq : big_oh size_time (fun n => fl_log n * fl_log n).
Proof.
  apply (big_oh_trans size_time size_time2
                      (fun n => fl_log n * fl_log n)).
  apply size_time12.
  apply (big_oh_trans size_time2 size_time3
                      (fun n => fl_log n * fl_log n)).
  apply size_time23.
  unfold size_time3.
  apply big_oh_mult.
  apply size_big_oh_fl_log.
Qed.
