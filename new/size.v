Require Import braun util log.
Require Import Coq.Program.Tactics Coq.Program.Wf.
Require Import Arith Arith.Even Arith.Div2.
Set Implicit Arguments.

Inductive SizeLinearR {A:Set} : (@bin_tree A) -> nat -> nat -> Prop :=
| SLR_mt :
    SizeLinearR bt_mt 0 0
| SLR_node :
    forall y s t s_sz s_time t_sz t_time,
      SizeLinearR s s_sz s_time ->
      SizeLinearR t t_sz t_time ->
      SizeLinearR (bt_node y s t) (s_sz + t_sz + 1) (s_time + t_time + 1).
Hint Constructors SizeLinearR.

Theorem size_linear :
  forall A (bt:@bin_tree A),
    { sz | exists t, SizeLinearR bt sz t }.
Proof.
  induction bt as [|y s IS t IT].

  exists 0. eauto.
  destruct IS as [s_sz IS].
  destruct IT as [t_sz IT].
  exists (s_sz + t_sz + 1).
  destruct IS as [s_time IS].
  destruct IT as [t_time IT].
  exists (s_time + t_time + 1).
  eauto.
Defined.

Theorem SizeLinearR_correct_and_time :
  forall A (bt:@bin_tree A) n,
    Braun bt n ->
    SizeLinearR bt n n.
Proof.
  induction bt as [|y s IS t IT]; intros n B;
  inversion_clear B; eauto.
Qed.
Hint Resolve SizeLinearR_correct_and_time.

Inductive DiffR {A:Set} : @bin_tree A -> nat -> nat -> nat -> Prop :=
| DR_mt :
    DiffR bt_mt 0 0 0
| DR_single :
    forall x,
      DiffR (bt_node x bt_mt bt_mt) 0 1 1
| DR_one :
    forall x s t s_df s_time k,
      DiffR s k s_df s_time ->
      DiffR (bt_node x s t) (2 * k + 1) s_df (s_time+1)
| DR_two :
    forall x s t t_df t_time k,
      DiffR t k t_df t_time ->
      DiffR (bt_node x s t) (2 * k + 2) t_df (t_time+1).
Hint Constructors DiffR.

Lemma DiffR_fun :
  forall A (s:@bin_tree A) m df dt,
    DiffR s m df dt ->
    forall df' dt',
      DiffR s m df' dt' ->
      df = df' /\ dt = dt'.
Proof.
  intros A s m df dt DR.
  induction DR; intros df' dt' DR';
  inversion DR'; subst; clear DR'; try omega;
  replace k0 with k in *; try omega;
  apply IHDR in H5; omega.
Qed.
Hint Rewrite DiffR_fun.

Theorem DiffR_correct_ans :
  forall A (s:@bin_tree A) m df t,
    DiffR s m df t ->
    (df = 0 \/ df = 1).
Proof.
  intros A s m df t DR.
  induction DR; auto.
Qed.
Hint Resolve DiffR_correct_ans.

Theorem DiffR_correct_zero :
  forall A (s:@bin_tree A) m,
    Braun s m ->
    exists t, DiffR s m 0 t.
Proof.
  intros A s m B.
  induction B; eauto.

  assert (s_size = t_size \/ s_size = t_size + 1) as CASES; try omega.
  destruct CASES as [EQ|EQ]; subst.

  replace (t_size + t_size + 1) with (2 * t_size + 1); try omega.
  destruct IHB1 as [s_time Ds].
  exists (s_time+1).
  eauto.

  replace (t_size + 1 + t_size + 1) with (2 * t_size + 2); try omega.
  destruct IHB2 as [t_time Dt].
  exists (t_time+1).
  eauto.
Qed.
Hint Resolve DiffR_correct_zero.

Theorem DiffR_correct_one :
  forall A (s:@bin_tree A) m,
    Braun s (m+1) ->
    exists t, DiffR s m 1 t.
Proof.
  intros A s m B.
  remember (m+1) as n.
  generalize m Heqn. clear m Heqn.
  induction B; intros m Heqn.

  omega.

  destruct s_size as [|s_size];
    destruct t_size as [|t_size].

  exists 1.
  replace m with 0 in *; try omega.
  inversion B1; try omega.
  inversion B2; try omega.
  eapply DR_single.

  destruct (IHB2 m); omega.

  assert (s_size = 0); try omega. subst.
  replace m with 1 in *; try omega.
  destruct (IHB1 0) as [s_time Ds]; try omega.
  exists (s_time+1).
  replace 1 with (2 * 0 + 1); try omega.
  eapply DR_one.
  auto.

  replace m with (S s_size + S t_size) in *; try omega.
  clear Heqn.

  assert (s_size = t_size \/ s_size = t_size + 1) as CASES; try omega.
  destruct CASES as [EQ|EQ]; subst.

  destruct (IHB2 t_size) as [t_time Dt]; try omega.
  exists (t_time+1).
  replace (S t_size + S t_size) with (2 * t_size + 2); try omega.
  eapply DR_two. auto.

  destruct (IHB1 (t_size+1)) as [s_time Ds]; try omega.
  exists (s_time+1).
  replace (S (t_size + 1) + S t_size) with (2 * (t_size + 1) + 1); try omega.
  eapply DR_one. auto.
Qed.
Hint Resolve DiffR_correct_one.

Theorem DiffR_time_zero :
  forall A (bt:@bin_tree A) n dt,
    DiffR bt n 0 dt ->
    dt = fl_log n.
Proof.
  intros A bt n dt DR.
  remember 0 in DR.
  rename n0 into df.
  rename Heqn0 into EQ.
  induction DR.

  auto.
  congruence.

  apply IHDR in EQ. subst.
  symmetry.
  replace (2 * k) with (k + k); try omega.
  apply fl_log_odd.

  apply IHDR in EQ. subst.
  symmetry.
  replace (2 * k + 2) with (k + 1 + (k + 1)); try omega.
  apply fl_log_even.
Qed.
Hint Rewrite DiffR_time_zero.

Theorem DiffR_time_one :
  forall A (bt:@bin_tree A) n dt,
    DiffR bt n 1 dt ->
    dt = cl_log (n+1).
Proof.
  intros A bt n dt DR.
  remember 1 in DR.
  rename n0 into df.
  rename Heqn0 into EQ.
  induction DR.

  congruence.
  simpl. auto.

  apply IHDR in EQ; clear IHDR. subst.
  replace (2 * k + 1 + 1) with (k + 1 + k + 1); try omega.
  apply cl_log_even.

  apply IHDR in EQ; clear IHDR. subst.
  symmetry.
  replace (2 * k + 2 + 1) with ((k + 1) + (k + 1) + 1); try omega.
  apply cl_log_odd.
Qed.
Hint Rewrite DiffR_time_one.

Theorem DiffR_time :
  forall A (bt:@bin_tree A) n df dt,
    DiffR bt n df dt ->
    (dt = fl_log n) \/ (dt = cl_log (n + 1)).
Proof.
  intros A bt n df dt DR.
  destruct (DiffR_correct_ans DR); subst.

  left. apply (DiffR_time_zero DR).
  right. apply (DiffR_time_one DR).
Qed.
Hint Resolve DiffR_time.

Theorem diff_dec :
  forall A (bt:@bin_tree A) m,
    { df | exists t, DiffR bt m df t } +
    { forall df t, ~ DiffR bt m df t }.
Proof.
  induction bt as [|y s IS t IT]; intros m.

  destruct m as [|m'].
  left. eauto.
  right. intros df t DR. inversion DR.

  destruct m as [|m'].

  destruct s as [|sx ss st];
    destruct t as [|tx ts tt]; eauto; right;
    intros df dt DR;
    inversion DR; clear DR; subst; try omega.

  destruct (even_odd_dec m') as [E | O].

  apply even_2n in E.
  destruct E as [k E]; subst.
  destruct (IS k) as [ [s_df ISk] | ISk_Fail ].
  left. exists s_df.
  destruct ISk as [s_time ISk].
  exists (s_time+1).
  unfold double.
  replace (S (k + k)) with (2 * k + 1); try omega.
  eauto.

  right. intros df dt DR.
  inversion DR; clear DR; subst.
  unfold double in *.
  replace k0 with k in *; try omega.
  eapply ISk_Fail. apply H5.

  unfold double in *.
  omega.

  apply odd_S2n in O.
  destruct O as [k O]; subst.
  destruct (IT k) as [[t_df ITk] | ITk_Fail ].
  left. exists t_df.
  destruct ITk as [t_time ITk].
  exists (t_time+1).
  unfold double.
  replace (S (S (k + k))) with (2 * k + 2); try omega.
  eauto.

  right. intros df dt DR.
  inversion DR; clear DR; subst;
  unfold double in *.

  omega.

  replace k0 with k in *; try omega.
  eapply ITk_Fail. apply H5.
Defined.

Theorem diff_Braun :
  forall A (bt:@bin_tree A) m,
    (Braun bt m) \/ (Braun bt (m+1)) ->
    exists df t,
      DiffR bt m df t.
Proof.
  intros A bt m [B | B].
  eauto.
  exists 1.
  eauto.
Qed.

Theorem diff :
  forall A (bt:@bin_tree A) m,
    (Braun bt m) \/ (Braun bt (m+1)) ->
    { df | exists t, DiffR bt m df t }.
Proof.
  intros A bt m Bor.
  destruct (diff_dec bt m) as [OK | FAIL].
  eauto.
  apply diff_Braun in Bor.
  assert False; try tauto.
  destruct Bor as [df [t DR]].
  apply FAIL in DR.
  auto.
Defined.

Inductive SizeR {A:Set} : (@bin_tree A) -> nat -> nat -> Prop :=
| SR_mt :
    SizeR bt_mt 0 0
| SR_node :
    forall x s t m t_time s_df s_time,
      SizeR t m t_time ->
      DiffR s m s_df s_time ->
      SizeR (bt_node x s t) (1 + 2 * m + s_df) (s_time + t_time + 1).
Hint Constructors SizeR.

Theorem SizeR_correct :
  forall A (bt:@bin_tree A) n,
    Braun bt n ->
    exists t, SizeR bt n t.
Proof.
  induction bt as [|y s IS t IT]; intros n B;
  inversion_clear B; eauto.

  clear IS.
  rename H0 into Bs.
  rename H1 into Bt.
  apply IT in Bt.
  destruct Bt as [t_time SRt].

  assert (s_size = t_size \/ s_size = t_size + 1) as CASES; try omega.
  destruct CASES as [EQ|EQ]; subst.

  replace (t_size + t_size + 1) with (1 + 2 * t_size + 0); try omega.
  apply DiffR_correct_zero in Bs.
  destruct Bs as [s_time Ds].
  exists (s_time + t_time + 1).
  eapply SR_node; eauto.

  replace (t_size + 1 + t_size + 1) with (1 + 2 * t_size + 1); try omega.
  apply DiffR_correct_one in Bs.
  destruct Bs as [s_time Ds].
  exists (s_time + t_time + 1).
  eapply SR_node; eauto.
Qed.
Hint Resolve SizeR_correct.

Theorem SizeR_time :
  forall A (bt:@bin_tree A) n st,
    SizeR bt n st ->
    st = sum_of_logs n.
Proof.
  intros A bt n st SR.
  induction SR.

  auto.

  subst.
  rename H into DR.
  destruct (DiffR_correct_ans DR); subst.

  apply DiffR_time_zero in DR. subst.
  replace (1 + 2 * m + 0) with (m + m + 1); try omega.
  rewrite <- sum_of_logs_odd.
  cut (fl_log m + 1 = fl_log (m + m + 1)).
  intros EQ. omega.
  symmetry.
  apply fl_log_odd.

  apply DiffR_time_one in DR. subst.
  replace (1 + 2 * m + 1) with (m + 1 + m + 1); try omega.
  rewrite <- sum_of_logs_even.
  cut (cl_log (m+1) + 1 = cl_log (m + 1 + m + 1)).
  intros EQ. omega.
  apply cl_log_even.
Qed.
Hint Rewrite SizeR_time.

Lemma SizeR_fun :
  forall A (s:@bin_tree A) sz st,
    SizeR s sz st ->
    forall sz' st',
      SizeR s sz' st' ->
      sz = sz' /\ st = st'.
Proof.
  intros A s sz st SR.

  induction SR; intros sz' st' SR';
  inversion SR'; clear SR'; subst;
  try (split; omega).

  destruct (IHSR m0 t_time0 H5); subst m0 t_time0.
  destruct (DiffR_fun H H6); subst.
  omega.
Qed.
Hint Rewrite SizeR_fun.

Theorem size_dec :
  forall A (bt:@bin_tree A),
    { sz | exists t, SizeR bt sz t } +
    { forall sz t, ~ SizeR bt sz t }.
Proof.
  induction bt as [|y s IS t IT].
  eauto.
  clear IS.
  destruct IT as [[m IT] | FAIL ].
  destruct (diff_dec s m) as [[s_df DS] | DFAIL ].
  left. exists (1 + 2 * m + s_df).
  destruct IT as [t_time IT].
  destruct DS as [s_time DS].
  eauto.

  right. intros sz st SR.
  inversion SR; clear SR; subst.
  destruct IT as [t_time' SRt].
  replace m0 with m in *.
  eapply DFAIL. apply H5.
  destruct (SizeR_fun SRt H4); auto.

  right. intros sz st SR.
  inversion SR; clear SR; subst.
  eapply FAIL; apply H4.
Defined.

Theorem size :
  forall A (bt:@bin_tree A) m,
    Braun bt m ->
    { sz | exists t, SizeR bt sz t }.
Proof.
  intros A bt m B.
  destruct (size_dec bt) as [ OK | FAIL ]; eauto.
Defined.
