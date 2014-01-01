Require Import util log braun sequence list.
Require Import Omega.
Require Import Arith Arith.Even Arith.Div2.

Inductive InsertR : A -> bin_tree -> bin_tree -> nat -> Prop :=
| IR_mt :
    forall (x:A),
      InsertR x bt_mt (bt_node x bt_mt bt_mt) 1
| IR_node :
    forall (x:A) (y:A) (s:bin_tree) (t t':bin_tree) (n:nat),
      InsertR y t t' n ->
      InsertR x (bt_node y s t) (bt_node x t' s) (S n).
Hint Constructors InsertR.

Theorem InsertR_fun :
  forall (a : A) (b b' : bin_tree) (rt : nat),
    InsertR a b b' rt ->
    forall (_b' : bin_tree) (_rt : nat),
      InsertR a b _b' _rt -> b' = _b' /\ rt = _rt.
Proof.
  intros a b b' rt IR.

  induction IR; intros _b' _rt IR'; invclr IR'; eauto.
  destruct (IHIR _ _ H5). subst. eauto.
Qed.

Theorem insert :
  forall (x:A) (bt:bin_tree),
    { bt' | exists n, InsertR x bt bt' n }.
Proof.
  intros x bt.
  generalize x. clear x.
  induction bt as [|y s t]; intros x.

  eauto.

  destruct (IHbt1 y) as [t' IR].
  exists (bt_node x t' s).
  destruct IR as [n IR].
  eauto.
Defined.

Lemma InsertR_dec :
  forall (a : A) (b : bin_tree),
    {b' : bin_tree | exists rt : nat, InsertR a b b' rt} +
    {(forall (b' : bin_tree) (rt : nat), ~ InsertR a b b' rt)}.
Proof.
  intros a b.
  destruct (insert a b).
  eauto.
Defined.

Theorem InsertR_Braun :
  forall (x:A) (n n':nat) (bt bt':bin_tree),
    Braun bt n ->
    InsertR x bt bt' n' ->
    Braun bt' (S n).
Proof.
  intros x n n' bt.
  generalize x n n'. clear x n n'.
  induction bt as [|y s t]; intros x n n' bt' BT IR.

  inversion_clear BT.
  inversion_clear IR.
  replace 1 with (0 + 0 + 1); try omega.
  eapply B_node; eauto.
  omega.

  rename t into IHs.
  rename bt1 into t.
  rename IHbt1 into IHt.
  inversion_clear IR.
  rename H into IR.
  inversion_clear BT.
  rename H into BP.
  rename H0 into BPs.
  rename H1 into BPt.
  replace (S (s_size + t_size + 1)) with ((t_size + 1) + s_size + 1); try omega.
  apply IHt with (n:=t_size) in IR.
  eapply B_node; eauto.
  omega.
  eauto.
  replace (t_size +1) with (S t_size); try omega.
  auto.
  auto.
Qed.

Theorem InsertR_time :
  forall (x:A) (n n':nat) (bt bt':bin_tree),
    Braun bt n ->
    InsertR x bt bt' n' ->
    n' = (fl_log n + 1).
Proof.
  intros x n n' bt bt' BP IR.
  generalize n BP. clear n BP.
  induction IR; intros BPn BP.

  inversion_clear BP.
  simpl.
  auto.

  inversion_clear BP.
  apply braun_invariant_implies_fl_log_property in H.
  apply IHIR in H1.
  omega.
Qed.

Lemma InsertR_SequenceR:
  forall t ts y t' n,
    SequenceR t ts ->
    InsertR y t t' n ->
    SequenceR t' (y :: ts).
Proof.
  induction t as [|x s IHs t IHt]; intros ts y t' n SR IR.

  invclr SR. invclr IR.
  cut (nil = interleave A nil nil). intros EQ; rewrite EQ.
  eapply SR_node; eauto.
  auto.

  invclr SR. rename H3 into SRs. rename H4 into SRt.
  invclr IR. rename H5 into IR. rename ts0 into ts.
  rename t'0 into t'.
  rewrite interleave_case2.
  eapply SR_node; eauto.
Qed.
