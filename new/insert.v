Require Import util log braun.
Require Import Omega.
Require Import Arith Arith.Even Arith.Div2.

Section insert.
  Variable A : Set.

  Inductive InsertR : A -> (bin_tree A) -> (bin_tree A) -> nat -> Prop :=
  | IR_mt :
      forall (x:A),
        InsertR x (bt_mt A) (bt_node x (bt_mt A) (bt_mt A)) 1
  | IR_node :
      forall (x:A) (y:A) (s:(bin_tree A)) (t t':(bin_tree A)) (n:nat),
        InsertR y t t' n ->
        InsertR x (bt_node y s t) (bt_node x t' s) (S n).
  Hint Constructors InsertR.

  Theorem insert :
    forall (x:A) (bt:(bin_tree A)),
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

  Theorem InsertR_Braun :
    forall (x:A) (n n':nat) (bt bt':(bin_tree A)),
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

    constructor.

    constructor.

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
    forall (x:A) (n n':nat) (bt bt':(bin_tree A)),
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
End insert.
