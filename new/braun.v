Require Import util log.
Require Import Omega.
Require Import Arith Arith.Even Arith.Div2.

Set Implicit Arguments.

Variable A : Set.

Inductive bin_tree : Set :=
| bt_mt : bin_tree
| bt_node : A -> bin_tree -> bin_tree -> bin_tree.
Hint Constructors bin_tree.

Inductive Braun : bin_tree -> nat -> Prop :=
| B_mt :
    Braun bt_mt 0
| B_node :
    forall (x:A) s s_size t t_size,
      t_size <= s_size <= t_size+1 ->
      Braun s s_size ->
      Braun t t_size ->
      Braun (bt_node x s t) (s_size+t_size+1).
Hint Constructors Braun.

Inductive InsertR : A -> bin_tree -> bin_tree -> nat -> Prop :=
| IR_mt :
    forall (x:A),
      InsertR x bt_mt (bt_node x bt_mt bt_mt) 1
| IR_node :
    forall (x:A) (y:A) (s:bin_tree) (t t':bin_tree) (n:nat),
      InsertR y t t' n ->
      InsertR x (bt_node y s t) (bt_node x t' s) (S n).
Hint Constructors InsertR.

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
Qed.

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

Require Import List.

Program Fixpoint inserts l :=
  match l with
      | nil =>
        bt_mt
      | x :: l =>
        insert x (inserts l)
  end.

Theorem inserts_Braun :
  forall l,
    Braun (inserts l) (length l).
Proof.
  induction l as [|x l]; simpl.
  eauto.

  remember (insert x (inserts l)) as I.
  destruct I as [bt' [n IR]].
  simpl.
  eapply InsertR_Braun.
  apply IHl.
  apply IR.
Qed.

Set Extraction AccessOpaque.
Recursive Extraction inserts.
