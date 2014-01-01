Require Import braun log insert util index list sequence.
Require Import Arith Arith.Even Arith.Div2 List.
Require Import Program.
Require Import Omega.

Inductive MakeArrayLinearR : list A -> bin_tree -> nat -> Prop :=
| MALR_zero :
    MakeArrayLinearR nil bt_mt 0
| MALR_succ :
    forall x xs bt bt' time insert_time,
      InsertR x bt bt' insert_time ->
      MakeArrayLinearR        xs bt                  time ->
      MakeArrayLinearR (x :: xs) bt' (time + insert_time).
Hint Constructors MakeArrayLinearR.

Theorem MakeArrayLinearR_SequenceR :
  forall xs bt n,
    MakeArrayLinearR xs bt n ->
    SequenceR bt xs.
Proof.
  intros xs bt n MALR.
  induction MALR; eauto.
  eapply InsertR_SequenceR; eauto.
Qed.

Theorem make_array_linear :
  forall xs,
    { bt | exists n, MakeArrayLinearR xs bt n }.
Proof.
  induction xs as [| x xs]; [eauto |].
  destruct IHxs as [bt IR].
  remember (insert x bt).
  clear Heqs.
  destruct s as [bt' insIR'].
  exists bt'.
  destruct IR as [indTime indR].
  destruct insIR' as [insTime insIR].
  exists (indTime + insTime).
  apply (MALR_succ _ _ bt); eauto.
Defined.

Theorem MakeArrayLinearR_Braun :
  forall xs bt n,
    MakeArrayLinearR xs bt n ->
    Braun bt (length xs).
Proof.
  intro xs.
  induction xs as [| x xs]; intros bt n MkArrR.

  simpl.
  inversion_clear MkArrR.
  constructor.

  simpl.
  inversion_clear MkArrR.
  apply (InsertR_Braun x (length xs) insert_time bt0).
  apply (IHxs bt0 time H0).
  assumption.
Qed.

Theorem MakeArrayLinearR_correct :
  forall xs bt n,
    MakeArrayLinearR xs bt n ->
    forall i x,
      IndexR bt i x ->
      ListIndexR xs i x.
Proof.
  intros xs bt n MALR i x IR.
  eapply SequenceR_IndexR.
  apply IR.
  eapply MakeArrayLinearR_Braun.
  apply MALR.
  eapply MakeArrayLinearR_SequenceR.
  apply MALR.
Qed.

Theorem MakeArrayLinearR_time :
  forall xs bt t,
    MakeArrayLinearR xs bt t ->
    t = nlogn (length xs).
Proof.
  intros xs bt t MALR.
  induction MALR.
  auto.
  rename H into IR.
  subst.
  apply MakeArrayLinearR_Braun in MALR.
  eapply (InsertR_time _ _ _ _ _ MALR) in IR.
  subst.
  simpl.
  auto.
Qed.
