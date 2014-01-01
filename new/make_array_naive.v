Require Import braun log insert util index list_util sequence.
Require Import Arith Arith.Even Arith.Div2 List.
Require Import Program.
Require Import Omega.

Inductive MakeArrayNaiveR : list A -> bin_tree -> nat -> Prop :=
| MALR_zero :
    MakeArrayNaiveR nil bt_mt 0
| MALR_succ :
    forall x xs bt bt' time insert_time,
      InsertR x bt bt' insert_time ->
      MakeArrayNaiveR        xs bt                  time ->
      MakeArrayNaiveR (x :: xs) bt' (time + insert_time).
Hint Constructors MakeArrayNaiveR.

Theorem MakeArrayNaiveR_SequenceR :
  forall xs bt n,
    MakeArrayNaiveR xs bt n ->
    SequenceR bt xs.
Proof.
  intros xs bt n MALR.
  induction MALR; eauto.
  eapply InsertR_SequenceR; eauto.
Qed.
Hint Resolve MakeArrayNaiveR_SequenceR.

Theorem make_array_naive :
  forall xs,
    { bt | exists n, MakeArrayNaiveR xs bt n }.
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

Theorem MakeArrayNaiveR_Braun :
  forall xs bt n,
    MakeArrayNaiveR xs bt n ->
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
Hint Resolve MakeArrayNaiveR_Braun.

Theorem MakeArrayNaiveR_correct :
  forall xs bt n,
    MakeArrayNaiveR xs bt n ->
    forall i x,
      IndexR bt i x ->
      ListIndexR xs i x.
Proof.
  intros. eauto.
Qed.
Hint Resolve MakeArrayNaiveR_correct.

Theorem MakeArrayNaiveR_time :
  forall xs bt t,
    MakeArrayNaiveR xs bt t ->
    t = nlogn (length xs).
Proof.
  intros xs bt t MALR.
  induction MALR; eauto.
  rename H into IR.
  subst.
  apply MakeArrayNaiveR_Braun in MALR.
  eapply (InsertR_time _ _ _ _ _ MALR) in IR.
  subst.
  auto.
Qed.
