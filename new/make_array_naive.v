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

Fixpoint man_time n : nat :=
  match n with
    | 0 => 0
    | S n' => man_time n' + (fl_log n' + 1)
  end.

Example man_time_ex :
  map man_time (1 :: 2 :: 3 :: 4 ::  5 ::  6 ::  7 ::  8 ::  9 :: 10 :: nil)
  = (1 :: 3 :: 5 :: 8 :: 11 :: 14 :: 17 :: 21 :: 25 :: 29 :: nil).
Proof.
  auto.
Qed.

Lemma man_time_nlogn :
  forall n,
    man_time n <= n * fl_log n.
Proof.
  induction n as [|n].

  simpl. omega.
  remember (man_time (S n)) as m.
  simpl in Heqm.
  subst.

  (* XXX ? *)
  admit.
Qed.
Hint Resolve man_time_nlogn.

Theorem MakeArrayNaiveR_time :
  forall xs bt t,
    MakeArrayNaiveR xs bt t ->
    t = man_time (length xs).
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
Hint Rewrite MakeArrayNaiveR_time.

Theorem MakeArrayNaiveR_bound :
  forall xs bt t,
    MakeArrayNaiveR xs bt t ->
    t <= (length xs) * fl_log (length xs).
Proof.
  intros xs bt t MALR.
  rewrite (MakeArrayNaiveR_time xs bt t); eauto.
Qed.
