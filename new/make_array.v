Require Import braun log insert util.
Require Import Arith List.

Section naive1.
  Variable A : Set.

  Inductive MkArrNaive1R : list A -> bin_tree A -> nat -> Prop :=
  | naive1R_zero : 
      MkArrNaive1R nil (bt_mt A) 0
  | naive1R_suc  :
      forall x xs bt bt' time insert_time,
        InsertR A x bt bt' insert_time ->
        MkArrNaive1R        xs bt                  time ->
        MkArrNaive1R (x :: xs) bt' (time + insert_time).
  Hint Constructors MkArrNaive1R.

  Theorem make_array_naive1 :
    forall xs,
      { bt | exists n, MkArrNaive1R xs bt n }.
  Proof.
    induction xs as [| x xs]; [eauto |].
    destruct IHxs as [bt IR].
    remember (insert A x bt).
    clear Heqs.
    destruct s as [bt' insIR'].
    exists bt'.
    destruct IR as [indTime indR].
    destruct insIR' as [insTime insIR].
    exists (indTime + insTime).
    apply (naive1R_suc _ _ bt); eauto.
  Defined.
  
  Theorem MkArrNaive1R_Braun :
    forall xs bt n,
      MkArrNaive1R xs bt n ->
      Braun bt (length xs).
  Proof.
    intro xs.
    induction xs as [| x xs]; intros bt n MkArrR.

    simpl.
    inversion_clear MkArrR.
    constructor.

    simpl.
    inversion_clear MkArrR.
    apply (InsertR_Braun A x (length xs) insert_time bt0).
    apply (IHxs bt0 time H0).
    assumption.
  Qed.

  Fixpoint rt_naive n : nat :=
    match n with
      | 0 => 0
      | S n' => rt_naive n' + (fl_log n' + 1)
    end.

  Example rt_naive_ex :
    map rt_naive (1 :: 2 :: 3 :: 4 ::  5 ::  6 ::  7 ::  8 ::  9 :: 10 :: nil)
               = (1 :: 3 :: 5 :: 8 :: 11 :: 14 :: 17 :: 21 :: 25 :: 29 :: nil).
  Proof.
    auto.
  Qed.

  (* Helper *)
  Theorem MkArrNaive1R_time_help :
    forall xs bt n,
      MkArrNaive1R xs bt n ->
      n = rt_naive (length xs) /\ Braun bt (length xs).
  Proof.
    intros xs bt n IndR.
    induction IndR.
    split; simpl; constructor.

    assert (Braun bt' (length (x :: xs))).

    apply (InsertR_Braun _ x (length xs) insert_time bt bt').
    destruct IHIndR; assumption.
    assumption.
        
    split; [| assumption].

    destruct IHIndR as [IHTime IHBraun].
    simpl; subst.
    cut (insert_time = (fl_log (length xs) + 1)); try omega.
    apply (InsertR_time A x _ _ bt bt'); auto.
  Qed.
  
  Theorem MkArrNaive1R_time :
    forall xs bt n,
      MkArrNaive1R xs bt n ->
      n = rt_naive (length xs).
  Proof.
    apply MkArrNaive1R_time_help.
  Qed.  
End naive1.
