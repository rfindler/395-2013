Require Import braun log insert util.
Require Import Arith Arith.Even Arith.Div2 List.
Require Import Omega.

Section array.
  Variable A : Set.

  Inductive IndexR : bin_tree A -> nat -> A -> Prop :=
    | IR_zero :
        forall x s t,
          IndexR (bt_node x s t) 0 x
    | IR_left :
        forall x s t i y,
          IndexR s i y ->
          IndexR (bt_node x s t) (2 * i + 1) y
    | IR_right :
        forall x s t i y,
          IndexR t i y ->
          IndexR (bt_node x s t) (2 * i + 2) y.
  Hint Constructors IndexR.

  Theorem index_dec :
    forall bt i,
      { x | IndexR bt i x } +
      { forall x, ~ IndexR bt i x }.
  Proof.
    intros bt.
    induction bt as [|x s IRs t IRt]; intros i.

    right. intros x IR.
    inversion IR.

    destruct i as [|i].
    left. eauto.

    destruct (even_odd_dec i) as [E | O].

    apply even_2n in E. 
    destruct E as [k EQ]. subst.
    unfold double.
    replace (S (k + k)) with (2 * k + 1); try omega.
    destruct (IRs k) as [[y IRs_k] | FAIL].
    left. eauto.
    right. intros y IR.
    inversion IR; clear IR; subst; try omega.
    replace i with k in *; try omega.
    apply (FAIL y); auto.

    apply odd_S2n in O.
    destruct O as [k EQ]. subst.
    unfold double.
    replace (S (S (k + k))) with (2 * k + 2); try omega.
    destruct (IRt k) as [[y IRt_k] | FAIL].
    left. eauto.
    right. intros y IR.
    inversion IR; clear IR; subst; try omega.
    replace i with k in *; try omega.
    apply (FAIL y); auto.
  Defined.

  Theorem index_Braun :
    forall bt n,
      Braun bt n ->
      forall i,
        i < n ->
        exists x,
          IndexR bt i x.
  Proof.
    induction bt as [|x s Is t It];
    intros n B i LT.

    inversion B. omega.

    inversion B; clear B; subst.
    rename H2 into BP.
    rename H4 into Bs.
    rename H5 into Bt.
    destruct i as [|i].
    eauto.
    destruct (even_odd_dec i) as [E | O].

    apply even_2n in E. destruct E as [k EQ]; subst.
    unfold double in *.
    destruct (Is s_size Bs k) as [y IRs]; try omega.
    replace (S (k + k)) with (2 * k + 1); try omega.
    eauto.

    apply odd_S2n in O. destruct O as [k EQ]; subst.
    unfold double in *.
    destruct (It t_size Bt k) as [y IRt]; try omega.
    replace (S (S (k + k))) with (2 * k + 2); try omega.
    eauto.
  Qed.

  Theorem index :
    forall bt n,
      Braun bt n ->
      forall i,
        i < n ->
        { x | IndexR bt i x }.
  Proof.
    intros bt n B i LT.
    destruct (index_dec bt i) as [OK | FAIL].
    auto.
    assert False; try tauto.
    destruct (index_Braun bt n B i LT) as [y IR].
    apply (FAIL y). auto.
  Defined.

  Inductive MakeArrayLinearR : list A -> bin_tree A -> nat -> Prop :=
  | MALR_zero : 
      MakeArrayLinearR nil (bt_mt A) 0
  | MALR_suc  :
      forall x xs bt bt' time insert_time,
        InsertR A x bt bt' insert_time ->
        MakeArrayLinearR        xs bt                  time ->
        MakeArrayLinearR (x :: xs) bt' (time + insert_time).
  Hint Constructors MakeArrayLinearR.

  Theorem make_array_linear :
    forall xs,
      { bt | exists n, MakeArrayLinearR xs bt n }.
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
    apply (MALR_suc _ _ bt); eauto.
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
  Theorem MakeArrayLinearR_time_help :
    forall xs bt n,
      MakeArrayLinearR xs bt n ->
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
  
  Theorem MakeArrayLinearR_time :
    forall xs bt n,
      MakeArrayLinearR xs bt n ->
      n = rt_naive (length xs).
  Proof.
    apply MakeArrayLinearR_time_help.
  Qed.  
End array.
