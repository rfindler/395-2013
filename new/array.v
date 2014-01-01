Require Import braun log insert util.
Require Import Arith Arith.Even Arith.Div2 List.
Require Import Program.
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

  Program Fixpoint interleave (evens : list A) (odds : list A)
          {measure (length (evens ++ odds))} :=
    match evens with
      | nil => odds
      | (x :: xs) => x :: (interleave odds xs)
    end.
  Next Obligation.
    simpl.
    rewrite app_length.
    rewrite app_length.
    omega.
  Qed.

  Lemma interleave_case2 :
    forall x ss ts,
      x :: interleave ss ts = interleave (x :: ts) ss.
  Proof.
    intros.
    unfold interleave.
    WfExtensionality.unfold_sub interleave_func (interleave_func (existT (fun _ : list A => list A) (x :: ts) ss)).
    fold interleave_func.
    destruct ts; simpl; reflexivity.
  Qed.

  Inductive SequenceR : bin_tree A -> list A -> Prop :=
    | SR_mt :
        SequenceR (bt_mt A) nil
    | SR_node :
        forall x s t ss ts,
          SequenceR s ss ->
          SequenceR t ts ->
          SequenceR (bt_node x s t) (x::interleave ss ts).
  Hint Constructors SequenceR.

  Lemma InsertR_SequenceR:
    forall t ts y t' n,
      SequenceR t ts ->
      InsertR A y t t' n ->
      SequenceR t' (y :: ts).
  Proof.
    induction t as [|x s IHs t IHt]; intros ts y t' n SR IR.

    invclr SR. invclr IR.
    cut (nil = interleave nil nil). intros EQ; rewrite EQ.
    eapply SR_node; eauto.
    auto.

    invclr SR. rename H3 into SRs. rename H4 into SRt.
    invclr IR. rename H5 into IR. rename ts0 into ts.
    rename t'0 into t'.
    rewrite interleave_case2.
    eapply SR_node; eauto.
  Qed.

  Inductive MakeArrayLinearR : list A -> bin_tree A -> nat -> Prop :=
  | MALR_zero : 
      MakeArrayLinearR nil (bt_mt A) 0
  | MALR_succ :
      forall x xs bt bt' time insert_time,
        InsertR A x bt bt' insert_time ->
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
    remember (insert A x bt).
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
    apply (InsertR_Braun A x (length xs) insert_time bt0).
    apply (IHxs bt0 time H0).
    assumption.
  Qed.

  Inductive ListIndexR : list A -> nat -> A -> Prop :=
    | LIR_zero :
        forall x xs,
          ListIndexR (x :: xs) 0 x
    | LIR_succ :
        forall x xs n y,
          ListIndexR xs n y ->
          ListIndexR (x :: xs) (S n) y.
  Hint Constructors ListIndexR.

  Theorem ListIndexR_correct :
    forall i xs x,
      nth_error xs i = value x <->
      ListIndexR xs i x.
  Proof.
    induction i as [|n]; intros xs y;
    destruct xs as [|x xs]; simpl;
    split; intros H;
    inversion H; clear H; subst;
    eauto.

    apply IHn in H1. eauto.
    apply IHn in H4. auto.
  Qed.

  Lemma IndexR_interleave_evens :
    forall ss i y x ts,
      length ts <= length ss <= (length ts) + 1 ->
      ListIndexR ss i y ->
      ListIndexR (x :: interleave ss ts) (2 * i + 1) y.
  Proof.
    induction ss as [|sy ss]; intros i y x ts BP LIR.
    invclr LIR.

    invclr LIR. simpl.
    eapply LIR_succ. eapply LIR_zero.
    
    rename H3 into LIR.
    destruct ts as [|ty ts].

    simpl in BP. replace ss with (@nil A) in *.
    invclr LIR.
    destruct ss; simpl in *; try omega.
    auto.

    eapply (IHss _ _ ty ts) in LIR.
    replace (2 * S n + 1) with (S (S (2 * n + 1))); try omega.
    eapply LIR_succ.
    rewrite <- interleave_case2.
    rewrite <- interleave_case2.
    eapply LIR_succ.
    apply LIR.
    simpl in BP. omega.
  Qed.

  Lemma IndexR_interleave_odds :
    forall ts i y x ss,
      length ts <= length ss <= (length ts) + 1 ->
      ListIndexR ts i y ->
      ListIndexR (x :: interleave ss ts) (2 * i + 2) y.
  Proof.
    induction ts as [|ty ts]; intros i y x ss BP LIR.
    invclr LIR.

    destruct i as [|i].
    invclr LIR.

    replace (2 * 0 + 2) with (S (S 0)); try omega.
    eapply LIR_succ.
    destruct ss as [|sy ss].
    simpl in BP. omega.
    rewrite <- interleave_case2.
    eapply LIR_succ.
    eapply LIR_zero.

    invclr LIR. rename H3 into LIR.
    replace (2 * (S i) + 2) with (S (S (2 * i + 2))); try omega.
    eapply LIR_succ.
    destruct ss as [|sy ss].
    simpl in BP. omega.
    rewrite <- interleave_case2.
    eapply LIR_succ.
    rewrite <- interleave_case2.
    eapply IHts; eauto.
    simpl in BP.
    omega.
  Qed.

  Lemma interleave_length_swap :
    forall ss ts,
      (length (interleave ss ts)) = (length (interleave ts ss)).
  Proof.
    induction ss as [|sy ss]; intros ts.
    
    induction ts as [|ty ts]; simpl; auto.

    rewrite <- interleave_case2.
    simpl.
    destruct ts as [|ty ts].
    auto.
    rewrite <- interleave_case2.
    rewrite <- interleave_case2.
    rewrite <- interleave_case2.
    simpl. rewrite IHss.
    auto.
  Qed.

  Lemma interleave_length_split :
    forall ss ts,
      (length ss) + (length ts) = (length (interleave ss ts)).
  Proof.
    induction ss as [|sy ss]; intros ts.
    
    simpl. auto.

    rewrite <- interleave_case2.
    simpl. rewrite IHss.
    rewrite interleave_length_swap.
    auto.
  Qed.

  Lemma BraunR_SequenceR :
    forall b n,
      Braun b n ->
      forall l,
        SequenceR b l ->
        n = (length l).
  Proof.
    intros b n B.
    induction B; intros l SR; invclr SR.
    auto.

    rename H into BP.
    rename H4 into SRs.
    rename H5 into SRt.
    apply IHB1 in SRs.
    apply IHB2 in SRt.
    subst.
    rewrite interleave_length_split.
    simpl.
    omega.
  Qed.

  Theorem SequenceR_IndexR :
    forall b i x,
      IndexR b i x ->
      forall xs,
        Braun b (length xs) ->
        SequenceR b xs ->
        ListIndexR xs i x.
  Proof.
    intros b i x IR.
    induction IR; intros xs BP SR; invclr SR; eauto;
    rename H3 into SRs; rename H4 into SRt.

    invclr BP.
    rename H3 into BP.
    rename H4 into Bs.
    rename H5 into Bt.
    rename H2 into EQ.
    rewrite <- interleave_length_split in EQ.
    replace s_size with (length ss) in *; try omega.
    replace t_size with (length ts) in *; try omega.
    apply IHIR in SRs; eauto.
    apply IndexR_interleave_evens; eauto.
    symmetry. eapply BraunR_SequenceR. apply Bs.
    apply SRs.

    invclr BP.
    rename H3 into BP.
    rename H4 into Bs.
    rename H5 into Bt.
    rename H2 into EQ.
    rewrite <- interleave_length_split in EQ.
    replace s_size with (length ss) in *; try omega.
    replace t_size with (length ts) in *; try omega.
    apply IHIR in SRt; eauto.
    apply IndexR_interleave_odds; eauto.
    symmetry. eapply BraunR_SequenceR. apply Bs.
    apply SRs.
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

  Theorem MakeArrayLinearR_time :
    forall xs bt n,
      MakeArrayLinearR xs bt n ->
      n = rt_naive (length xs).
  Proof.
    intros xs bt n MALR.
    induction MALR.
    auto.
    rename H into IR.
    subst.
    simpl.
    apply MakeArrayLinearR_Braun in MALR.
    eapply (InsertR_time _ _ _ _ _ _ MALR) in IR.
    subst.
    auto.
  Qed.  
End array.
