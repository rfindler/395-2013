Require Import braun log insert util index list.
Require Import Arith Arith.Even Arith.Div2 List.
Require Import Program.
Require Import Omega.

Section array.
  Variable A : Set.

  Inductive SequenceR : bin_tree A -> list A -> Prop :=
    | SR_mt :
        SequenceR (bt_mt A) nil
    | SR_node :
        forall x s t ss ts,
          SequenceR s ss ->
          SequenceR t ts ->
          SequenceR (bt_node x s t) (x::interleave A ss ts).
  Hint Constructors SequenceR.

  Lemma InsertR_SequenceR:
    forall t ts y t' n,
      SequenceR t ts ->
      InsertR A y t t' n ->
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
      IndexR A b i x ->
      forall xs,
        Braun b (length xs) ->
        SequenceR b xs ->
        ListIndexR A xs i x.
  Proof.
    intros b i x IR.
    induction IR; intros xs BP SR; invclr SR; eauto;
    rename H3 into SRs; rename H4 into SRt.

    eapply LIR_zero.

    invclr BP.
    rename H3 into BP.
    rename H4 into Bs.
    rename H5 into Bt.
    rename H2 into EQ.
    rewrite <- interleave_length_split in EQ.
    replace s_size with (length ss) in *; try omega.
    replace t_size with (length ts) in *; try omega.
    apply IHIR in SRs; eauto.
    apply ListIndexR_interleave_evens; eauto.
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
    apply ListIndexR_interleave_odds; eauto.
    symmetry. eapply BraunR_SequenceR. apply Bs.
    apply SRs.
  Qed.

  Theorem MakeArrayLinearR_correct :
    forall xs bt n,
      MakeArrayLinearR xs bt n ->
      forall i x,
        IndexR A bt i x ->
        ListIndexR A xs i x.
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
    forall xs bt t,
      MakeArrayLinearR xs bt t ->
      t = rt_naive (length xs).
  Proof.
    intros xs bt t MALR.
    induction MALR.
    auto.
    rename H into IR.
    subst.
    apply MakeArrayLinearR_Braun in MALR.
    eapply (InsertR_time _ _ _ _ _ _ MALR) in IR.
    subst.
    simpl.
    auto.
  Qed.  
End array.
