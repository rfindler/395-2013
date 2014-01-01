Require Import braun util index list.
Require Import Arith Arith.Even Arith.Div2 List.
Require Import Program.
Require Import Omega.

Section sequence.
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

End sequence.
