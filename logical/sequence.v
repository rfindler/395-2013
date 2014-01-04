Require Import Braun.common.braun Braun.common.util Braun.logical.index Braun.logical.list_util List.
Require Import Omega.

Inductive SequenceR {A:Set} : @bin_tree A -> list A -> Prop :=
| SR_mt :
    SequenceR bt_mt nil
| SR_node :
    forall x s t ss ts,
      SequenceR s ss ->
      SequenceR t ts ->
      SequenceR (bt_node x s t) (x::interleave ss ts).
Hint Constructors SequenceR.

Lemma BraunR_SequenceR :
  forall A (b:@bin_tree A) n,
    Braun b n ->
    forall l,
      SequenceR b l ->
      n = (length l).
Proof.
  intros A b n B.
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
Hint Rewrite BraunR_SequenceR.

Theorem SequenceR_IndexR :
  forall A (b:@bin_tree A) i x,
    IndexR b i x ->
    forall xs,
      Braun b (length xs) ->
      SequenceR b xs ->
      ListIndexR xs i x.
Proof.
  intros A b i x IR.
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
  symmetry. eapply BraunR_SequenceR. apply Bs.
  apply SRs.
Qed.
Hint Resolve SequenceR_IndexR.

Lemma SequenceR_In :
  forall A (bt:@bin_tree A) xs,
    SequenceR bt xs ->
    forall y,
      In y xs ->
      exists i,
        IndexR bt i y.
Proof.
  intros A bt xs SR.
  induction SR; simpl; intros y; try tauto.
  intros [EQ|IN].
  subst. eauto.
  apply interleave_In in IN.
  destruct IN as [IN|IN]; [ rename IHSR1 into IH | rename IHSR2 into IH ];
  apply IH in IN; destruct IN as [i IR]; eauto.
Qed.
Hint Resolve SequenceR_In.
