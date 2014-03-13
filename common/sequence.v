Require Import Braun.common.braun Braun.common.util Braun.common.index Braun.common.list_util List.
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

Lemma SR_singleton:
  forall (A:Set) (x:A),
    SequenceR (bt_node x bt_mt bt_mt) (x :: nil).
Proof.
  intros A x.
  cut (nil = (@interleave A nil nil)).
  intros EQ. rewrite EQ. clear EQ.
  eapply SR_node; eauto.
  auto.
Qed.

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

Fixpoint mk_list {A:Set} (x:A) (n:nat) :=
  match n with
    | 0 => nil
    | S n' => cons x (mk_list x n')
  end.

Lemma interleave_mk_list_same_size : 
  forall (A:Set) (x:A) n,
    interleave (mk_list x n) (mk_list x n) = mk_list x (n+n).
Proof.
  induction n; auto.
  simpl.
  rewrite <- interleave_case2.
  rewrite <- interleave_case2.
  rewrite IHn.
  replace (n + S n) with (S (n + n)); try omega.
  auto.
Qed.

Lemma interleave_constant_lists :
  forall (A:Set) ss tt (x:A) n,
    interleave ss tt = mk_list x n ->
    exists n1 n2,
      ss = mk_list x n1 /\ tt = mk_list x n2.
Proof.
  induction ss; induction tt.

  (* nil nil *)
  intros.
  exists 0.
  exists 0.
  constructor;auto.

  (* cons nil *)
  intros x n ILML.
  rewrite interleave_nil2 in ILML.
  destruct n; simpl in ILML.
  inversion ILML.
  injection ILML; clear ILML; intros ILML AEQ.
  subst a.
  exists 0.
  exists (S n).
  simpl.
  subst tt.
  split;auto.

(* nil cons *)
  intros x n ILML.
  rewrite interleave_nil1 in ILML.
  destruct n; simpl in ILML.
  inversion ILML.
  injection ILML; clear ILML; intros ILML AEQ.
  subst a ss.
  exists (S n).
  exists 0.
  simpl.
  split; auto.

(* cons cons *)
  intros.
  rewrite <- interleave_case2 in H.
  rewrite <- interleave_case2 in H.
  destruct n; simpl in H.
  inversion H.
  injection H; clear H; intros.
  subst a.
  destruct n; simpl in H.
  inversion H.
  injection H; clear H; intros.
  subst a0.
  remember (IHss tt x n H) as EN1N2EQ.
  clear HeqEN1N2EQ.
  destruct EN1N2EQ as [n1 [n2 [SSEQ TTEQ]]].
  subst ss tt.
  exists (S n1).
  exists (S n2).
  simpl.
  split; reflexivity.
Qed.

Lemma sequence_constant_list_index_is_constant :
  forall (A:Set) n (x:A) (y:A) i t,
    SequenceR t (mk_list x n)
    -> IndexR t i y
    -> x = y.
Proof.
  intros A n x y i t SR IR.
  generalize dependent n.
  induction IR; intros n SR.
  destruct n; simpl in SR.
  inversion SR.
  inversion SR;auto.
  invclr SR.
  rename H3 into ILML.
  destruct n; simpl in ILML.
  inversion ILML.
  injection ILML;clear ILML;intros ILML XISX0.
  remember (interleave_constant_lists A ss ts x n ILML) as THING.
  clear HeqTHING.
  destruct THING as [n1 [n2 [SSEQ TSEQ]]].
  subst ss.
  apply (IHIR n1); auto.

  destruct n; simpl in SR.
  inversion SR.
  invclr SR.
  rename H4 into ILML.
  remember (interleave_constant_lists A ss ts x n ILML) as THING.
  clear HeqTHING.
  destruct THING as [n1 [n2 [SSEQ TSEQ]]].
  subst ts.
  apply (IHIR n2);auto.
Qed.
