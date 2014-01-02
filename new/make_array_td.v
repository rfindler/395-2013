Require Import braun log insert util index list_util sequence.
Require Import Arith Arith.Even Arith.Div2 List.
Require Import Program.
Require Import Omega.

Inductive UnravelR : list A -> list A -> list A -> nat -> Prop :=
| UR_nil :
    UnravelR nil nil nil 0
| UR_cons :
    forall x xs evens odds utime,
      UnravelR xs odds evens utime ->
      UnravelR (x :: xs) (x :: evens) odds (utime + 1).
Hint Constructors UnravelR.

Lemma UnravelR_interleave :
  forall xs evens odds ut,
    UnravelR xs evens odds ut ->
    xs = interleave evens odds.
Proof.
  intros xs evens odds ut UR.
  induction UR.

  auto.
  rewrite <- interleave_case2.
  subst. auto.
Qed.
Hint Rewrite UnravelR_interleave.

Lemma UnravelR_length_both :
  forall xs evens odds ut,
    UnravelR xs evens odds ut ->
    length evens < S (length xs)
 /\ length odds < S (length xs).
Proof.
  intros xs evens odds ut UR.
  induction UR; simpl; omega.
Qed.
Hint Resolve UnravelR_length_both.

Lemma UnravelR_length_evens :
  forall xs evens odds ut,
    UnravelR xs evens odds ut ->
    length evens < S (length xs).
Proof.
  intros xs evens odds ut UR.
  eapply UnravelR_length_both in UR.
  tauto.
Qed.
Hint Resolve UnravelR_length_evens.

Lemma UnravelR_length_odds :
  forall xs evens odds ut,
    UnravelR xs evens odds ut ->
    length odds < S (length xs).
Proof.
  intros xs evens odds ut UR.
  eapply UnravelR_length_both in UR.
  tauto.
Qed.
Hint Resolve UnravelR_length_odds.

Lemma UnravelR_length :
  forall xs evens odds ut,
    UnravelR xs evens odds ut ->
    length odds <= length evens <= length odds + 1.
Proof.
  intros xs evens odds ut UR.
  induction UR; simpl; omega.
Qed.
Hint Resolve UnravelR_length.

Theorem unravel :
  forall xs,
    { eo | exists t, UnravelR xs (fst eo) (snd eo) t }.
Proof.
  induction xs as [|x xs].

  exists (@nil A, @nil A).
  eauto.

  destruct IHxs as [[odds evens] UR].
  exists (x :: evens, odds).
  simpl in *.
  destruct UR as [xst UR].
  eauto.
Defined.

Theorem UnravelR_time :
  forall xs evens odds ut,
    UnravelR xs evens odds ut ->
    ut = length xs.
Proof.
  intros xs evens odds ut UR.
  induction UR; simpl; try omega.
Qed.
Hint Rewrite UnravelR_time.

Inductive MakeArrayTDR : list A -> bin_tree -> nat -> Prop :=
| MATDR_zero :
    MakeArrayTDR nil bt_mt 0
| MATDR_succ :
    forall xs odds evens unravel_time s odds_time t evens_time x,
      UnravelR xs odds evens unravel_time ->
      MakeArrayTDR odds s odds_time ->
      MakeArrayTDR evens t evens_time ->
      MakeArrayTDR (x :: xs) (bt_node x s t) 
                   (unravel_time + odds_time + evens_time + 1).
Hint Constructors MakeArrayTDR.

Theorem MakeArrayTDR_SequenceR :
  forall xs bt n,
    MakeArrayTDR xs bt n ->
    SequenceR bt xs.
Proof.
  intros xs bt n MAR.
  induction MAR; eauto.
  rename H into UR.
  apply UnravelR_interleave in UR.
  subst.
  eauto.
Qed.
Hint Resolve MakeArrayTDR_SequenceR.

Lemma make_array_td_base :
  forall xs,
    (forall ys, length ys < length xs ->
                { bt | exists t, MakeArrayTDR ys bt t }) ->
    { bt | exists t, MakeArrayTDR xs bt t }.
Proof.
  intros [|x xs] IH.
  eauto.
  destruct (unravel xs) as [[evens odds] UR].
  simpl in UR.
  destruct (IH evens) as [s MARs].
   simpl. destruct UR as [t UR]. eauto.
  destruct (IH odds) as [t MARt].
   simpl. destruct UR as [t UR]. eauto.
  exists (bt_node x s t).
   destruct UR as [ut UR].
   destruct MARs as [st MARs].
   destruct MARt as [tt MARt].
   eauto.
Defined.

(* COMMENT: I can't decide if I like it separated like this. On one
hand it is nice, but maybe it is confusing? I think the optimal would
be to figure out how to generate the IH that make_array_td_base needs
directly. *)

Theorem make_array_td :
  forall xs,
    { bt | exists t, MakeArrayTDR xs bt t }.
Proof.
  intros xs.
  remember (length xs).
  generalize n xs Heqn. clear n xs Heqn.
  apply (well_founded_induction_type
           lt_wf
           (fun n => forall ys, 
                       n = length ys -> 
                       { bt | exists t, MakeArrayTDR ys bt t })).
  intros n IH xs Heqn. subst n.
  apply make_array_td_base.
  intros ys LT.
  eapply IH. apply LT. auto.
Defined.

Theorem MakeArrayTDR_Braun :
  forall xs bt n,
    MakeArrayTDR xs bt n ->
    Braun bt (length xs).
Proof.
  intros xs bt n MAR.
  induction MAR; simpl; eauto.

  rename H into UR.
  replace xs with (interleave odds evens).
  replace (S (length (interleave odds evens))) with 
          ((length odds) + (length evens) + 1); eauto.
  rewrite <- interleave_length_split.
  omega.
  symmetry.
  eapply UnravelR_interleave.
  apply UR.
Qed.
Hint Resolve MakeArrayTDR_Braun.

Theorem MakeArrayTDR_correct :
  forall xs bt n,
    MakeArrayTDR xs bt n ->
    forall i x,
      IndexR bt i x ->
      ListIndexR xs i x.
Proof.
  intros. eauto.
Qed.
Hint Resolve MakeArrayTDR_correct.

Program Fixpoint mat_time n {measure n} :=
  match n with
    | O => 0
    | S n' =>
      mat_time (div2 (S n')) + mat_time (div2 n') + (S n')
  end.
Next Obligation.
  destruct n' as [|n'].
  omega.
  apply lt_n_S.
  apply lt_div2'.
Qed.

Lemma mat_time_Sn : 
  forall n',
    mat_time (S n') = 
    mat_time (div2 (S n')) +
    mat_time (div2 n') +
    (S n').
Proof.
  intros.
  WfExtensionality.unfold_sub 
    mat_time
    (mat_time (S n')).
  auto.
Qed.

Theorem MakeArrayTDR_time :
  forall xs bt t,
    MakeArrayTDR xs bt t ->
    t = mat_time (length xs).
Proof.
  intros xs bt t MALR.
  induction MALR; eauto.
  rename H into UR.
  replace (length (x :: xs)) with (S (length xs)); eauto.
  subst.
  rewrite (UnravelR_time _ _ _ _ UR).
  rewrite (UnravelR_interleave _ _ _ _ UR).
  assert (length evens <= length odds <= length evens+1) as BTI;
    [eapply UnravelR_length; apply UR|].
  clear MALR1 MALR2 s t x UR xs unravel_time.
  rewrite <- interleave_length_split.
  remember (length odds) as x.
  remember (length evens) as y.
  clear Heqx Heqy odds evens.
  rewrite mat_time_Sn.

  assert (x = y \/ x = y+1) as TWOCASES;[omega|clear BTI].
  destruct TWOCASES; subst x.

  rewrite div2_with_odd_argument.
  rewrite double_div2.
  omega.

  replace (S (y + 1 + y)) with ((y+1)+(y+1));[|omega].
  replace (y+1+y) with (S (y + y));[|omega].
  rewrite div2_with_odd_argument.
  rewrite double_div2.
  omega.
Qed.
