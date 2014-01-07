Require Import Braun.common.braun Braun.common.log Braun.common.util Braun.common.le_util.
Require Import Braun.logical.insert Braun.logical.index Braun.logical.list_util Braun.logical.sequence.
Require Import Braun.common.array. (* used only for proof that the running time is the same as naive *)
Require Import Arith Arith.Even Arith.Div2 List.
Require Import Program.
Require Import Omega.

Inductive UnravelR {A:Set} : list A -> list A -> list A -> nat -> Prop :=
| UR_nil :
    UnravelR nil nil nil 0
| UR_cons :
    forall x xs evens odds utime,
      UnravelR xs odds evens utime ->
      UnravelR (x :: xs) (x :: evens) odds (utime + 1).
Hint Constructors UnravelR.

Lemma UnravelR_interleave :
  forall A xs evens odds ut,
    @UnravelR A xs evens odds ut ->
    xs = interleave evens odds.
Proof.
  intros A xs evens odds ut UR.
  induction UR.

  auto.
  rewrite <- interleave_case2.
  subst. auto.
Qed.
Hint Rewrite UnravelR_interleave.

Lemma UnravelR_length_both :
  forall A xs evens odds ut,
    @UnravelR A xs evens odds ut ->
    length evens < S (length xs)
 /\ length odds < S (length xs).
Proof.
  intros A xs evens odds ut UR.
  induction UR; simpl; omega.
Qed.
Hint Resolve UnravelR_length_both.

Lemma UnravelR_length_evens :
  forall A xs evens odds ut,
    @UnravelR A xs evens odds ut ->
    length evens < S (length xs).
Proof.
  intros A xs evens odds ut UR.
  eapply UnravelR_length_both in UR.
  tauto.
Qed.
Hint Resolve UnravelR_length_evens.

Lemma UnravelR_length_odds :
  forall A xs evens odds ut,
    @UnravelR A xs evens odds ut ->
    length odds < S (length xs).
Proof.
  intros A xs evens odds ut UR.
  eapply UnravelR_length_both in UR.
  tauto.
Qed.
Hint Resolve UnravelR_length_odds.

Lemma UnravelR_length :
  forall A xs evens odds ut,
    @UnravelR A xs evens odds ut ->
    length odds <= length evens <= length odds + 1.
Proof.
  intros A xs evens odds ut UR.
  induction UR; simpl; omega.
Qed.
Hint Resolve UnravelR_length.

Theorem unravel :
  forall A xs,
    { eo | exists t, @UnravelR A xs (fst eo) (snd eo) t }.
Proof.
  induction xs as [|x xs].

  exists (@nil A, @nil A). simpl.
  eauto.

  destruct IHxs as [[odds evens] UR].
  exists (x :: evens, odds).
  simpl in *.
  destruct UR as [xst UR].
  eauto.
Defined.

Theorem UnravelR_time :
  forall A xs evens odds ut,
    @UnravelR A xs evens odds ut ->
    ut = length xs.
Proof.
  intros A xs evens odds ut UR.
  induction UR; simpl; try omega.
Qed.
Hint Rewrite UnravelR_time.

Inductive MakeArrayTDR {A:Set} : list A -> @bin_tree A -> nat -> Prop :=
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
  forall A xs (bt:@bin_tree A) n,
    MakeArrayTDR xs bt n ->
    SequenceR bt xs.
Proof.
  intros A xs bt n MAR.
  induction MAR; eauto.
  rename H into UR.
  apply UnravelR_interleave in UR.
  subst.
  eauto.
Qed.
Hint Resolve MakeArrayTDR_SequenceR.

Lemma make_array_td_base :
  forall (A:Set) (xs:list A),
    (forall (ys:list A), length ys < length xs ->
                { bt | exists t, MakeArrayTDR ys bt t }) ->
    { bt | exists t, MakeArrayTDR xs bt t }.
Proof.
  intros A [|x xs] IH.
  eauto.
  destruct (unravel A xs) as [[evens odds] UR].
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
  forall A xs,
    { bt : @bin_tree A | exists t, MakeArrayTDR xs bt t }.
Proof.
  intros A xs.
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
  forall A xs (bt:@bin_tree A) n,
    MakeArrayTDR xs bt n ->
    Braun bt (length xs).
Proof.
  intros A xs bt n MAR.
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
  forall A xs (bt:@bin_tree A) n,
    MakeArrayTDR xs bt n ->
    forall i x,
      IndexR bt i x ->
      ListIndexR xs i x.
Proof.
  intros. eauto.
Qed.
Hint Resolve MakeArrayTDR_correct.

Lemma MakeArrayTDR_exact_time :
  forall A xs (bt:@bin_tree A) t,
    MakeArrayTDR xs bt t ->
    t = mat_time (length xs).
Proof.
  intros A xs bt t MALR.
  induction MALR; eauto.
  rename H into UR.
  replace (length (x :: xs)) with (S (length xs)); eauto.
  subst.
  rewrite (UnravelR_time _ _ _ _ _ UR).
  rewrite (UnravelR_interleave _ _ _ _ _ UR).
  assert (length evens <= length odds <= length evens+1) as BTI;
    [eapply UnravelR_length; apply UR|].
  clear MALR1 MALR2 s t x UR xs unravel_time.
  rewrite <- interleave_length_split.
  remember (length odds) as x.
  remember (length evens) as y.
  clear Heqx Heqy odds evens.
  auto.
Qed.

Theorem MakeArrayTDR_time :
  forall A xs (bt:@bin_tree A) t,
    MakeArrayTDR xs bt t ->
    t <= (length xs) * cl_log (length xs).
Proof.
  intros.
  apply (le_trans t 
                  (mat_time (length xs))
                  (length xs * cl_log (length xs))).
  apply MakeArrayTDR_exact_time in H.
  omega.

  apply mat_time_nlogn.
Qed.
