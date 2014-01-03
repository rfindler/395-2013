Require Import braun log insert util index list_util sequence le_util.
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

(* this is http://oeis.org/A001855 *)
Program Fixpoint mat_time n {measure n} :=
  match n with
    | O => 0
    | S n' =>
      mat_time (div2 n) + mat_time (div2 n') + n
  end.

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

Lemma mat_time_nlogn : 
  forall n,
    mat_time n <= n * cl_log n.
Proof.
  apply (well_founded_ind
           lt_wf
           (fun n => mat_time n <= n * cl_log n)).
  intros n IND.
  destruct n. 
  compute;constructor.

  rewrite mat_time_Sn.

  apply (le_trans (mat_time (div2 (S n)) + mat_time (div2 n) + S n)
                  (div2 (S n) * cl_log (div2 (S n)) + 
                   (div2 n) * cl_log (div2 n) +
                   S n)
                  (S n * cl_log (S n))).
  apply le_plus_left.

  assert (mat_time (div2 (S n)) <= div2 (S n) * cl_log (div2 (S n)));
    [apply IND; auto|].
  assert (mat_time (div2 n) <=  div2 n * cl_log (div2 n));
    [apply IND;auto|].
  omega.

  rewrite cl_log_div2'.
  assert (S n * S (cl_log (div2 (S n))) = (S n) * cl_log (div2 (S n)) + S n) as H;
    [rewrite mult_comm;
     unfold mult at 1;fold mult;
     rewrite plus_comm;
     rewrite mult_comm;
     reflexivity|rewrite H;clear H].

  apply le_plus_left.

  apply (le_trans
           (div2 (S n) * cl_log (div2 (S n)) + div2 n * cl_log (div2 n))
           (div2 (S n) * cl_log (div2 (S n)) + div2 (S n) * cl_log (div2 (S n)))
           (S n * cl_log (div2 (S n)))).

  apply le_plus_right.

  apply le_pieces_le_prod.
  apply div2_monotone.
  
  assert (even n \/ odd n) as H; [apply even_or_odd|destruct H].
  rewrite even_div2;[|assumption].
  constructor.

  rewrite <- odd_div2;[|assumption].
  apply cl_log_monotone.

  rewrite mult_comm.
  replace (S n * cl_log (div2 (S n))) with (cl_log (div2 (S n)) * S n);[|apply mult_comm].
  apply div2_mult.
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
