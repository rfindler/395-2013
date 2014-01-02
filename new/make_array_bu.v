Require Import braun log insert util index list_util sequence.
Require Import Arith Arith.Even Arith.Div2 List.
Require Import Program.
Require Import Omega.

(* Okasaki's algorithm is wrong or at least ill-defined, because it
(a) relies on in-order matching and assumes that k is not 0, because
when it is, the second case infinite loops. *)

Inductive RowsR : nat -> list A -> list (nat * list A) -> nat -> Prop :=
| RR_mt :
    forall k,
      RowsR k nil nil 0
| RR_cons :
    forall k x xs more more_time,
      RowsR (2 * (S k)) (skipn (S k) (x :: xs)) more more_time ->
      RowsR (S k) (x :: xs) (((S k), firstn (S k) (x::xs)) :: more) (more_time + 1).
Hint Constructors RowsR.

Lemma skipn_length :
  forall k (xs:list A),
    length xs - k = length (skipn k xs).
Proof.
  induction k as [|k]; intros xs; simpl.
  omega.
  destruct xs as [|x xs]. 
  simpl. omega.
  simpl. rewrite IHk. auto.
Qed.
Hint Rewrite skipn_length.

Theorem rows :
  forall k xs,
    { o | exists t, RowsR (S k) xs o t }.
Proof.
  intros k xs. generalize k. clear k.
  remember (length xs) as n.
  generalize n xs Heqn. clear n xs Heqn.

  apply (well_founded_induction_type
           lt_wf
           (fun n => forall xs, 
                       n = length xs -> 
                       forall k,
                         { o | exists t, RowsR (S k) xs o t })).
  
  intros n IH xs Heqn k.
  destruct xs as [|x xs]. eauto.
  remember (n - (S k)) as y.
  cut (y < n). intros LT.
  remember (skipn (S k) (x :: xs)) as next.
  cut (y = length next). intros EQ.
  edestruct (IH y LT next EQ (pred (2 * (S k)))) as [more IHn].
  exists (((S k), firstn (S k) (x::xs)) :: more).
  destruct IHn as [more_time IHn].
  subst.
  exists (more_time + 1).
  eapply RR_cons.
  replace (S (pred (2 * S k))) with (2 * S k) in *.
  auto.
  omega.

  subst. apply skipn_length.

  clear IH. subst y.
  simpl in *.
  destruct n as [|n]; omega.
Qed.
Hint Resolve rows.

Theorem RowsR_time_xs :
  forall k xs o t,
    RowsR k xs o t ->
    t = (length xs).
Proof.
  intros k xs o t RR.
  induction RR.
  auto.
  subst.
  rewrite <- skipn_length.

  (* XXX This is wrong *)
  admit.
Qed.

Theorem RowsR_time_k :
  forall k xs o t,
    RowsR k xs o t ->
    t = k.
Proof.
  intros k xs o t RR.
  induction RR.

  (* XXX This is wrong *)
  admit.

  subst.
  (* XXX This is wrong *)
  admit.
Qed.

Theorem RowsR_bound_k :
  forall k xs o t,
    RowsR k xs o t ->
    t <= k.
Proof.
  intros k xs o t RR.
  induction RR.

  omega.

  invclr IHRR.
  
  (* XXX This is wrong *)
  admit.

  clear x xs more RR.
  generalize more_time H0. clear more_time H0.
  induction k as [|k]; simpl; intros mt LE.
  invclr LE.

  (* XXX This is wrong *)
  admit.
  
  omega.

  replace (k+0) with k in *; try omega.
  replace (S (k + S (S k))) with ((S k) + S (S k)) in *; try omega.
  (* XXX This looks crazy *)
  admit.
Qed.

Theorem RowsR_bound_xs :
  forall k xs o t,
    RowsR k xs o t ->
    t <= (length xs).
Proof.
  intros k xs ot t RR.
  induction RR; simpl.
  omega.
  rewrite <- skipn_length in IHRR.
  simpl in IHRR.
  replace (more_time+1) with (S more_time); try omega.
Qed.

(* XXX border *)

Inductive MakeArrayBUR : list A -> bin_tree -> nat -> Prop :=
| MABUR_zero :
    MakeArrayBUR nil bt_mt 0
| MABUR_succ :
    forall xs odds evens unravel_time s odds_time t evens_time x,
      UnravelR xs odds evens unravel_time ->
      MakeArrayBUR odds s odds_time ->
      MakeArrayBUR evens t evens_time ->
      MakeArrayBUR (x :: xs) (bt_node x s t) 
                   (unravel_time + odds_time + evens_time + 1).
Hint Constructors MakeArrayBUR.

Theorem MakeArrayBUR_SequenceR :
  forall xs bt n,
    MakeArrayBUR xs bt n ->
    SequenceR bt xs.
Proof.
  intros xs bt n MAR.
  induction MAR; eauto.
  rename H into UR.
  apply UnravelR_interleave in UR.
  subst.
  eauto.
Qed.
Hint Resolve MakeArrayBUR_SequenceR.

Lemma make_array_td_base :
  forall xs,
    (forall ys, length ys < length xs ->
                { bt | exists t, MakeArrayBUR ys bt t }) ->
    { bt | exists t, MakeArrayBUR xs bt t }.
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
    { bt | exists t, MakeArrayBUR xs bt t }.
Proof.
  intros xs.
  remember (length xs).
  generalize n xs Heqn. clear n xs Heqn.
  apply (well_founded_induction_type
           lt_wf
           (fun n => forall ys, 
                       n = length ys -> 
                       { bt | exists t, MakeArrayBUR ys bt t })).
  intros n IH xs Heqn. subst n.
  apply make_array_td_base.
  intros ys LT.
  eapply IH. apply LT. auto.
Defined.

Theorem MakeArrayBUR_Braun :
  forall xs bt n,
    MakeArrayBUR xs bt n ->
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
Hint Resolve MakeArrayBUR_Braun.

Theorem MakeArrayBUR_correct :
  forall xs bt n,
    MakeArrayBUR xs bt n ->
    forall i x,
      IndexR bt i x ->
      ListIndexR xs i x.
Proof.
  intros. eauto.
Qed.
Hint Resolve MakeArrayBUR_correct.

Fixpoint mat_time n :=
  match n with
    | O => 
      0
    | S n =>
      mat_time n + 1 + n + fl_log n
  end.

Theorem MakeArrayBUR_time :
  forall xs bt t,
    MakeArrayBUR xs bt t ->
    t = mat_time (length xs).
Proof.
  intros xs bt t MALR.
  induction MALR; eauto.
  rename H into UR.
  subst.
  replace (length (x :: xs)) with (S (length xs)); eauto.
  simpl.
  rewrite (UnravelR_time _ _ _ _ UR).
  rewrite (UnravelR_interleave _ _ _ _ UR).
  clear MALR1 MALR2 s t x UR xs unravel_time.
  rewrite <- interleave_length_split.
  remember (length odds) as x.
  remember (length evens) as y.
  clear Heqx Heqy odds evens.

  (* XXX mat_time is wrong *)

  admit.
Qed.
