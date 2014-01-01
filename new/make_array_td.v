Require Import braun log insert util index list sequence.
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
Qed.

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

Theorem make_array_td :
  forall xs,
    { bt | exists t, MakeArrayTDR xs bt t }.
Proof.

  (* XXX Find the right induction principle and call
  make_array_td_base *)
  admit.

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

Theorem MakeArrayTDR_time :
  forall xs bt t,
    MakeArrayTDR xs bt t ->
    t = nlogn (length xs).
Proof.
  intros xs bt t MALR.
  induction MALR; eauto.
  rename H into UR.
  subst.
  replace (length (x :: xs)) with (S (length xs)); eauto.
  simpl.

  (* XXX I'm not sure what's going on here. *)

  admit.
Qed.
