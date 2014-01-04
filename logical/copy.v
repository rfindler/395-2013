Require Import util log braun index sequence list_util.
Require Import Program.Equality.
Require Import Omega.
Require Import Arith Arith.Even Arith.Div2 List.

Inductive Copy2R {A:Set} : A -> nat -> (@bin_tree A) * (@bin_tree A) -> nat -> Prop :=
  C2R_zero :
    forall x,
      Copy2R x 0 (bt_node x bt_mt bt_mt, bt_mt) 1
| C2R_even :
    forall x m time s t,
      Copy2R x m (s,t) time ->
      Copy2R x (2*m+1) (bt_node x s t, bt_node x t t) (time+2)
| C2R_odd :
    forall x m time s t,
      Copy2R x m (s,t) time ->
      Copy2R x (2*m+2) (bt_node x s s, bt_node x s t) (time+2).
Hint Constructors Copy2R.

Inductive CopyR {A:Set} : A -> nat -> (@bin_tree A) -> nat -> Prop :=
  CR :
    forall x n bt1 bt2 time,
      Copy2R x n (bt1,bt2) time ->
      CopyR x n bt2 time.
Hint Constructors CopyR.

Lemma copy2 :
  forall (A:Set) (x:A) (n:nat),
    {pr | exists time, Copy2R x n pr time}.
Proof.
  intros A x.
  apply (well_founded_induction_type
           lt_wf
           (fun n => {pr | exists time, Copy2R x n pr time})).
  intros n IND.
  destruct n.
  eauto.

  destruct (IND (div2 n)) as [PR IND2];[auto|].
  clear IND; destruct PR as [s t].
  destruct (even_odd_dec n).

  exists (bt_node x s t, bt_node x t t).
  destruct IND2.
  exists (x0+2).
  replace (S n) with (2*(div2 n)+1).
  eauto.
  rewrite (even_double n) at 2;[|assumption].
  unfold double.
  omega.

  exists (bt_node x s s, bt_node x s t).
  destruct IND2.
  exists (x0+2).
  replace (S n) with (2*(div2 n)+2).
  eauto.
  rewrite (odd_double n) at 2;[|assumption].
  unfold double.
  omega.
Defined.

Theorem copy :
  forall (A:Set) (x:A) (n:nat), {bt | exists time, CopyR x n bt time}.
Proof.
  intros A x n.
  destruct (copy2 A x n) as [[s t] E].
  exists t.
  destruct E.
  eauto.
Defined.

Lemma Copy2_produces_Braun :
  forall (A:Set) (x:A) n bt1 bt2 time,
    (Copy2R x n (bt1,bt2) time)
    -> Braun bt1 (n+1) /\ Braun bt2 n.
Proof.
  intros A x n s t time CSR.
  dependent induction CSR; try (inversion IHCSR; clear IHCSR).

  constructor.
  replace (0+1) with (0+0+1);[|omega].
  constructor; [omega|constructor|constructor].
  constructor.

  constructor.

  replace (2*m+1+1) with ((m+1)+m+1);[|omega].
  constructor;[omega|assumption|assumption].

  replace (2*m+1) with (m+m+1);[|omega].
  constructor;[omega|assumption|assumption].

  constructor.

  replace (2*m+2+1) with ((m+1)+(m+1)+1);[|omega].
  constructor;[omega|assumption|assumption].

  replace (2*m+2) with ((m+1)+m+1);[|omega].
  constructor;[omega|assumption|assumption].
Qed.

Lemma Copy_produces_Braun :
  forall (A:Set) (x:A) n bt time,
    (CopyR x n bt time) ->
    Braun bt n.
Proof.
  intros A x n bt time CSR.
  inversion CSR.
  apply Copy2_produces_Braun in H.
  inversion H.
  assumption.
Qed.

Lemma Copy2R_correct_elems :
  forall (A:Set) (x:A) n bt1 bt2 ct,
    Copy2R x n (bt1, bt2) ct ->
    (forall i y,
       IndexR bt1 i y ->
       y = x)
    /\ (forall i y,
          IndexR bt2 i y ->
          y = x).
Proof.
  Ltac indexr_mt :=
    match goal with [ H : IndexR bt_mt ?i ?n |- ?G ] => inversion H end.

  intros A x n bt1 bt2 ct CR.
  remember (bt1, bt2) as bp.
  generalize bt1 bt2 Heqbp. clear bt1 bt2 Heqbp.
  induction CR; intros bt1 bt2 Heqbp; inversion_clear Heqbp;
  split; intros y n IR;
  invclr IR; eauto; try indexr_mt;
  destruct (IHCR s t); eauto.
Qed.
Hint Resolve Copy2R_correct_elems.

Lemma CopyR_correct_elems :
  forall (A:Set) (x:A) n bt ct,
    CopyR x n bt ct ->
    forall i y,
      IndexR bt i y ->
      y = x.
Proof.
  intros A x n bt ct CR i y IR.
  invclr CR.
  destruct (Copy2R_correct_elems A x n bt1 bt ct H).
  eauto.
Qed.
Hint Rewrite CopyR_correct_elems.

Theorem CopyR_correct :
  forall (A:Set) (x:A) n bt ct,
    CopyR x n bt ct ->
    forall xs,
      SequenceR bt xs ->
      n = (length xs) /\
      (forall y,
         In y xs -> y = x).
Proof.
  intros A x n bt ct CR xs SR. split.
  eapply BraunR_SequenceR; eauto.
  eapply Copy_produces_Braun; eauto.
  intros y IN.
  edestruct SequenceR_In; eauto.
  eapply CopyR_correct_elems; eauto.
Qed.
Hint Resolve CopyR_correct.

Lemma Copy2R_running_time :
  forall (A:Set) (x:A) n bt1 bt2 time,
    Copy2R x n (bt1,bt2) time ->
    time = ((2 * fl_log n) + 1).
Proof.
  intros A x n bt1 bt2 time Copy2.
  dependent induction Copy2.
  compute; reflexivity.

  replace (2*m+1) with (m+m+1); [|omega].
  rewrite fl_log_odd.
  omega.

  replace (2*m+2) with ((m+1)+(m+1));[|omega].
  rewrite fl_log_even.
  omega.
Qed.
Hint Resolve Copy2R_running_time.

Theorem CopyR_running_time :
  forall (A:Set) (x:A) n bt1 time,
    CopyR x n bt1 time ->
    time = ((2 * fl_log n) + 1).
Proof.
  intros.
  inversion H.
  eauto.
Qed.
