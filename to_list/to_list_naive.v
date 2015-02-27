Require Import Braun.monad.monad.

Require Import Braun.common.sequence.
Require Import Braun.common.list_util.

Require Import Braun.common.braun.
Require Import Braun.common.util.
Require Import Braun.common.le_util.
Require Import Braun.common.big_oh.
Require Import Braun.common.pow.

Require Import List.

Definition cinterleave_time_best (n:nat) (m:nat) :=
  3 + 9 * (min n m).
Definition cinterleave_time_worst (n:nat) (m:nat) :=
  3 + 9 * (n + m).

Definition cinterleave_result (A:Set) (e:list A) (o:list A) (xs:list A) (c:nat) :=
  xs = interleave e o /\
  cinterleave_time_best (length e) (length o)
  <= c <= cinterleave_time_worst (length e) (length o).

Load "cinterleave_gen.v".

Next Obligation.
Proof.
  clear cinterleave.
  unfold cinterleave_result, cinterleave_time_best, cinterleave_time_worst.
  rewrite interleave_nil2. split. auto.
  simpl. omega.
Qed.

Next Obligation.
Proof.
  clear cinterleave.
  unfold cinterleave_result, cinterleave_time_best, cinterleave_time_worst.
  simpl. rewrite app_length. rewrite app_length. omega.
Qed.

Next Obligation.
Proof.
  clear cinterleave.
  unfold cinterleave_result, cinterleave_time_best, cinterleave_time_worst in *.
  clear am H1.
  rename H0 into REC_P.
  destruct REC_P as [EQ REC_P].
  subst xsp.
  rewrite interleave_case2. split. auto.
  simpl length.
  replace (S (length xs) + length o) with (S (length o + length xs)); try omega.
  remember (length o + length xs) as L.
  rewrite Mult.mult_succ_r.
  rewrite Min.min_comm.
  destruct (Min.min_spec (length o) (length xs)) as [[LT EQ] | [LT EQ]].
  rewrite EQ in REC_P.
  rewrite Min.min_l. omega. omega.
  rewrite EQ in REC_P.
  apply Min.min_case_strong; intros LE.
  omega.
  omega.
Qed.

Fixpoint tln_time n :=
  match n with
    | O =>
      3
    | S n' =>
      15 + (3 + 9 * n') + 2 * tln_time n'
  end.

Lemma tln_time_bigger:
  forall tn,
    3 <= tln_time tn.
Proof.
  induction tn as [|tn]; simpl; omega.
Qed.

Lemma tln_time_split:
  forall sn tn,
    tln_time sn + tln_time tn <= 2 * tln_time (sn + tn).
Proof.
  induction sn as [|sn]; simpl; intros tn.
  remember (tln_time_bigger tn) as P. omega.

  assert (tln_time sn + tln_time tn <= 2 * tln_time (sn + tn)) as LE.
  auto. omega.
Qed.

Definition to_list_naive_result (A:Set) b (xs:list A) (c:nat) :=
  SequenceR b xs
  /\ c <= tln_time (length xs).

Load "to_list_naive_gen.v".

Next Obligation.
Proof.
  unfold to_list_naive_result. simpl.
  split. eauto. auto.
Qed.

Next Obligation.
Proof.
  clear am H5 am0 H4.
  clear am1 H3.
  unfold to_list_naive_result in *.
  destruct H1 as [SEQt ANt].
  destruct H2 as [SEQs ANs].
  unfold cinterleave_result, cinterleave_time_best, cinterleave_time_worst in *.
  destruct H0 as [EQxs ANi].
  subst xs.
  simpl length.
  rewrite <- interleave_length_split.
  remember (length sl) as sn.
  remember (length tl) as tn.
  split; eauto.
  clear SEQs SEQt A x s t sl tl Heqtn Heqsn.
  remember (an + 15) as p.
  replace (an1 + (an0 + p)) with
          (p + (an1 + an0)); try omega.
  replace (tln_time (S (sn + tn))) with
    (15 + (3 + 9 * (sn + tn)) + 2 * tln_time (sn + tn)); try auto.
  subst p.
  replace (an + 15 + (an1 + an0)) with (15 + an + (an0 + an1)); try omega.
  apply le_add.
  apply le_add. auto. omega.
  
  apply Le.le_trans with (tln_time sn + tln_time tn); try omega.
  apply tln_time_split.
Qed.

Theorem tln_time_big_oh:
  big_oh tln_time (fun n => pow 3 n).
Proof.
  unfold big_oh.
  exists 0. exists 18.
  intros n _. generalize n. clear n.
  induction n as [|n].
  simpl. omega. 
  replace (tln_time (S n)) with (15 + (3 + 9 * n) + 2 * tln_time n); try auto.
  simpl pow.
  replace (18 * (pow 3 n + (pow 3 n + (pow 3 n + 0))))
    with (18 * pow 3 n + 2 * 18 * pow 3 n); try omega.
  apply le_add. clear IHn.
  replace (15 + (3 + 9 * n)) with (9 * n + 18); try omega.

  induction n as [|n]. simpl. auto.
  simpl pow. rewrite Mult.mult_succ_r.
  replace (9 * n + 9 + 18) with (9 + (9 * n + 18)); try omega.
  rewrite <- Mult.mult_assoc.
  apply le_mult. auto.
  auto.
Qed.
