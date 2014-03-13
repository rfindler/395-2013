Require Import Braun.tmonad.monad.
Require Import Braun.insert.insert_log.

Require Import Braun.common.sequence.

Require Import Braun.common.braun.
Require Import Braun.common.array.
Require Import Braun.common.util.
Require Import Braun.common.big_oh.
Require Import Braun.common.log Braun.common.le_util.
Require Import Arith Arith.Even Arith.Div2 Omega.

Fixpoint man_time' n : nat :=
  match n with
    | 0 => 3
    | S n' => man_time' n' + 9 * (fl_log n') + 14
  end.

Definition make_array_naive_result (A:Set) (xs:list A) (b : @bin_tree A) c :=
  let n := length xs in
  Braun b n
  /\ c = man_time' n
  /\ SequenceR b xs.
Hint Unfold make_array_naive_result.

Load "make_array_nlogn1_gen.v".

Next Obligation.
Proof.
  clear H2 H3.
  rename H1 into MANRxs'.
  rename H0 into IRbt.

  destruct MANRxs' as [BTbt [EQxm SRbt]].

  unfold insert_result in *.
  remember (IRbt (length xs') BTbt) as ONE; clear HeqONE IRbt.
  destruct ONE as [BRir [SRimpl EQxm0]].

  repeat split; auto.
  subst.
  simpl.
  unfold insert_time.
  omega.
Qed.

Lemma man_time'_nlogn_helper: 
  forall n, 
    n * (9 * (fl_log n) + 14) + 3 <=
    23 * n * fl_log n + 3.
Proof.
  intros n.
  apply le_plus_left.
  replace (n * (9 * fl_log n + 14)) with (9 * n * fl_log n + 14 * n).
  replace (23*n*fl_log n) with (9 * n * fl_log n + 14 * n * fl_log n).
  apply le_plus_right.
  replace (14 * n * fl_log n) with (14 * (n * fl_log n)).
  apply le_mult_right.
  
  destruct n; auto.
  
  assert (S n = S n * 1) as H;[omega|rewrite H at 1; clear H].
  apply le_mult_right.
  apply one_le_fl_log_S.
  
  apply mult_assoc.
  
  replace 23 with (9+14);[|omega].
  rewrite <- mult_plus_distr_r.
  replace ((9+14)*n) with (9*n+14*n);
    [reflexivity|rewrite mult_plus_distr_r;reflexivity].
  
  rewrite mult_plus_distr_l.
  replace (n * (9 * fl_log n)) with ((n * 9) * fl_log n);
    [|rewrite mult_assoc;reflexivity].
  replace (9*n) with (n*9); [|apply mult_comm].
  replace (14*n) with (n*14); [|apply mult_comm].
  reflexivity.
Qed.

Lemma man_time'_nlogn_help:
  forall n,
    man_time' n <=  23 * n * (fl_log n) + 3.
Proof.
  intros n.
  apply (le_trans (man_time' n)
                  (n * (9 * (fl_log n) + 14) + 3)
                  (23 * n * fl_log n + 3)); try (apply man_time'_nlogn_helper).
  
  induction n as [|n].
  simpl; omega.
  
  unfold man_time'; fold man_time'.
  
  apply (le_trans (man_time' n + 9 * fl_log n + 14)
                  ((n * (9 * fl_log n + 14) + 3) + 9 * fl_log n + 14)
                  (S n * (9 * fl_log (S n) + 14) + 3)).
  
  repeat (apply le_plus_left).
  assumption.
  
  replace (S n * (9 * fl_log (S n) + 14))
  with (n * (9 * fl_log (S n) + 14) + (9 * fl_log (S n) + 14)).
  
  assert (n * (9 * fl_log n + 14) <= n * (9 * fl_log (S n) + 14)).
  apply le_mult_right.
  apply le_plus_left.
  apply le_mult_right.
  apply fl_log_monotone_Sn.
  
  assert (9 * fl_log n + 14 <= 9 * fl_log (S n) + 14).
  apply le_plus_left.
  apply le_mult_right.
  apply fl_log_monotone_Sn.
  omega.
  
  unfold mult; fold mult; omega.
Qed.

Lemma nlogn_plus_3_is_n_log_n:
  big_oh (fun n => n * fl_log n + 3) 
         (fun n => n * fl_log n).
Proof.
  exists 1.
  exists 8.
  intros n LE.
  destruct n; intuition.
  clear LE.
  rewrite <- fl_log_div2.
  rewrite mult_plus_distr_l.
  rewrite mult_plus_distr_l.
  apply (le_trans (S n * fl_log (div2 n) + S n * 1 + 3)
                  (S n * fl_log (div2 n) + 8 * (S n * 1))
                  (8 * (S n * fl_log (div2 n)) + 8 * (S n * 1))).
  rewrite <- plus_assoc.
  apply le_plus_right.
  omega.
  apply le_plus_left.
  remember (S n * fl_log (div2 n)) as x.
  omega.
Qed.

Theorem man_time'_nlogn: big_oh man_time' (fun n => n * fl_log n).
Proof.
  apply (big_oh_trans man_time'
                      (fun n => n * fl_log n + 3)
                      (fun n => n * fl_log n)).
  exists 0.
  exists 23.
  intros n JUNK.
  apply (le_trans (man_time' n)
                  (23 * n * fl_log n + 3)
                  (23 * (n * fl_log n + 3))).
  apply man_time'_nlogn_help.
  rewrite mult_plus_distr_l.
  rewrite mult_assoc.
  apply le_plus_right.
  omega.
  apply nlogn_plus_3_is_n_log_n.
Qed.
