Require Import Braun.monad.monad Braun.common.log Braun.common.finite_sums.
Require Import Braun.common.util Braun.common.big_oh Braun.common.le_util.
Require Import Arith Arith.Even Arith.Div2.
Require Import Coq.Program.Wf Arith.Even Arith.Div2 Arith Init.Wf.
Require Import Braun.arith.sub1.

Include WfExtensionality.

Fixpoint sub1_linear_time n :=
  match n with
    | 0 => 3
    | S n' => sub1_time n + sub1_linear_time n' + 7
  end.

Definition sub1_linear_loop_result (n:nat) (res:nat) (c:nat) :=
  c = sub1_linear_time n.
Hint Unfold sub1_linear_loop_result.

Load "sub1_linear_loop_gen.v".

Next Obligation.
Proof.
  rename H into SUB1R.
  destruct SUB1R.
  omega.
Qed.

Next Obligation.
Proof.
  clear H2 am0 am H3 sub1_linear_loop.
  rename H1 into SUB1_RESULT.
  
  unfold sub1_linear_loop_result in *.
  destruct SUB1_RESULT.
  subst an an0 n'.
  unfold sub1_linear_time; fold sub1_linear_time.
  replace (S wildcard' - 1) with wildcard'; omega.
Qed.

Definition sub1_linear_time1 n := (sum 0 n (fun n => sub1_time n + 7)) - 7.

Lemma sub1_linear_time01 :
  forall n,
    sub1_linear_time n = sub1_linear_time1 n.
Proof.
  intros n.
  induction n.
  simpl.
  unfold sub1_linear_time1.
  simpl; auto.

  unfold sub1_linear_time.
  fold sub1_linear_time.
  rewrite IHn.
  unfold sub1_linear_time1.
  rewrite sum_S_j;[|omega].

  assert (sum 0 n (fun n0 : nat => sub1_time n0 + 7) >= 7); try omega.

  induction n.
  simpl; omega.
  rewrite sum_S_j; omega.
Qed.

Definition sub1_linear_time2 n := (sum 0 n (fun n => sub1_time n + 7)).

Lemma sub1_linear_time12 : big_oh sub1_linear_time1 sub1_linear_time2.
Proof.
  unfold sub1_linear_time2.
  unfold sub1_linear_time1.
  exists 0. exists 1.
  intros n _.
  omega.
Qed.

Definition sub1_linear_time3 n := (sum 0 n (fun n => sub1_time n)) + 7*(n+1).

Lemma sub1_linear_time23 : forall n, sub1_linear_time2 n = sub1_linear_time3 n.
Proof.
  intros n.
  unfold sub1_linear_time2; unfold sub1_linear_time3.
  replace (fun n0 : nat => sub1_time n0 + 7)
  with (fplus sub1_time (const 7)); [| unfold fplus; unfold const; reflexivity].
  rewrite <- sum_over_fns.
  unfold const.
  rewrite (sum_constant 0 n 7 n); [|omega].
  intuition.
Qed.

Definition sub1_linear_time4 n := sum 0 n (fun n => sub1_time n).

Lemma sub1_linear_time4_linear : big_oh sub1_linear_time4 (fun n => n).
Proof.
  exists 1.
  exists 32.
  intros n LT.
  destruct n;[intuition|clear LT].

  apply (well_founded_induction
           lt_wf
           (fun n => sub1_linear_time4 (S n) <= 32 * (S n))).
  clear n.
  intros n IND.
  destruct n.
  unfold sub1_linear_time4.
  rewrite sum_S_j; auto.
  rewrite sum_eq.
  compute.
  omega.

  unfold sub1_linear_time4.
  rewrite sum_div2.
  unfold shift_2x.
  unfold shift.

  replace (sum 0 (div2 (S n)) (fun n0 : nat => sub1_time (S (n0 + n0))))
  with (sum 0 (div2 (S n)) (fun n0 => 8));
    [|apply sum_extensionality; intros; rewrite sub1_time_double; auto].

  unfold sub1_linear_time4 in IND.
  
  apply (le_trans
           (sum 0 (div2 (S (S n))) (fun n0 : nat => sub1_time (n0 + n0)) +
            sum 0 (div2 (S n)) (fun _ : nat => 8))
           (sum 0 (div2 (S (S n))) (fun n0 : nat => sub1_time n0 + 12) +
            sum 0 (div2 (S n)) (fun _ : nat => 8))).
  apply plus_le_compat; auto.
  apply sum_preserves_order.
  intros n0 _.
  apply sub1_time_S_double.
  replace (fun n0 : nat => sub1_time n0 + 12)
  with (fplus (fun n0 : nat => sub1_time n0) (fun n0 => 12));
    [|unfold fplus; auto].

  rewrite <- sum_over_fns.

  replace (div2 (S (S n))) with (S (div2 n));[|auto].

  apply (le_trans
           (sum 0 (S (div2 n)) (fun n0 : nat => sub1_time n0) +
            sum 0 (S (div2 n)) (fun _ : nat => 12) +
            sum 0 (div2 (S n)) (fun _ : nat => 8))
           (32 * (S (div2 n)) +
            sum 0 (S (div2 n)) (fun _ : nat => 12) +
            sum 0 (div2 (S n)) (fun _ : nat => 8))).
  apply plus_le_compat;auto.
  apply plus_le_compat;auto.
  rewrite (sum_constant 0 (S (div2 n)) 12 (S (div2 n))); auto.
  rewrite (sum_constant 0 (div2 (S n)) 8 (div2 (S n))); auto.

  replace (32 * S (div2 n) + (S (div2 n) + 1) * 12 + (div2 (S n) + 1) * 8)
          with 
          (44 * div2 n + 8 * (div2 (S n)) + 64);[|omega].
  replace (32 * (S (S n))) with (32 * n + 64);[|omega].
  apply plus_le_compat;auto.

  destruct (even_odd_dec n).

  (* even case *)
  rewrite <- even_div2; auto.
  rewrite (even_double n) at 3; auto.
  unfold double.
  omega.

  rewrite <- odd_div2; auto.
  rewrite (odd_double n) at 3; auto.
  unfold double.
  omega.
Qed.

Theorem sub1_linear_time_linear :
  big_oh sub1_linear_time (fun n => n).
Proof.
  apply (big_oh_trans sub1_linear_time sub1_linear_time1).
  apply big_oh_eq.
  apply sub1_linear_time01.

  apply (big_oh_trans sub1_linear_time1 sub1_linear_time2).
  apply sub1_linear_time12.

  apply (big_oh_trans sub1_linear_time2 sub1_linear_time3).
  apply big_oh_eq.
  apply sub1_linear_time23.

  unfold sub1_linear_time3.
  apply big_oh_plus.

  fold sub1_linear_time4.
  apply sub1_linear_time4_linear.

  exists 1.
  exists 14.
  intros n LT.
  destruct n.
  intuition.
  omega.
Qed.
