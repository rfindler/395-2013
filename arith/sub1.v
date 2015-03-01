Require Import Braun.monad.monad Braun.common.log.
Require Import Braun.common.util Braun.common.big_oh Braun.common.le_util.
Require Import Arith Arith.Even Arith.Div2.
Require Import Coq.Program.Wf Arith.Even Arith.Div2 Arith Init.Wf.

Include WfExtensionality.

Program Fixpoint sub1_time (n:nat) {measure n} :=
  match n with
    | 0 => 3
    | S _ => if (even_odd_dec n)
             then (sub1_time (div2 n)) + 12
             else 8
  end.

Definition sub1_result (n:nat) (res:nat) (c:nat) := 
  n-1 = res /\ c = sub1_time n.
Hint Unfold sub1_result.

Load "sub1_gen.v".

Next Obligation.
  clear H2 am.
  rename H into EW.
  rename H1 into SR.

  destruct SR; subst sd2 an.

  split.

  rewrite (even_double (S wildcard')) at 1; auto.
  unfold double.
  remember (div2 (S wildcard')) as x.
  destruct x; try omega.

  destruct wildcard'.
  inversion EW.
  inversion H0.
  simpl in Heqx.
  inversion Heqx.

  unfold_sub sub1_time (sub1_time (S wildcard')).
  fold_sub sub1_time.
  dispatch_if EW' EW''; intuition.
  assert False; intuition.
  apply (not_even_and_odd (S wildcard')); auto.
Qed.

Next Obligation.
  split;auto.
  unfold_sub sub1_time (sub1_time (S wildcard')).
  fold_sub sub1_time.
  dispatch_if EW EW'; intuition.
  assert False; intuition.
  apply (not_even_and_odd (S wildcard')); auto.
Qed.

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
  rename H into SUB1R.
  destruct SUB1R.
  omega.
Qed.

Next Obligation.
  clear H2 am0 am H3 sub1_linear_loop.
  rename H1 into SUB1_RESULT.
  
  unfold sub1_linear_loop_result in *.
  destruct SUB1_RESULT.
  subst an an0 n'.
  unfold sub1_linear_time; fold sub1_linear_time.
  replace (S wildcard' - 1) with wildcard'; omega.
Qed.

Program Fixpoint sub1_time2 (n:nat) {measure n} :=
  match n with
    | 0 => 0
    | S _ => if (even_odd_dec n)
             then (sub1_time2 (div2 n)) + 1
             else 1
  end.

Lemma sub1_time12 : big_oh sub1_time sub1_time2.
  exists 1.
  exists 50.
  intros n LE.
  destruct n; intuition.
  clear LE.
  apply (well_founded_induction
           lt_wf
           (fun n => sub1_time (S n) <= 50 * sub1_time2 (S n))).
  clear n; intros n IND.
  unfold_sub sub1_time (sub1_time (S n)); fold_sub sub1_time.
  unfold_sub sub1_time2 (sub1_time2 (S n)); fold sub1_time2.
  dispatch_if COND1 COND1'; try omega.
  destruct n.
  simpl; omega.
  rewrite mult_plus_distr_l.
  replace (50*1) with (38+12); [|omega].
  rewrite plus_assoc.
  apply le_plus_left.
  apply le_add_right.
  apply IND; auto.
Qed.

Theorem sub1_log : big_oh sub1_time fl_log.
Proof.
  admit.
Qed.
