Require Import Braun.monad.monad Braun.common.log.
Require Import Braun.common.util Braun.common.big_oh Braun.common.le_util.
Require Import Arith Arith.Even Arith.Div2.
Require Import Coq.Program.Wf Arith.Even Arith.Div2 Arith Init.Wf.

Include WfExtensionality.

Program Fixpoint add1_time (n:nat) {measure n} :=
  match n with
    | 0 => 1
    | S _ => if (even_odd_dec n)
             then 1
             else (add1_time (div2 n)) + 1
  end.

Lemma add1_time_0 : add1_time 0 = 1.
Proof.
  unfold_sub add1_time (add1_time 0); auto.
Qed.

Lemma add1_time_S : forall n, 1 <= add1_time (S n).
Proof.
  intros n.
  apply (well_founded_ind
           lt_wf
           (fun n =>
              1 <= add1_time n)).
  intros.
  destruct x.
  rewrite add1_time_0;auto.
  unfold_sub add1_time (add1_time (S x)).
  dispatch_if EW' EW';auto.
  fold_sub add1_time.
  destruct x; auto.
  omega.
Qed.

Definition add1_result (n:nat) (res:nat) (c:nat) := 
  n+1 = res /\ c = add1_time n.
Hint Unfold add1_result.

Load "add1_gen.v".

Next Obligation.
Proof.
  split;auto.
  unfold_sub add1_time (add1_time (S wildcard')).
  fold_sub add1_time.
  dispatch_if EW EW'; intuition.
  assert False; intuition.
  apply (not_even_and_odd (S wildcard')); auto.
Qed.

Next Obligation.
Proof.
  clear H2 am add1.
  rename H into EW.
  rename H1 into SR.

  destruct SR; subst sd2 an.

  split.
  replace (div2 (S wildcard') + 1 + (div2 (S wildcard') + 1))
  with (S (div2 (S wildcard') + div2 (S wildcard')) + 1);[|omega].
  replace (div2 (S wildcard') + div2 (S wildcard'))
  with (double (div2 (S wildcard')));[|unfold double;auto].
  rewrite <- odd_double; auto.

  unfold_sub add1_time (add1_time (S wildcard')).
  fold_sub add1_time.
  dispatch_if EW' EW''; intuition.
  assert False; intuition.
  apply (not_even_and_odd (S wildcard')); auto.
Qed.

Program Fixpoint add1_time2 (n:nat) {measure n} :=
  match n with
    | 0 => 0
    | S _ => if (even_odd_dec n)
             then 1
             else (add1_time2 (div2 n)) + 1
  end.

Lemma  add1_time_Sn : forall n,
                        add1_time (S n) <= (add1_time (div2 (S n))) + 1.
Proof.
  intros.
  unfold_sub add1_time (add1_time (S n)).
  fold_sub add1_time.
  dispatch_if EW EW.
  omega.
  destruct n; auto.
Qed.

Lemma add1_time12 : big_oh add1_time add1_time2.
Proof.
  exists 1.
  exists 14.
  intros n LE.
  destruct n; intuition.
  clear LE.
  apply (well_founded_induction
           lt_wf
           (fun n => add1_time (S n) <= 14 * add1_time2 (S n))).
  clear n; intros n IND.
  unfold_sub add1_time (add1_time (S n)); fold_sub add1_time.
  unfold_sub add1_time2 (add1_time2 (S n)); fold add1_time2.
  dispatch_if COND1 COND1'; try omega.
  destruct n.
  simpl; omega.
  rewrite mult_plus_distr_l.
  apply plus_le_compat;[|omega].
  apply IND; auto.  
Qed.

Theorem add1_log : big_oh add1_time cl_log.
Proof.
  apply (big_oh_trans add1_time add1_time2).
  apply add1_time12.
  
  exists 0.
  exists 1.
  intros n _.
  rewrite mult_1_l.
  apply (well_founded_induction
           lt_wf
           (fun n => add1_time2 n <= cl_log n)).
  clear n; intros n IND.
  destruct n.
  unfold_sub add1_time2 (add1_time2 0).
  omega.

  unfold_sub add1_time2 (add1_time2 (S n)).
  fold add1_time2.

  dispatch_if COND1 COND1'.
  rewrite <- fl_log_cl_log_relationship.
  apply le_n_S.
  omega.

  destruct n.
  simpl.
  rewrite cl_log_div2'.
  apply le_n_S.
  omega.

  apply (le_trans (add1_time2 (S (div2 n)) + 1)
                  (cl_log (S (div2 n)) + 1)).
  apply plus_le_compat;auto.
  apply IND.
  apply lt_n_S.
  auto.

  replace (cl_log (S (S n))) with (S (cl_log (div2 (S (S n)))));[|rewrite cl_log_div2';auto].
  simpl div2.
  omega.
Qed.

Lemma cl_log_bnd_add1_time : forall n,
                               1 <= n ->
                               add1_time n <= 2 * cl_log n.
Proof.
  intros.
  apply le_trans with (2*add1_time2 n).
  destruct n ; intuition.
  apply (well_founded_induction
           lt_wf
           (fun n => add1_time (S n) <= 2 * add1_time2 (S n))).
  intros.
  unfold_sub add1_time (add1_time (S x)); fold_sub add1_time.
  unfold_sub add1_time2 (add1_time2 (S x)); fold add1_time2.
  dispatch_if COND1 COND1'; try omega.
  destruct x.
  simpl; omega.
  rewrite mult_plus_distr_l.
  apply plus_le_compat;[|omega].
  apply H0; auto.
  apply mult_le_compat_l.
  apply (well_founded_induction
           lt_wf
           (fun n => add1_time2 n <= cl_log n)).
  intros.
  destruct x.
  unfold_sub add1_time2 (add1_time2 0).
  omega.

  unfold_sub add1_time2 (add1_time2 (S x)).
  fold add1_time2.

  dispatch_if COND1 COND1'.
  rewrite <- fl_log_cl_log_relationship.
  apply le_n_S.
  omega.

  destruct x.
  simpl.
  rewrite cl_log_div2'.
  apply le_n_S.
  omega.

  apply (le_trans (add1_time2 (S (div2 x)) + 1)
                  (cl_log (S (div2 x)) + 1)).
  apply plus_le_compat;auto.
  apply H0.
  apply lt_n_S.
  auto.

  replace (cl_log (S (S x))) with (S (cl_log (div2 (S (S x)))));[|rewrite cl_log_div2';auto].
  simpl div2.
  omega.
Qed.
