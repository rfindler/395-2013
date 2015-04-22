Require Import Braun.common.util Braun.common.le_util.
Require Import Braun.common.log Braun.common.big_oh Braun.common.pow.
Require Import Braun.monad.monad Braun.arith.plus Braun.fib.fib.
Require Import Program Div2 Omega Even.

Fixpoint fib_iter_loop_time_lb fuel a b :=
  match fuel with
    | 0 => 1
    | S fuel' => plus_time_lb a b + fib_iter_loop_time_lb fuel' b (a+b) + 1
  end.

Fixpoint fib_iter_loop_time_ub fuel a b :=
  match fuel with
    | 0 => 1
    | S fuel' => plus_time_ub a b + fib_iter_loop_time_ub fuel' b (a+b) + 1
  end.

Definition fib_iter_loop_result (fuel:nat) (target:nat) (a:nat) (b:nat)
           (res:nat) (c:nat) :=
    1 < target ->
    fuel < target ->
    Fib (target - fuel - 1) a ->
    Fib (target - fuel) b ->
    Fib target res /\
    fib_iter_loop_time_lb fuel a b <= c <= fib_iter_loop_time_ub fuel a b.

Load "fib_iter_loop_gen.v".

Next Obligation.
Proof.
  unfold fib_iter_loop_result.
  intros.

  split.
  destruct target.
  intuition.
  destruct target.
  intuition.
  eauto.
  simpl.
  omega.
Qed.

Next Obligation.
Proof.
  unfold fib_iter_loop_result in *.
  rename fuel0 into fuel.
  clear am0 H2 am H3.
  rename H0 into IH.
  rename H1 into TPLUS_RESULT.

  intros LT LE Fa Fb.
  destruct TPLUS_RESULT as [SUMEQAPLUSB PLUSTIME].

  destruct target.
  intuition.
  destruct target.
  intuition.
  edestruct IH as [Fab EQan];try omega.
  replace (S (S target) - fuel - 1) with (S (S target) - S fuel) in *;auto.
  omega.
  replace (S (S target) - S fuel - 1) with (S target - S fuel) in *;[|omega].
  replace (S (S target) - (S fuel)) with (S (S target - S fuel)) in *;[|omega].
  replace (S (S target) - fuel) with (S (S (target - fuel)));[|omega].
  subst sum.
  auto.

  split.
  
  auto.

  simpl fib_iter_loop_time_lb. simpl fib_iter_loop_time_ub. 
  rewrite <- SUMEQAPLUSB.
  omega.
Qed.

Fixpoint fib_iter_time_lb (n:nat) :=
  match n with
    | O => 1
    | S n' =>
      match n' with
        | O => 1
        | S n'' => fib_iter_loop_time_lb n' 0 1 + 1
      end
  end.

Fixpoint fib_iter_time_ub (n:nat) :=
  match n with
    | O => 1
    | S n' =>
      match n' with
        | O => 1
        | S n'' => fib_iter_loop_time_ub n' 0 1 + 1
      end
  end.

Definition fib_iter_result (target:nat) (res:nat) (c:nat) :=
  Fib target res /\
  fib_iter_time_lb target <= c <= fib_iter_time_ub target.

Load "fib_iter_gen.v".

Next Obligation.
Proof.
  unfold fib_iter_result.
  split; simpl; eauto.
Qed.  

Next Obligation.
Proof.
  unfold fib_iter_result.
  split; simpl; eauto.
Qed.

Next Obligation.
Proof.
  clear H1 am.
  rename H0 into FIL.

  unfold fib_iter_result, fib_iter_loop_result, fib_iter_time_lb, fib_iter_time_ub in *.
  edestruct FIL; [ | | | | split; auto]; clear FIL.
  omega. omega.
  replace (S (S target'') - S target'' - 1) with 0; [|omega].
  auto.
  replace (S (S target'') - S target'') with 1;[|omega].
  auto.
  omega.
Qed.

Definition plus_two_fibs_time n := plus_time_lb (fib n) (fib (n+1)).

Fixpoint fib_iter_loop_time_lb2 fuel n :=
  match fuel with
    | 0 => 1
    | S fuel' => plus_two_fibs_time n + 
                 fib_iter_loop_time_lb2 fuel' (n+1) + 1
  end.

Lemma fib_iter_loop_lb12 : 
  forall n steps_taken,
    fib_iter_loop_time_lb n (fib steps_taken) (fib (steps_taken+1)) =
    fib_iter_loop_time_lb2 n steps_taken.
Proof.
  induction n.
  intros; simpl; auto.
  intros.
  simpl fib_iter_loop_time_lb.
  simpl fib_iter_loop_time_lb2.
  unfold plus_two_fibs_time.
  replace (fib steps_taken + fib (steps_taken + 1)) 
  with (fib (steps_taken+2)).
  
  assert (fib_iter_loop_time_lb n (fib (steps_taken + 1)) (fib (steps_taken + 2)) =
          fib_iter_loop_time_lb2 n (steps_taken + 1));auto.
  replace (steps_taken + 2) with ((steps_taken+1)+1);[|omega].
  apply IHn.
  rewrite plus_comm.
  unfold plus at 1.
  rewrite fib_SS.
  replace (S steps_taken) with (steps_taken+1);omega.
Qed.


Lemma fib_iter_loop_time_lb2_grows:
  forall fuel n, 
    fib_iter_loop_time_lb2 fuel n <= fib_iter_loop_time_lb2 fuel (n + 1).
Proof.
  intros fuel.
  induction fuel.
  intros; simpl;omega.
  intros n.
  unfold fib_iter_loop_time_lb2; fold fib_iter_loop_time_lb2.
  repeat (apply plus_le_compat); auto.
  clear IHfuel.
  rewrite plus_cin_time_lb_symmetric at 1.
  apply plus_cin_time_lb_right_arg_grows.
  apply fib_monotone.
  omega.
Qed.

Lemma plus_time_lb_big_oh_plus_cin_time_lb :
  big_oh (fun n : nat => plus_time_lb (fib n) (fib n))
         (fun n : nat => plus_cin_time_lb (fib n) (fib n)).
Proof.
  unfold plus_time_lb.
  exists 1 2.
  intros n LE.
  apply plus_cin_time_lb_growth.
Qed.

Lemma plus_two_fibs_time_lb :
  big_oh (fun n => n) plus_two_fibs_time.
Proof.
  apply (big_oh_trans (fun n => n) div2).
  exists 2 4.
  intros n LT.
  destruct n. intuition.
  destruct n. intuition.
  clear LT.
  apply (well_founded_ind lt_wf (fun n => S (S n) <= 4 * div2 (S (S n)))).
  clear n; intros n IND.
  destruct n.
  simpl; auto.
  destruct n.
  simpl; auto.
  replace (div2 (S (S (S (S n))))) with (S (div2 (S (S n))));[|simpl div2;auto].
  replace (S (div2 (S (S n)))) with (div2 (S (S n)) + 1);[|omega].
  rewrite mult_plus_distr_l.
  rewrite mult_1_r.
  apply (le_trans (S (S (S (S n)))) (S (S n) + 4)).
  omega.
  apply plus_le_compat; auto.

  apply (big_oh_trans div2 (fun n => (plus_cin_time_lb (fib n) (fib (n + 1))))).
  apply (big_oh_trans div2 (fun n => (plus_cin_time_lb (fib n) (fib n)))).
  apply (big_oh_trans div2 (fun n => (cl_log (2 * fib n)))).
  apply (big_oh_trans div2 (fun n => (cl_log (pow 2 (div2 n))))).
  
  exists 0 1.
  intros n _; rewrite mult_1_l.
  rewrite pow2_log.
  omega.

  exists 1 1.
  intros n LT. destruct n. intuition.
  rewrite mult_1_l.
  apply cl_log_monotone.
  apply fib_lower_bound.

  apply (big_oh_trans (fun n => cl_log (2 * fib n))
                      (fun n => cl_log (fib n))).
  apply cl_log_big_oh_double.

  apply (big_oh_trans (fun n => cl_log (fib n))
                      (fun n => plus_time_lb (fib n) (fib n))).
  exists 0 1.
  intros n _.
  rewrite mult_1_l.
  apply log_below_plus_time_nn.

  apply plus_time_lb_big_oh_plus_cin_time_lb.

  exists 0 1.
  intros n _.
  rewrite mult_1_l.
  apply plus_cin_time_lb_right_arg_grows.
  apply fib_monotone; omega.

  exists 0 1.
  intros n _.
  unfold plus_two_fibs_time.
  unfold plus_time_lb.
  omega.
Qed.

Fixpoint fib_iter_loop_time_lb3 fuel n :=
  match fuel with
    | 0 => 1
    | S fuel' => n +
                 fib_iter_loop_time_lb3 fuel' (n+1) + 1
  end.

Lemma fib_iter_loop_lb23 : 
  exists n,
    forall n',
      n <= n' ->
      big_oh (fun fuel => fib_iter_loop_time_lb3 fuel n')
             (fun fuel => fib_iter_loop_time_lb2 fuel n').
Proof.
  apply (recurrence_that_sums 1 1 (fun n => n) plus_two_fibs_time); 
  intros; simpl; auto.

  apply plus_two_fibs_time_lb.
  admit.
Qed.

Lemma fib_iter_loop_time_lb3_sq : 
  exists n,
    forall n',
      n <= n' ->
      big_oh (fun n => n*n) (fun fuel => fib_iter_loop_time_lb3 fuel n').
Admitted.

Lemma fib_iter_time_lb_big_oh_fib_iter_loop_time_lb : 
  big_oh (fun n => fib_iter_loop_time_lb n 0 1) fib_iter_time_lb.
Admitted.
(* this is likely true. *)

Lemma fib_iter_loop_last_arg_invariant :
  forall fb, 
    exists X, 
      forall n,
        fib_iter_loop_time_lb2 n fb <= X * fib_iter_loop_time_lb2 n 0.
Admitted.
(* no clue if this is true. seems not to be obviously false. *)


Theorem fib_iter_n_squared: big_omega fib_iter_time_lb (fun n => n * n).
Proof.
  apply big_oh_rev.
  destruct fib_iter_loop_time_lb3_sq as [lb3_start FACT3].
  destruct fib_iter_loop_lb23 as [lb2_start FACT2].
  apply (big_oh_trans (fun n=> n*n) (fun n => fib_iter_loop_time_lb3 n (max lb2_start lb3_start))).
  apply FACT3.
  apply Max.le_max_r.
  clear FACT3.
  apply (big_oh_trans (fun fuel => fib_iter_loop_time_lb3 fuel (max lb2_start lb3_start))
                      (fun fuel => fib_iter_loop_time_lb2 fuel (max lb2_start lb3_start))).
  apply FACT2.
  apply Max.le_max_l.
  clear FACT2.
  apply (big_oh_trans (fun fuel : nat => fib_iter_loop_time_lb2 fuel (max lb2_start lb3_start))
                      (fun fuel => fib_iter_loop_time_lb fuel 0 1));
    [|apply fib_iter_time_lb_big_oh_fib_iter_loop_time_lb].
  
  remember (max lb2_start lb3_start) as fb; clear Heqfb lb3_start lb2_start.
  destruct (fib_iter_loop_last_arg_invariant fb) as [X FACT].
  exists 0 X.
  intros n _.
  replace (fib_iter_loop_time_lb n 0 1) with (fib_iter_loop_time_lb n (fib 0) (fib 1));[|unfold fib;auto].
  rewrite fib_iter_loop_lb12.
  apply FACT.
Qed.

