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
  admit.
Qed.


Fixpoint fib_iter_loop_time_lb3 fuel n :=
  match fuel with
    | 0 => 1
    | S fuel' => plus_two_fibs_time (n+fuel') +
                 fib_iter_loop_time_lb3 fuel' n + 1
  end.

Lemma fib_iter_loop_time_lb3_identity :
  forall fuel n,
   plus_two_fibs_time n + fib_iter_loop_time_lb3 fuel (n + 1) =
   plus_two_fibs_time (n + fuel) + fib_iter_loop_time_lb3 fuel n.
Proof.
  induction fuel.
  intros n.
  unfold fib_iter_loop_time_lb3.
  repeat (rewrite plus_0_r).
  auto.
  intros n.
  unfold fib_iter_loop_time_lb3.
  fold fib_iter_loop_time_lb3.
  assert (plus_two_fibs_time (n + 1 + fuel) +
          (plus_two_fibs_time n +
          fib_iter_loop_time_lb3 fuel (n + 1)) =
          plus_two_fibs_time (n + S fuel) +
          plus_two_fibs_time (n + fuel) + fib_iter_loop_time_lb3 fuel n);[|omega].
  rewrite (IHfuel n).

  replace (n + S fuel) with (n+1+fuel);[|omega].
  assert (plus_two_fibs_time (n + 1 + fuel) +
          plus_two_fibs_time (n + fuel) + fib_iter_loop_time_lb3 fuel n =
          plus_two_fibs_time (n + 1 + fuel) + plus_two_fibs_time (n + fuel) +
          fib_iter_loop_time_lb3 fuel n);[|omega].
  auto.
Qed.

Lemma fib_iter_loop_lb23:
  forall fuel n,
    fib_iter_loop_time_lb2 fuel n = fib_iter_loop_time_lb3 fuel n.
Proof.
  induction fuel; intros n.
  simpl; auto.
  unfold fib_iter_loop_time_lb3, fib_iter_loop_time_lb2.
  fold fib_iter_loop_time_lb3.
  fold fib_iter_loop_time_lb2.
  
  assert (plus_two_fibs_time n + fib_iter_loop_time_lb2 fuel (n + 1) = 
          plus_two_fibs_time (n+fuel) + fib_iter_loop_time_lb3 fuel n);[|omega].
  rewrite (IHfuel (n+1)).
  apply fib_iter_loop_time_lb3_identity.
Qed.

Fixpoint fib_iter_loop_time_lb4 fuel :=
  match fuel with
    | 0 => 1
    | S fuel' => plus_two_fibs_time fuel' +
                 fib_iter_loop_time_lb4 fuel' + 1
  end.

Lemma fib_iter_loop_lb34 :
  forall n, fib_iter_loop_time_lb3 n 0 = fib_iter_loop_time_lb4 n.
Proof.
  induction n; simpl; auto.
Qed.

Fixpoint fib_iter_loop_time_lb5 fuel :=
  match fuel with
    | 0 => 0
    | S fuel' => plus_two_fibs_time fuel' +
                 fib_iter_loop_time_lb5 fuel'
  end.

Lemma fib_iter_loop_lb45 : 
  forall n, 
    fib_iter_loop_time_lb4 n = n + fib_iter_loop_time_lb5 n + 1.
Proof.
  induction n.
  simpl; auto.
  unfold fib_iter_loop_time_lb4, fib_iter_loop_time_lb5;
  fold fib_iter_loop_time_lb4;
  fold fib_iter_loop_time_lb5.
  rewrite IHn.
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

Fixpoint fib_iter_loop_time_lb6 fuel :=
  match fuel with
    | 0 => 0
    | S fuel' => fuel' +
                 fib_iter_loop_time_lb6 fuel'
  end.

Lemma fib_iter_loop_lb56 : 
  big_oh fib_iter_loop_time_lb6 fib_iter_loop_time_lb5.
Proof.
  destruct plus_two_fibs_time_lb as [plus_two_start [plus_two_factor PLUSTWO]].
  exists (S plus_two_start) plus_two_factor.
  apply (well_founded_ind 
           lt_wf 
           (fun n => 
              (S plus_two_start) <= n -> 
              fib_iter_loop_time_lb6 n <=
              plus_two_factor * fib_iter_loop_time_lb5 n)).
  intros n IND LT.
  destruct n.
  simpl; omega.

  unfold fib_iter_loop_time_lb5, fib_iter_loop_time_lb6;
  fold fib_iter_loop_time_lb5; fold fib_iter_loop_time_lb6.
  rewrite mult_plus_distr_l.
  apply plus_le_compat;auto.

  apply PLUSTWO; omega.

  apply IND; auto.
  admit. (* sigh.*)
Qed.

Fixpoint fib_iter_loop_time_lb2' fuel n :=
  match fuel with
    | 0 => 1
    | S fuel' => n +
                 fib_iter_loop_time_lb2' fuel' n + 1
  end.

Lemma fib_iter_loop_lb22' : big_oh (fun fuel => fib_iter_loop_time_lb2' fuel fuel)
                                   (fun fuel => fib_iter_loop_time_lb2 fuel fuel).
Proof.
  destruct plus_two_fibs_time_lb as [plus_two_start [plus_two_factor PLUSTWO]].
  exists plus_two_start (S plus_two_factor).

  assert (forall fuel n,
            plus_two_start <= n ->
             fib_iter_loop_time_lb2' fuel n <=
             S plus_two_factor * fib_iter_loop_time_lb2 fuel n) as NEW;[|intros; remember (NEW n); auto].
  apply (well_founded_ind
           lt_wf
           (fun fuel => 
              forall n, 
                plus_two_start <= n ->
                fib_iter_loop_time_lb2' fuel n <=
                (S plus_two_factor) * fib_iter_loop_time_lb2 fuel n)).
  intros fuel IND n LE.
  destruct fuel.
  simpl; omega.
  simpl fib_iter_loop_time_lb2'.
  simpl fib_iter_loop_time_lb2.
  repeat (rewrite mult_plus_distr_l).
  repeat (apply plus_le_compat); try omega.

  replace (S plus_two_factor) with (plus_two_factor+1);[|omega].
  rewrite mult_plus_distr_r.
  apply (le_trans n (plus_two_factor * plus_two_fibs_time n)).
  apply PLUSTWO;auto.
  replace (plus_two_factor * plus_two_fibs_time n) with (plus_two_factor * plus_two_fibs_time n + 0) at 1;
    [|omega].
  apply plus_le_compat; omega.

  apply (le_trans (fib_iter_loop_time_lb2' fuel n)
                  (S plus_two_factor * fib_iter_loop_time_lb2 fuel n)).
  apply IND; auto.
  apply mult_le_compat;auto.

  clear.
  apply fib_iter_loop_time_lb2_grows.
Qed.

Lemma le_eq:
  forall n m,
    n <= m ->
    { q | m = q + n }.
Proof.
  induction n; intros m LE.
  exists m. omega.
  destruct m.
  omega.
  destruct (IHn m) as [q EQ].
  omega.
  subst m.
  exists q. auto.
Qed.

(* If we knew something about these numbers, then we'd be able to have
a base case for the property, but we don't, so the "base case" is the
entire proof. *)

Lemma fib_iter_loop_lb56':
  forall
    (plus_two_start : nat)
    (plus_two_factor : nat)
    (PLUSTWO : forall n : nat,
      plus_two_start <= n ->
      n <= plus_two_factor * plus_two_fibs_time n),
    2 <= plus_two_start <= 4 ->
    1 <= plus_two_factor ->
      big_oh fib_iter_loop_time_lb6 fib_iter_loop_time_lb5.
Proof.
  intros. rename H into LEs. rename H0 into LEf.

  exists plus_two_start plus_two_factor.

  intros n LE.
  apply le_eq in LE.
  destruct LE as [q EQ]; subst n.

  induction q.

  simpl plus.
  destruct plus_two_start. omega.
  destruct plus_two_start. omega.
  destruct plus_two_start.
   simpl. omega.
  destruct plus_two_start.
   simpl. omega.
  destruct plus_two_start.
   simpl. omega.
  omega.

  simpl plus.
  unfold fib_iter_loop_time_lb5, fib_iter_loop_time_lb6;
  fold fib_iter_loop_time_lb5; fold fib_iter_loop_time_lb6.
  rewrite mult_plus_distr_l.
  apply plus_le_compat;auto.
  apply PLUSTWO. omega.
Qed.

Lemma fib_iter_loop_lb56'' : 
  big_oh fib_iter_loop_time_lb6 fib_iter_loop_time_lb5.
Proof.
  destruct plus_two_fibs_time_lb as [plus_two_start [plus_two_factor PLUSTWO]].
  exists plus_two_start plus_two_factor.

  intros n LE. (* Point A *)
  apply le_eq in LE.
  destruct LE as [q EQ]; subst n.

  induction q.

  simpl plus.
  rename plus_two_start into n.
  (* Notice that this proof context is the entire property we want to
  prove, Point A, except we no longer have LE. This means that this
  tactic can't work and is wrong. *)
  admit.

  simpl plus.
  unfold fib_iter_loop_time_lb5, fib_iter_loop_time_lb6;
  fold fib_iter_loop_time_lb5; fold fib_iter_loop_time_lb6.
  rewrite mult_plus_distr_l.
  apply plus_le_compat;auto.
  apply PLUSTWO. omega.
Qed.

Theorem fib_iter_n_squared: big_oh fib_iter_time_lb (fun n => n * n).
Admitted.
