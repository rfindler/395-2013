Require Import Braun.common.util Braun.common.le_util Braun.common.finite_sums.
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

Lemma plus_two_fibs_time_monotone : monotone plus_two_fibs_time.
Proof.
  unfold monotone.
  intros.
  unfold plus_two_fibs_time.
  unfold plus_time_lb.
  apply plus_le_compat;auto.
  apply (le_trans (plus_cin_time_lb (fib n) (fib (n+1)))
                  (plus_cin_time_lb (fib n) (fib (m+1)))).
  apply plus_cin_time_lb_right_arg_grows.
  apply fib_monotone.
  apply plus_le_compat;auto.
  rewrite plus_cin_time_lb_symmetric.
  replace (plus_cin_time_lb (fib m) (fib (m + 1))) with
          (plus_cin_time_lb (fib (m+1)) (fib m));[|apply plus_cin_time_lb_symmetric].
  apply plus_cin_time_lb_right_arg_grows.
  apply fib_monotone.
  auto.
Qed.

Lemma plus_two_fibs_time_upper_bound :
  forall n, plus_two_fibs_time n <= n + 4.
Proof.
  intros.
  unfold plus_two_fibs_time.
  unfold plus_time_lb.
  apply (le_trans
           (plus_cin_time_lb (fib n) (fib (n + 1))+1)
           (plus_cin_time_lb (fib (n+1)) (fib (n + 1))+1)).
  rewrite plus_cin_time_lb_symmetric.
  apply plus_le_compat; auto.
  apply plus_cin_time_lb_right_arg_grows.
  apply fib_monotone.
  omega.
  replace (plus_cin_time_lb (fib (n + 1)) (fib (n + 1))+1) with
          (plus_time_lb (fib (n + 1)) (fib (n + 1))).
  rewrite plus_time_lb_below_log_nn.
  replace (n+4) with ((n+2)+2);[|omega].
  apply plus_le_compat; auto.
  eapply le_trans.
  apply fib_log_upper_bound. omega.
  unfold plus_time_lb. auto.
Qed.  
  
Fixpoint fib_iter_loop_time_lb2 fuel n :=
  match fuel with
    | 0 => 1
    | S fuel' => plus_two_fibs_time n + 
                 fib_iter_loop_time_lb2 fuel' (n+1) + 1
  end.

Fixpoint fib_iter_loop_time_lb22 fuel n :=
  match fuel with
    | 0 => 1
    | S fuel' => plus_two_fibs_time (n+fuel') +
                 fib_iter_loop_time_lb22 fuel' n + 1
  end.

Fixpoint fib_iter_loop_time_lb2_rev fuel n :=
  match fuel with
    | 0 => 1
    | S fuel' => plus_two_fibs_time n +
                 fib_iter_loop_time_lb2_rev fuel' (pred n) + 1
  end.


Theorem fib_iter_loop_lb2_is_a_sum :
  forall fuel n,
    0 < fuel ->
    fib_iter_loop_time_lb2 fuel n = 1 + sum 0 (fuel - 1) (fun m => 1 + plus_two_fibs_time (n+m)).
Proof.
  intros.
  apply function_is_a_sum with (f := fib_iter_loop_time_lb2)
                                 (fuel := fuel)
                                 (n := n)
                                 (g := (fun m : nat => 1 + plus_two_fibs_time m)); auto.
  intros. simpl. replace (n0+1) with (S n0); omega.
Qed.

Lemma fib_iter_loop_lb2_sum2 :
  forall fuel n,
    0 < fuel ->
    fib_iter_loop_time_lb2 fuel n =
    1 + sum 0 (fuel - 1) (fplus (const 1) (fun m => plus_two_fibs_time (n+m))).
Proof.
  intros.
  rewrite fib_iter_loop_lb2_is_a_sum; auto.
Qed.  

Lemma fib_iter_loop_lb2_sum3 :
  forall fuel n,
    0 < fuel ->
    fib_iter_loop_time_lb2 fuel n =
    1 + fuel + sum 0 (fuel - 1) (fun m => plus_two_fibs_time (n+m)).
Proof.
  intros.
  rewrite fib_iter_loop_lb2_sum2; auto.
  rewrite <- sum_over_fns.
  unfold const.
  rewrite sum_constant with (k:=fuel-1); try omega.
Qed.

Lemma fib_iter_loop_lb2_upper_bound1 :
  forall fuel n,
    0 < fuel ->
    fib_iter_loop_time_lb2 fuel n <=
    1 + fuel + sum 0 (fuel - 1) (const (plus_two_fibs_time (n+fuel))).
Proof.
  intros.
  rewrite fib_iter_loop_lb2_sum3; auto.
  apply plus_le_compat; auto.
  apply sum_preserves_order_in_range.
  intros.
  unfold const.  
  apply plus_two_fibs_time_monotone.
  apply plus_le_compat; auto.
  omega.
Qed.
  
Lemma fib_iter_loop_lb2_lower_bound1 :
  forall fuel n,
    4 < fuel ->
    1 + fuel + sum (div2 fuel) (fuel-1) (fun m => plus_two_fibs_time (n+m)) <=
    fib_iter_loop_time_lb2 fuel n.
Proof.
  intros.
  rewrite fib_iter_loop_lb2_sum3; try omega.
  apply plus_le_compat; auto.
  apply sum_splits_inc.
  assert (1 <= div2 fuel).
  replace 1 with (div2 2); auto.
  apply div2_monotone; auto.
  omega.
  assert (1 < div2 fuel).
  assert (div2 4 <= div2 fuel). apply div2_monotone. omega. simpl in H1. omega.
  omega.
  destruct (even_odd_dec fuel).
  replace fuel with (div2 fuel + div2 fuel) at 2.
  rewrite <- plus_0_r at 1.
  replace (div2 fuel + div2 fuel - 1) with (div2 fuel + (div2 fuel - 1)); try omega.
  apply plus_lt_compat_l.
  assert (1 < div2 fuel).
  assert (div2 4 <= div2 fuel). apply div2_monotone. omega. simpl in H0. omega.
  omega.
  replace (div2 fuel+ div2 fuel) with (double (div2 fuel)).
  rewrite even_double. auto. auto. auto.
  replace fuel with (S (double (div2 fuel))) at 2.
  replace (S (double (div2 fuel)) - 1) with (double (div2 fuel)); try omega.
  unfold double.
  rewrite <- plus_0_l at 1.
  apply plus_lt_compat_r.
  assert (1 < div2 fuel).
  assert (div2 4 <= div2 fuel). apply div2_monotone. omega. simpl in H0. omega.
  omega.
  apply eq_sym. apply odd_double. auto.
Qed.

Lemma fib_iter_loop_lb2_lower_bound2 :
  forall fuel n,
    4 < fuel ->
    1 + fuel + sum (div2 fuel) (fuel-1) (const (plus_two_fibs_time (n + div2 fuel))) <=
    fib_iter_loop_time_lb2 fuel n.
Proof.  
  intros.
  apply (le_trans
           (1 + fuel + sum (div2 fuel) (fuel - 1) (const (plus_two_fibs_time (n + div2 fuel))))
           (1 + fuel + sum (div2 fuel) (fuel-1) (fun m => plus_two_fibs_time (n+m)))).
  apply plus_le_compat; auto.
  apply sum_preserves_order.
  intros.
  unfold const.  
  apply plus_two_fibs_time_monotone. omega.
  apply fib_iter_loop_lb2_lower_bound1. auto.
Qed.


Lemma fib_iter_loop_lb2_closed_upper_bound :
  forall fuel n,
    0 < fuel ->
    fib_iter_loop_time_lb2 fuel n <=
    1 + fuel + fuel*plus_two_fibs_time (n+fuel).
Proof.  
  intros.
  eapply le_trans.
  apply fib_iter_loop_lb2_upper_bound1; auto.
  apply plus_le_compat; auto.
  unfold const.
  rewrite sum_constant with (k:=fuel-1); try omega.
  replace (fuel - 1 + 1 ) with fuel; try omega.
Qed.

Lemma fib_iter_loop_time_lb2_closed_lower_bound :
  forall fuel n,
    4 < fuel ->
    1 + fuel + (div2 fuel)*(plus_two_fibs_time (n + div2 fuel)) <=
    fib_iter_loop_time_lb2 fuel n.
Proof.
  intros.
  apply (le_trans
           (1 + fuel + div2 fuel * plus_two_fibs_time (n + div2 fuel))
           (1 + fuel + sum (div2 fuel) (fuel-1) (const (plus_two_fibs_time (n + div2 fuel))))).

  apply plus_le_compat; auto.
  unfold const.
  destruct (even_odd_dec fuel).
  erewrite sum_constant. apply mult_le_compat; auto.
  assert (div2 fuel <= (div2 fuel - 1 + 1)); try omega.
  apply H0.
  replace (div2 fuel + (div2 fuel - 1)) with (div2 fuel + div2 fuel - 1); try omega.
  replace fuel with (double (div2 fuel)) at 3. auto. rewrite even_double. auto. auto.
  erewrite sum_constant. apply mult_le_compat; auto.
  assert (div2 fuel <= div2 fuel + 1); try omega.
  apply H0.
  replace fuel with (S (double (div2 fuel))) at 3.
  replace (S (double (div2 fuel)) - 1) with (double (div2 fuel)); try omega.
  unfold double. auto.
  rewrite <- odd_double; auto.
  apply fib_iter_loop_lb2_lower_bound2; auto.
Qed.  
  
  
Lemma fib_iter_loop_time_lb_monotone :
  forall a b n n',
    n <= n' ->
    fib_iter_loop_time_lb n a b <= fib_iter_loop_time_lb n' a b.
Proof.
  intros.
  apply (well_founded_ind
           lt_wf
           (fun n => forall a b n', n<=n'-> fib_iter_loop_time_lb n a b <= fib_iter_loop_time_lb n' a b));[|auto].
  intros.
  destruct x.
  simpl.
  inversion H1.
  simpl.
  auto.
  simpl.
  omega.
  inversion H1.
  simpl.
  auto.
  simpl.
  apply plus_le_compat; auto.
  apply plus_le_compat.
  auto.
  apply H0.
  auto.
  omega.
Qed.

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

Lemma fib_iter_loop_time_lb2_lower_bound :
  forall fuel n,
    fuel*(plus_two_fibs_time n + 1) <=  fib_iter_loop_time_lb2 fuel n. 
Proof.
  intro fuel.
  induction fuel.
  intros.
  simpl.
  auto.
  intros.
  simpl.
  rewrite <- plus_assoc. rewrite <- plus_assoc.
  apply plus_le_compat.
  auto. rewrite plus_comm. apply plus_le_compat; auto.
  eapply le_trans.
  apply IHfuel.
  apply fib_iter_loop_time_lb2_grows.
Qed.


Lemma div2_inc1 : forall n, div2 n <= div2 (S n).
Proof.
  intros.
  destruct (even_odd_dec n).
  rewrite even_div2; auto.
  rewrite <- odd_div2; auto.
Qed.  

Lemma inc_implies_mono : forall f, (forall n, f n <= f (S n)) -> monotone f.
Proof.
  intros.
  unfold monotone.
  intros.
  induction m.
  inversion H0.
  auto.
  apply le_lt_or_eq in H0.
  destruct H0.
  assert (n <= m); try omega.
  eapply le_trans.
  apply IHm.
  auto.
  auto.
  subst.
  auto.
Qed.  

Lemma div2_monotone : monotone div2.
Proof.
  unfold monotone.
  intros.
  apply inc_implies_mono.
  apply div2_inc1.
  auto.
Qed.  
  
Lemma plus_two_fibs_time_below :
  forall n, 4<=n -> n <= 4*plus_two_fibs_time n.
Proof.
  intros.
  inversion H.
  compute. omega.
  inversion H0.
  compute.
  omega.
  unfold plus_two_fibs_time.
  apply (le_trans (S (S m0))
                  (4*plus_time_lb (fib (S (S m0))) (fib (S (S m0))))).
    
  apply (le_trans (S (S m0))
                  (4*cl_log (fib (S (S m0))))).
  apply (le_trans (S (S m0))
                  (4*div2 m0)).
  replace 4 with (2+2);[|omega].
  rewrite mult_plus_distr_r.
  destruct (even_odd_dec m0).
  rewrite even_double at 1; try repeat constructor;auto.
  simpl div2.
  unfold double.
  replace (S (div2 m0) + S (div2 m0)) with (2*div2 m0 + 2*1);[|omega].
  apply plus_le_compat;auto.
  apply mult_le_compat;auto.
  apply (le_trans 1 (div2 4)).
  simpl. auto.
  apply div2_monotone.
  auto.
  rewrite odd_double at 1;try repeat constructor;auto.
  simpl div2.
  unfold double.
  replace (S (S (div2 m0) + S (div2 m0))) with (2*div2 m0 + 3);[|omega].
  apply plus_le_compat;auto.
  subst.
  apply (le_trans 3 (2*div2 4)).
  simpl. auto.
  apply mult_le_compat;auto.
  apply div2_monotone; auto.
  apply mult_le_compat; auto.
  apply fib_log_lower_bound.
  apply mult_le_compat;auto.
  apply log_below_plus_time_nn.
  apply mult_le_compat;auto.
  unfold plus_time_lb.
  apply plus_le_compat; auto.
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

Lemma fib_iter_loop_time_lb3_Sn :
  forall fuel n,
    fib_iter_loop_time_lb3 fuel (S n) = fib_iter_loop_time_lb3 fuel n + fuel.
Proof.
  intro fuel.
  apply (well_founded_ind
           lt_wf
           (fun fuel => forall n,  fib_iter_loop_time_lb3 fuel (S n) = fib_iter_loop_time_lb3 fuel n + fuel)).
  intros.
  destruct x.
  simpl. auto.
  simpl.
  rewrite H; auto.
  omega.
Qed.

Lemma fib_iter_loop_time_lb3_mono_2 :
  forall fuel, monotone (fib_iter_loop_time_lb3 fuel).
  intros.
  unfold monotone.
  induction fuel.
  intros.
  simpl. auto.
  intros.
  simpl.
  apply plus_le_compat;auto.
  apply plus_le_compat;auto.
  apply IHfuel.
  apply plus_le_compat;auto.
Qed.

Lemma closed_form_fib_iter_loop_time_lb3 :
  forall n,
    fib_iter_loop_time_lb3 n 0 = div2 (n*(n+1)) + 1.
Proof.
intros.
induction n.
simpl. auto.
simpl fib_iter_loop_time_lb3.
rewrite fib_iter_loop_time_lb3_Sn.
rewrite IHn.
destruct (even_odd_dec n).
assert (even (S n +1 )).
simpl.
constructor.
replace (n+1) with (S n);[|omega].
constructor.
auto.
rewrite even_div_product; auto.
replace (S n * (S n + 1)) with ((S n + 1) * S n);[|rewrite mult_comm;auto].
rewrite even_div_product; auto.
replace (S n + 1) with (S (S n));[|omega].
simpl.
replace (n+1) with (S n);[|omega].
omega.
replace (n+1) with (S n);[|omega].
replace (n* S n) with (S n * n);[|rewrite mult_comm;auto].
rewrite even_div_product;[|constructor;auto].
rewrite even_div_product;[|constructor;auto].
replace (S n + 1) with (n+2);[|omega].
rewrite mult_plus_distr_l.
replace 2 with (1+1);[|omega].
rewrite mult_plus_distr_l.
rewrite mult_1_r.
replace  (div2 (S n) + div2 (S n)) with (S n).
omega.
replace (S n) with (double (div2 (S n))) at 1.
auto.
apply eq_sym.
apply even_double.
constructor.
auto.
Qed.

Lemma fib_iter_loop_time_lb3_full_closed_form :
  forall n m,
    fib_iter_loop_time_lb3 n m = div2(n*(n+1)) + 1 + n*m.
Proof.
  intros.
  generalize dependent n.
  induction m.
  intros.
  rewrite mult_0_r.
  rewrite plus_0_r.
  apply closed_form_fib_iter_loop_time_lb3.
  intros.
  rewrite fib_iter_loop_time_lb3_Sn.
  rewrite IHm.
  replace (S m) with (m + 1);[|omega].
  rewrite mult_plus_distr_l.
  rewrite mult_plus_distr_l.
  rewrite plus_assoc.
  omega.
Qed.

Lemma fib_iter_loop_time_lb3_sq : 
  exists n,
    forall n',
      n <= n' ->
      big_oh (fun n => n*n) (fun fuel => fib_iter_loop_time_lb3 fuel n').
Proof.
  exists 0.
  intros.
  exists 0.
  exists 2.
  intros.
  apply (le_trans (n*n)
                  (2*fib_iter_loop_time_lb3 n 0)).
  rewrite closed_form_fib_iter_loop_time_lb3.
  rewrite mult_plus_distr_l.
  simpl.
  rewrite plus_0_r.
  replace (div2 (n * (n + 1)) + div2 (n * (n + 1))) with (n*(n+1)).
  rewrite mult_plus_distr_l.
  omega.
  apply even_double.
  destruct (even_odd_dec n).
  apply even_mult_l.
  auto.
  apply even_mult_r.
  replace (n+1) with (S n);[|omega].
  constructor.
  auto.
  apply mult_le_compat;auto.
  apply  fib_iter_loop_time_lb3_mono_2.
  auto.
Qed.

Lemma mult_cancel_l :
  forall m n p,
    p > 0 -> n = m -> p*m = p*n.
Proof.
  intros m n p H.
  assert ((p * n = p * m <-> n = m)).
  apply NPeano.Nat.mul_cancel_l.
  omega.
  destruct H0.
  auto.
Qed.

Lemma mult_cancel_r :
  forall m n p,
    p > 0 -> n = m -> m*p = n*p.
Proof.
  intros m n p H.
  assert (( n*p = m*p <-> n = m)).
  apply NPeano.Nat.mul_cancel_r.
  omega.
  destruct H0.
  auto.
Qed.

Lemma mult_4_div2 : forall n, 2 < n -> n <= 4*div2 n.
Proof.
  intros.
  destruct (even_odd_dec n).
  replace 4 with (2*2); try omega.
  rewrite <- mult_assoc.
  replace (2* div2 n) with (div2 n + div2 n); try omega.
  rewrite even_double at 1; auto. unfold double. omega.
  rewrite odd_double at 1; auto.
  unfold double.
  replace (S (div2 n + div2 n)) with (div2 n + div2 n + 1); try omega.
  replace (4*div2 n) with (div2 n + div2 n + 2 * div2 n); try omega.
  apply plus_le_compat; auto.
  apply (le_trans 1 (2*1)); try omega.
  apply mult_le_compat; auto.
  replace 1 with (div2 2);[| try compute; auto].
  apply div2_monotone.
  omega.
Qed.
  
Lemma fib_iter_loop_lb23 : 
  exists n,
    forall n',
      n <= n' ->
      big_oh (fun fuel => fib_iter_loop_time_lb3 fuel n')
             (fun fuel => fib_iter_loop_time_lb2 fuel n').
Proof.
  
  exists 0.
  intros.
  exists 8.
  exists 64.
  intros.
  rewrite fib_iter_loop_time_lb3_full_closed_form.
  apply (le_trans (div2 (n * (n + 1)) + 1 + n * n')
                  (n*(n+1)+1+n*n')).
  repeat apply plus_le_compat;auto.
  assert ( div2 (n * (n + 1)) < n * (n + 1)).
  apply lt_div2.
  inversion H0. simpl. omega.
  compute. omega. omega.
  rewrite mult_plus_distr_l. rewrite mult_1_r.
  replace (n * n + n + 1 + n * n') with (1 + n + n*n' + n*n); try omega.
  apply (le_trans (1 + n + n*n' + n*n)
                  (64*(1 + n + (div2 n)*(plus_two_fibs_time (n' + div2 n))))).
  
  repeat (rewrite mult_plus_distr_l).
  rewrite mult_1_r.
  rewrite <- plus_assoc.
  apply plus_le_compat. omega.
  rewrite mult_assoc.
  replace 64 with (16*4); try omega.
  replace (16 * 4 * div2 n * plus_two_fibs_time (n' + div2 n))
          with
          (16 * div2 n * (4 * plus_two_fibs_time (n' + div2 n))).
  apply (le_trans
           ( n * n' + n * n)
           (16*div2 n * (n'+ div2 n))).
  
  replace 16 with (4*4); try omega.
  apply (le_trans  (n * n' + n * n)
                   (4*n*(n'+div2 n))).

  rewrite mult_plus_distr_l.
  apply plus_le_compat.
  apply mult_le_compat; auto. omega.

  replace (4*n) with (n*4).  
  repeat (rewrite <- mult_assoc).
  apply mult_le_compat_l; auto.
  apply mult_4_div2. omega.
  omega.
  repeat (rewrite <- mult_assoc).
  apply mult_le_compat; auto.
  rewrite mult_assoc.
  apply mult_le_compat; auto.
  apply mult_4_div2. omega.
  apply mult_le_compat; auto.
  apply plus_two_fibs_time_below.
  rewrite <- plus_0_l at 1. apply plus_le_compat. auto.
  replace 4 with (div2 8);[|compute; auto].
  apply div2_monotone.
  auto.
  repeat (rewrite <- mult_assoc).
  apply mult_cancel_l. omega.
  repeat (rewrite mult_assoc).
  apply mult_cancel_r.
  assert (plus_two_fibs_time 4 <= plus_two_fibs_time (n' + div2 n)).
  apply plus_two_fibs_time_monotone.
  rewrite <- plus_0_l at 1. apply plus_le_compat. auto.
  replace 4 with (div2 8);[|compute;auto].
  apply div2_monotone. auto.
  replace (plus_two_fibs_time 4) with 4 in H1;[|compute;auto].
  omega. omega.
  apply mult_le_compat;auto.
  apply fib_iter_loop_time_lb2_closed_lower_bound. omega.
Qed.

Lemma fib_iter_time_lb_big_oh_fib_iter_loop_time_lb : 
  big_oh (fun n => fib_iter_loop_time_lb n 0 1) fib_iter_time_lb.
Admitted.
(* this is likely true. *)

Lemma fib_iter_loop_last_arg_invariant :
  forall fb, 
    exists X, 
      forall n,
        8 < n ->
        fib_iter_loop_time_lb2 n fb <= X * fib_iter_loop_time_lb2 n 0.
Proof.
  intros.
  exists (64*(1+fb)).
  intros.
  eapply le_trans.
  apply fib_iter_loop_lb2_closed_upper_bound; try omega.
  apply (le_trans
           (1 + n + n * plus_two_fibs_time (fb + n))
           (64*(1+fb)*(1+n+(div2 n)*(plus_two_fibs_time (0 + div2 n)))));
    [|apply mult_le_compat; auto;
     apply fib_iter_loop_time_lb2_closed_lower_bound]; try omega.
  rewrite plus_0_l.
  repeat (rewrite mult_plus_distr_l).
  repeat (rewrite mult_1_r).
  repeat (rewrite plus_assoc).
  repeat (rewrite mult_plus_distr_l).
  repeat (rewrite mult_plus_distr_r).
  repeat (rewrite plus_assoc).
  eapply le_trans.
  apply plus_le_compat.
  apply le_refl.
  apply mult_le_compat.
  apply le_refl.
  apply plus_two_fibs_time_upper_bound.
  apply (le_trans
           (1 + n + n * (fb + n + 4))
           (64 + 64 * fb + 64 * n + 64 * fb * n +
            16 * (div2 n * (div2 n)) +
            16 * fb * (div2 n * (div2 n)))).
  repeat (rewrite mult_plus_distr_l).
  repeat (rewrite plus_assoc).
  replace (1 + n + n * fb + n * n + n * 4)
  with (1 + 5*n + n * fb + n * n);[|omega].
  replace (64 + 64 * fb + 64 * n + 64 * fb * n + 16 * (div2 n * div2 n) +
           16 * fb * (div2 n * div2 n))
  with (64 + 64 * fb + 64 * n + 64 * fb * n + 16 * fb * (div2 n * div2 n) +
        16 * (div2 n * div2 n));[|omega].
  apply plus_le_compat.
  replace (n*fb) with (fb*n);[|apply mult_comm].
  repeat (rewrite <- mult_assoc).
  remember (fb*n) as A.
  remember (fb*(div2 n * div2 n)) as B.
  omega.
  replace 16 with (4*4);[|omega].
  replace (4*4*(div2 n * div2 n)) with ((4*div2 n) *(4*div2 n)).
  apply mult_le_compat.
  apply mult_4_div2; omega.
  apply mult_4_div2; omega.
  repeat (rewrite <- mult_assoc).
  replace (div2 n * (4*div2 n)) with ((4*div2 n)*div2 n) at 1;[|apply mult_comm].
  repeat (rewrite mult_assoc). auto.
  apply plus_le_compat; auto.
  apply plus_le_compat; auto.
  replace 64 with (16*4); try omega.
  rewrite <- mult_assoc.
  apply mult_le_compat; auto.
  replace (div2 n * plus_two_fibs_time (div2 n)) with
          (plus_two_fibs_time (div2 n) * div2 n);[|apply mult_comm].
  rewrite mult_assoc.
  apply mult_le_compat; auto.
  apply plus_two_fibs_time_below.
  replace 4 with (div2 8).
  apply div2_monotone.
  omega.
  auto.
  replace 64 with (16*4); try omega.
  repeat (rewrite <- mult_assoc).
  apply mult_le_compat; auto.
  repeat (rewrite mult_assoc).
  replace (4*fb) with (fb*4);[|apply mult_comm].
  repeat (rewrite <- mult_assoc).
  apply mult_le_compat; auto.
  repeat (rewrite mult_assoc).
  replace (4*div2 n) with (div2 n * 4);[|apply mult_comm].
  repeat (rewrite <- mult_assoc).
  apply mult_le_compat;auto.
  apply plus_two_fibs_time_below.
  replace 4 with (div2 8).
  apply div2_monotone.
  omega.
  auto.
Qed.  


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
  exists 9 X.
  intros n H.
  replace (fib_iter_loop_time_lb n 0 1) with (fib_iter_loop_time_lb n (fib 0) (fib 1));[|unfold fib;auto].
  rewrite fib_iter_loop_lb12.
  apply FACT. omega.
Qed.

