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

Lemma relate_fib_iter_fib_iter_loop :
  forall n,
    1 < n ->
    fib_iter_time_lb n = 1 + fib_iter_loop_time_lb (n-1) 0 1.
Proof.
  intros.
  destruct n. inversion H.
  destruct n. intuition.
  unfold fib_iter_time_lb.
  replace (S (S n) - 1) with (S n); try omega.
Qed.  
  

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

  
Fixpoint fib_iter_loop_time_lb2 fuel n :=
  match fuel with
    | 0 => 1
    | S fuel' => plus_two_fibs_time n + 
                 fib_iter_loop_time_lb2 fuel' (n+1) + 1
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
  

Lemma n_squared_big_O_fib_iter_time_lb:
  big_oh (fun n => n*n) fib_iter_time_lb.
Proof.
  exists 10.
  exists 64.
  intros.
  rewrite relate_fib_iter_fib_iter_loop; try omega.
  rewrite mult_plus_distr_l. rewrite mult_1_r.
   replace 0 with (fib 0) at 4;[|simpl; auto].
   replace 1 with (fib 1) at 4;[|simpl;auto].
   rewrite fib_iter_loop_lb12.
   apply (le_trans
            (n*n)
            (64 + 64*(1+ (n-1) + (div2 (n-1)*(plus_two_fibs_time (0+div2 (n-1)))))));
     [|apply plus_le_compat;auto;
      apply mult_le_compat;auto;
      apply fib_iter_loop_time_lb2_closed_lower_bound;
      omega].
   rewrite plus_0_l.
   remember (n-1) as N.
   replace n with (N+1);[|omega].
   repeat (rewrite mult_plus_distr_l).
   repeat (rewrite mult_plus_distr_r).
   repeat (rewrite plus_assoc).
   repeat (rewrite mult_1_r).
   repeat (rewrite mult_1_l).
   replace ( N * N + N + N + 1) with (N * N + 2*N + 1);[|omega].
   apply (le_trans
            (N * N + 2 * N + 1)
            (64 + 64 + 64 * N + 16 * (div2 N * (div2 N))));
     [|apply plus_le_compat;auto;
       replace 64 with (16*4);[|omega];
       repeat (rewrite <- mult_assoc);
       apply mult_le_compat;auto;
       replace ((div2 N * plus_two_fibs_time (div2 N))) with
       ((plus_two_fibs_time (div2 N) * div2 N));[|apply mult_comm];
       rewrite mult_assoc;
       apply mult_le_compat;auto;
       apply plus_two_fibs_time_below;
       replace 4 with (div2 8);[|simpl;auto];
       apply div2_monotone;
       omega].
   apply (le_trans
            (N * N + 2 * N + 1)
            (64 + 64 + 64 * N + N*N)).
   omega.
   apply plus_le_compat; auto.
   rewrite  mult_assoc.
   replace (16*div2 N) with (div2 N * 16);[|apply mult_comm].
   replace 16 with (4*4);[|omega].
   rewrite mult_assoc.
   replace (div2 N * 4) with (4*div2 N);[|apply mult_comm].
   replace (4 * div2 N * 4 * div2 N) with ((4*div2 N)*(4*div2 N));
     [|repeat (rewrite mult_assoc); auto].
   apply mult_le_compat.
   apply mult_4_div2. omega.
   apply mult_4_div2. omega.
Qed.

Theorem fib_iter_n_squared: big_omega fib_iter_time_lb (fun n => n * n).
Proof.
  apply big_oh_rev.
  apply n_squared_big_O_fib_iter_time_lb.
Qed.

