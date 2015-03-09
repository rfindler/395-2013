Require Import Braun.common.util Braun.common.le_util Braun.common.same_structure.
Require Import Braun.common.log Braun.common.big_oh Braun.common.pow.
Require Import Braun.monad.monad Braun.arith.plus.
Require Import Program Div2 Omega.

Inductive Fib : nat -> nat -> Prop :=
| F_0 :
  Fib 0 0
| F_1 :
  Fib 1 1
| F_n :
  forall n a b,
    Fib n a ->
    Fib (S n) b  ->
    Fib (S (S n)) (a + b).
Hint Constructors Fib.

Fixpoint fib n :=
  match n with 
    | 0 => 0
    | S n' => 
      match n' with
        | 0 => 1
        | S n'' => fib n''  + fib n'
      end
  end.

Lemma Fib_fib:
  forall n, Fib n (fib n).
Proof.
  apply (well_founded_induction lt_wf).
  intros n IH.
  destruct n as [|n].
  eauto.
  destruct n as [|n].
  eauto.
  replace (fib (S (S n))) with (fib n + fib (S n));auto.
Defined.

Fixpoint fib_rec_time (n:nat) :=
  match n with
    | O => 1
    | S n' =>
      match n' with
        | O => 1
        | S n'' => (fib_rec_time n'') + (fib_rec_time n') + 1
      end
  end.

Definition fib_rec_result (n:nat) (res:nat) (c:nat) :=
    Fib n res /\
    c = fib_rec_time n.

Load "fib_rec_gen.v".

Next Obligation.
Proof.
  split;eauto.
Qed.

Next Obligation.
Proof.
  split;eauto.
Qed.

Next Obligation.
Proof.
  clear am H3 am0 H2.
  rename H1 into FR_A.
  rename H0 into FR_B.

  destruct FR_A as [FIBA FIBTIMEA].
  destruct FR_B as [FIBB FIBTIMEB].
  unfold fib_rec_result in *.
  split.
  eauto.
  rename n'' into n.
  destruct n as [|n]; subst; simpl; omega.
Qed.

Program Lemma fib_big_oh_fib:
  big_oh fib fib_rec_time.
Proof.
  exists 0 1.
  apply (well_founded_induction lt_wf (fun n => 0 <= n -> fib n <= 1 * (fib_rec_time n))).
  intros n IH _.
  destruct n as [|n]. simpl. omega.
  destruct n as [|n]. simpl. auto.
  replace (fib_rec_time (S (S n))) with
    ((fib_rec_time n) + (fib_rec_time (S n)) + 1); auto.

  assert (fib n <= 1 * (fib_rec_time n)) as IHn.
  eapply IH. auto. omega.
  assert (fib (S n) <= 1 * (fib_rec_time (S n))) as IHSn.
  eapply IH. auto. omega.

  rewrite mult_1_l in *.

  clear IH.
  replace (fib (S (S n))) with (fib n + fib (S n)); auto.
  omega.
Qed.

Fixpoint fib_rec_time2 (n:nat) :=
  match n with
    | O => 0
    | S n' =>
      match n' with
        | O => 1
        | S n'' => (fib_rec_time2 n'') + (fib_rec_time2 n') + 1
      end
  end.

Lemma fib_rec_time12 : big_oh fib_rec_time fib_rec_time2.
Proof.
  exists 1 11.
  intros n LT.
  destruct n. intuition.
  clear LT.
  apply (well_founded_induction
           lt_wf
           (fun n => fib_rec_time (S n) <= 11 * (fib_rec_time2 (S n)))).
  clear n; intros n IND.
  destruct n.
  simpl.
  omega.
  destruct n.
  simpl.
  omega.
  replace (fib_rec_time (S (S (S n)))) 
  with (fib_rec_time (S n) + fib_rec_time (S (S n)) + 1);
    [|unfold fib_rec_time;omega].
  replace (fib_rec_time2 (S (S (S n)))) 
  with (fib_rec_time2 (S n) + fib_rec_time2 (S (S n)) + 1);
    [|unfold fib_rec_time2;omega].
  repeat (rewrite mult_plus_distr_l).
  apply plus_le_compat.
  apply plus_le_compat;apply IND;auto.
  omega.
Qed.

Lemma fib_SS : forall n, fib (S (S n)) = fib (S n) + fib n.
Proof.
  intros; unfold fib; rewrite plus_comm; auto.
Qed.

Lemma fib_monotone : forall (n : nat) (m : nat), m <= n -> fib m <= fib n.
Proof.
  intros n m LE.
  destruct LE.
  auto.
  remember (S m0) as n.
  assert (m < n) as LT; [omega|].
  clear LE Heqn.
  apply (well_founded_induction lt_wf
                                (fun (n : nat) =>
                                   forall (m : nat), m < n -> fib m <= fib n)); auto.
  clear m m0 n LT.
  intros x0 H m H0.
  destruct x0 as [|n'].
  inversion H0.
  destruct n' as [|n''].
  inversion H0; [compute; omega|inversion H2].
  rewrite fib_SS.
  destruct m as [|m'].
  replace (fib 0) with 0; [|compute;auto].
  apply le_0_n.
  destruct m' as [|m''].
  apply le_plus_trans.
  destruct n'' as [|n''']; [|apply H]; try omega.
  destruct n'' as [|n''']; [intuition|]. 
  apply le_plus_trans.
  inversion H0; auto.
Qed.

Lemma fib_nonneg : forall n, 0 < fib (S n).
Proof.
  induction n;[simpl|rewrite fib_SS]; omega.
Qed.  

Lemma fib_rec_time2_fib_relationship : 
  forall n, fib_rec_time2 n + 1 = (fib (S (S n))).
Proof.
  intros.
  apply (well_founded_induction
           lt_wf
           (fun n => fib_rec_time2 n + 1 = (fib (S (S n))))).
  clear n; intros n IND.
  destruct n.
  simpl; reflexivity.
  destruct n.
  simpl; reflexivity.
  replace (fib_rec_time2 (S (S n))) with (fib_rec_time2 (S n) + fib_rec_time2 n + 1);
    [|unfold fib_rec_time2;omega].
  rewrite fib_SS.
  replace (fib_rec_time2 (S n) + fib_rec_time2 n + 1 + 1)
  with ((fib_rec_time2 (S n) + 1) + (fib_rec_time2 n + 1));[|omega].
  rewrite IND; auto.
Qed.

Lemma fib_rec_time23 : big_oh fib_rec_time2 fib.
Proof.
  exists 0 3.
  intros n _.
  assert ((fib_rec_time2 n + 1) <= S (3 * fib n));[|omega].
  rewrite fib_rec_time2_fib_relationship.
  replace (S (3 * fib n)) with (3 * fib n + 1);[|omega].
  rewrite fib_SS.
  replace (3 * fib n + 1) with (2 * fib n + 1 + fib n);[|omega].
  apply plus_le_compat; auto.
  destruct n.
  simpl.
  omega.
  rewrite fib_SS.
  replace (2 * fib (S n) + 1) with (fib (S n) + (fib (S n) + 1));[|omega].
  apply plus_le_compat;auto.
  apply le_plus_trans.
  apply fib_monotone; auto.
Qed.

Theorem fib_big_theta_fib:
  big_theta fib fib_rec_time.
Proof.
  split. 
  apply fib_big_oh_fib.
  apply big_oh_rev.
  apply (big_oh_trans fib_rec_time fib_rec_time2).
  apply fib_rec_time12.
  apply fib_rec_time23.
Qed.

Lemma fib_lower_bound : 
  forall n,
    pow 2 (div2 (S n)) <= 2 * fib (S n).
Proof.
  apply (well_founded_ind
           lt_wf
           (fun n => pow 2 (div2 (S n)) <= 2 * fib (S n))).
  intros n IND.
  destruct n;[simpl;auto|].
  destruct n;[simpl;auto|].
  replace (div2 (S (S (S n)))) with (S (div2 (S n)));[|unfold div2;auto].
  unfold pow; fold pow.
  apply (le_trans (2 * pow 2 (div2 (S n)))
                  (2 * (2 * fib (S n)))).
  apply mult_le_compat; auto.

  clear IND.
  apply mult_le_compat; auto.
  replace (fib (S (S (S n)))) with (fib (S (S n)) + fib (S n));[|simpl fib;omega].
  unfold mult.
  rewrite plus_0_r.
  apply plus_le_compat;auto.
  apply fib_monotone; auto.
Qed.

Theorem fib_big_omega_2_to_the_div2_n : 
  big_omega fib (fun n => pow 2 (div2 n)).
Proof.
  apply big_oh_rev.
  exists 1 2.
  intros n LT.
  destruct n. intuition.
  apply fib_lower_bound.
Qed.

Lemma fib_upper_bound : 
  forall n,
    fib n <= pow 2 n.
Proof.
  apply (well_founded_ind
           lt_wf 
           (fun n => fib n <= pow 2 n)).
  intros n IND.
  destruct n. simpl. auto.
  destruct n. simpl. auto.
  replace (fib (S (S n))) with (fib (S n) + fib n);[|unfold fib; omega].
  replace (pow 2 (S (S n))) with (2 * pow 2 (S n));[|unfold pow; omega].
  unfold mult; rewrite plus_0_r.
  apply (le_trans (fib (S n) + fib n)
                  (pow 2 (S n) + pow 2 n)).
  apply plus_le_compat; apply IND; auto.
  apply plus_le_compat; auto.
  apply pow2_monotone; auto.
Qed.

Theorem fib_big_oh_2_to_the_n : 
  big_oh fib (fun n => pow 2 n).
Proof.
  exists 0 1.
  intros n _.
  rewrite mult_1_l.
  apply fib_upper_bound.
Qed.

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


Fixpoint fib_iter_loop_time_lb2 fuel n :=
  match fuel with
    | 0 => 1
    | S fuel' => plus_time_lb (fib n) (fib (n+1)) +
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

Fixpoint fib_iter_loop_time_lb3 fuel :=
  match fuel with
    | 0 => 1
    | S fuel' => plus_time_lb (fib fuel') (fib fuel) +
                 fib_iter_loop_time_lb3 fuel' + 1
  end.

Lemma fib_iter_loop_lb23:
  forall n,
    fib_iter_loop_time_lb3 n = fib_iter_loop_time_lb2 n 0.
Proof.
  induction n.
  simpl.
  auto.
  unfold fib_iter_loop_time_lb3, fib_iter_loop_time_lb2.
  fold fib_iter_loop_time_lb3.
  fold fib_iter_loop_time_lb2.
  (* need a stronger induction hypothesis *)
  admit.
Qed.

Theorem fib_iter_nlogn: big_oh fib_iter_time_lb (fun n => n * fl_log n).
Admitted.
(* not sure I can prove this.... *)
  
Lemma mle_2_and_3 : forall a b, 3 * a < 2 * b -> 3 * (b + a) < 2 * (b + a + b).
Proof.
  intros.
  simpl. intuition.
Qed.

Lemma fib_S : forall (n : nat), n > 3 -> 3 * fib n < 2 * (fib (S n)).
Proof.
  apply (well_founded_induction lt_wf
                                (fun (n : nat) =>
                                   n > 3 -> 3 * fib n < 2 * (fib (S n)))).
  intros n IH g2.
  destruct n as [|n]; [compute; auto|].
  destruct n as [|n]; [inversion g2 as [|q G qq]; inversion G|].
  rewrite fib_SS.
  destruct n as [|n]; [compute; auto|].
  destruct n as [|n]; [inversion g2 as [|q1 G q2]; inversion G; omega|].
  destruct n as [|n]; [compute; auto|].
  destruct n as [|n]; [compute; auto|].
  replace (fib (S (S (S (S (S (S (S n))))))))
  with (fib (S (S (S (S (S n))))) + fib (S (S (S (S n)))) + fib (S (S (S (S (S n)))))).
  apply mle_2_and_3.
  apply IH; auto.
  omega.
  remember (fib (S (S (S (S (S n)))))) as a.
  remember (fib (S (S (S (S n))))) as b.
  rewrite fib_SS.
  rewrite <- Heqa.
  rewrite fib_SS.
  auto.
Qed.
Hint Resolve fib_S.

Lemma fib_log_div2 : forall (n : nat), 
                       n > 16 -> 3 * fib (cl_log (div2 n)) < 2 * fib (cl_log n).
Proof.
  intros n g16.
  unfold_sub cl_log (cl_log n).
  do 16 (destruct n as [|n]; [inversion g16; try omega|]).
  fold_sub cl_log.
  unfold div2. fold div2.
  apply fib_S.
  unfold gt.
  apply lt_le_trans with (m := cl_log 8); [compute; auto|]. 
  apply cl_log_monotone. 
  intuition.
Qed.

Hint Resolve fib_log_div2.
