Require Import Braun.common.util Braun.common.le_util Braun.common.same_structure.
Require Import Braun.common.log Braun.common.big_oh Braun.common.pow.
Require Import Braun.monad.monad.
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
    | O => 3
    | S n' =>
      match n' with
        | O => 5
        | S n'' => (fib_rec_time n'') + (fib_rec_time n') + 11
      end
  end.

Definition fib_rec_result (n:nat) (res:nat) (c:nat) :=
    Fib n res /\
    c = fib_rec_time n.

Load "fib_rec_gen.v".

Next Obligation.
  split;eauto.
Qed.

Next Obligation.
  split;eauto.
Qed.

Next Obligation.
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
    ((fib_rec_time n) + (fib_rec_time (S n)) + 11); auto.

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
  with (fib_rec_time (S n) + fib_rec_time (S (S n)) + 11);
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

Definition fib_iter_loop_result (fuel:nat) (target:nat) (a:nat) (b:nat)
           (res:nat) (c:nat) :=
    1 < target ->
    fuel < target ->
    Fib (target - fuel - 1) a ->
    Fib (target - fuel) b ->
    Fib target res /\
    c = 10 * fuel + 3.

Load "fib_iter_loop_gen.v".

Next Obligation.
  unfold fib_iter_loop_result.
  intros.

  split.
  destruct target.
  intuition.
  destruct target.
  intuition.
  eauto.
  omega.
Qed.

Next Obligation.
  unfold fib_iter_loop_result in *.
 rename fuel0 into fuel.
 clear am H1.
 rename H0 into IH.
 intros LT LE Fa Fb.

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
 auto.

 split.
 
 auto.

 omega.
Qed.

Fixpoint fib_iter_time (n:nat) :=
  match n with
    | O => 3
    | S n' =>
      match n' with
        | O => 5
        | S n'' => 10 * n'' + 23
      end
  end.

Definition fib_iter_result (target:nat) (res:nat) (c:nat) :=
  Fib target res /\
  c = fib_iter_time target.

Load "fib_iter_gen.v".

Next Obligation.
  unfold fib_iter_result.
  split; simpl; eauto.
Qed.  

Next Obligation.
  unfold fib_iter_result.
  split; simpl; eauto.
Qed.

Next Obligation.
  unfold fib_iter_result, fib_iter_loop_result, fib_iter_time in *.
  clear am H1.
  rename H0 into FIL.
  edestruct FIL; [ | | | | split; auto]; clear FIL.
  omega. omega.
  replace (S (S target'') - S target'' - 1) with 0; [|omega].
  auto.
  replace (S (S target'') - S target'') with 1;[|omega].
  auto.
  subst an.
  replace (S target'') with (target'' + 1);[|omega].
  rewrite mult_plus_distr_l.
  omega.
Qed.

Theorem fib_iter_linear: big_oh fib_iter_time (fun n => n).
Proof.
  exists 2 20.
  intros n LT.
  destruct n;[intuition|].
  destruct n;[intuition|].
  clear LT.
  unfold fib_iter_time.
  omega.
Qed.
  
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
