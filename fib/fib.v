Require Import Braun.common.util Braun.common.le_util Braun.common.same_structure.
Require Import Braun.common.log Braun.common.big_oh Braun.common.pow.
Require Import Braun.monad.monad Braun.arith.plus.
Require Import Program Div2 Omega Even.

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

Lemma fib_sum_less_than_fib_product:
  forall n, 
    n >= 4 ->
    fib n + fib n <= fib n * fib n.
Proof.
  intros n LE.
  destruct n;[intuition|].
  destruct n;[intuition|].
  destruct n;[intuition|].
  destruct n;[intuition|].
  clear LE.
  apply (well_founded_ind
           lt_wf
           (fun n => fib (S (S (S (S n)))) + fib (S (S (S (S n)))) <=
                     fib (S (S (S (S n)))) * fib (S (S (S (S n)))))).
  clear n; intros n IND.
  destruct n.
  compute; omega.
  destruct n.
  compute; omega.
  
  replace (fib (S (S (S (S (S (S n))))))) 
  with (fib (S (S (S (S (S n))))) + (fib (S (S (S (S n))))));[|unfold fib;omega].
  replace ((fib (S (S (S (S (S n))))) + fib (S (S (S (S n))))) +
           (fib (S (S (S (S (S n))))) + fib (S (S (S (S n))))))
  with ((fib (S (S (S (S n)))) + fib (S (S (S (S n))))) +
        (fib (S (S (S (S (S n))))) + fib (S (S (S (S (S n)))))));[|omega].
  apply (le_trans ((fib (S (S (S (S n)))) + fib (S (S (S (S n))))) +
                   (fib (S (S (S (S (S n))))) + fib (S (S (S (S (S n)))))))
                  ((fib (S (S (S (S n)))) * fib (S (S (S (S n))))) +
                   (fib (S (S (S (S (S n))))) * fib (S (S (S (S (S n)))))))).
  apply plus_le_compat; apply IND; auto.
  rewrite mult_plus_distr_r.
  repeat (rewrite mult_plus_distr_l).
  remember (fib (S (S (S (S n)))) * fib (S (S (S (S n))))) as i.
  remember (fib (S (S (S (S (S n))))) * fib (S (S (S (S (S n)))))) as j.
  replace (j + fib (S (S (S (S (S n))))) * fib (S (S (S (S n)))) +
           (fib (S (S (S (S n)))) * fib (S (S (S (S (S n))))) + i)) 
  with (i + j + 
        (fib (S (S (S (S (S n))))) * fib (S (S (S (S n)))) +
         fib (S (S (S (S n)))) * fib (S (S (S (S (S n)))))));[|omega].
  apply le_plus_trans.
  omega.
Qed.

Lemma cl_log_big_oh_double : 
  big_oh (fun n => cl_log (2 * fib n)) (fun n => cl_log (fib n)).
Proof.
  apply (big_oh_trans (fun n => cl_log (2 * fib n))
                      (fun n => (cl_log (fib n * fib n)))).
  exists 4 1.
  intros n LE.
  rewrite mult_1_l.
  apply cl_log_monotone.
  replace (2 * fib n) with (fib n + fib n);[|simpl mult;omega].
  apply fib_sum_less_than_fib_product.
  omega.

  exists 0 4.
  intros n _.
  apply cl_log_square_four.
Qed.

