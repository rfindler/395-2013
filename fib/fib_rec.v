Require Import Braun.common.util Braun.common.le_util.
Require Import Braun.common.log Braun.common.big_oh Braun.common.pow.
Require Import Braun.monad.monad Braun.arith.plus Braun.fib.fib.
Require Import Program Div2 Omega Even.


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

