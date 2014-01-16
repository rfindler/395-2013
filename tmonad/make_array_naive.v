Require Import Braun.tmonad.monad.
Require Import Braun.tmonad.insert.

Require Import Braun.logical.sequence.

Require Import Braun.common.braun.
Require Import Braun.common.array.
Require Import Braun.common.util.
Require Import Braun.common.log Braun.common.le_util.
Require Import Arith Arith.Even Arith.Div2 Omega.

Section make_array_naive.
  Variable A : Set.

  Fixpoint man_time' n : nat :=
    match n with
      | 0 => 1
      | S n' => man_time' n' + 3 * (fl_log n') + 5
    end.

  Program Fixpoint make_array_naive xs : 
    {! b !:! @bin_tree A
       !<! c !>!
       let n := length xs in
       Braun b n
       /\ c = man_time' n
       /\ SequenceR b xs !} :=
(match xs with
   | nil => 
     (++;
      (<== bt_mt))
   | cons x xs' => 
     (anorm5 <- (make_array_naive xs');
      (anorm6 <- (insert x anorm5);
       (++; ++; ++;
        (<== anorm6))))
 end).

  Obligation Tactic := auto.
  Next Obligation.
  Proof.
    intros xs x xs' Heqxs; subst xs.
    intros bt.
    intros [n [Bb [Heqn Sb]]].
    subst n.
    intros bt'.
    intros junk; clear junk.
    intros xn IH. 
    intros xn0.
    intros [Bbt [Heqxn0 Sbt]].
    subst xn0.
    intros n; subst n.

    remember (IH (length xs') Bb) as CONJ.
    clear HeqCONJ.
    destruct CONJ as [Bbt' [SR_IND Heqxn]].

    repeat constructor; auto.

    subst xn.
    simpl.
    omega.
  Qed.


  Lemma man_time'_nlogn_helper : 
    forall n,
      n * (3 * fl_log n + 5) + 1 <= 
      8 * n * fl_log n + 1.
  Proof.
    intros n.
    apply le_plus_left.
    replace (n * (3 * fl_log n + 5)) with (3 * n * fl_log n + 5 * n).
    replace (8*n*fl_log n) with (3 * n * fl_log n + 5 * n * fl_log n).
    apply le_plus_right.
    replace (5 * n * fl_log n) with (5 * (n * fl_log n)).
    apply le_mult_right.

    destruct n; auto.

    assert (S n = S n * 1) as H;[omega|rewrite H at 1; clear H].
    apply le_mult_right.
    apply one_le_fl_log_S.

    apply mult_assoc.

    replace 8 with (3+5);[|omega].
    rewrite <- mult_plus_distr_r.
    replace ((3+5)*n) with (3*n+5*n);[reflexivity|rewrite mult_plus_distr_r;reflexivity].

    rewrite mult_plus_distr_l.
    replace (n * (3 * fl_log n)) with ((n * 3) * fl_log n);
      [|rewrite mult_assoc;reflexivity].
    replace (3*n) with (n*3); [|apply mult_comm].
    replace (5*n) with (n*5); [|apply mult_comm].
    reflexivity.
  Qed.
    
  Lemma man_time'_nlogn:
    forall n,
      man_time' n <= 8 * n * fl_log n + 1.
  Proof.
    intros n.

    apply (le_trans (man_time' n)
                    (n * (3 * fl_log n + 5) + 1)
                    (8 * n * fl_log n + 1)); try (apply man_time'_nlogn_helper).

    induction n as [|n].
    simpl; omega.

    unfold man_time'; fold man_time'.

    apply (le_trans (man_time' n + 3 * fl_log n + 5)
                    ((n * (3 * fl_log n + 5) + 1) + 3 * fl_log n + 5)
                    (S n * (3 * fl_log (S n) + 5) + 1)).
    repeat (apply le_plus_left).
    assumption.

    replace (S n * (3 * fl_log (S n) + 5))
    with (n * (3 * fl_log (S n) + 5) + (3 * fl_log (S n) + 5)).
    
    assert (n * (3 * fl_log n + 5) <= n * (3 * fl_log (S n) + 5)).
    apply le_mult_right.
    apply le_plus_left.
    apply le_mult_right.
    apply fl_log_monotone.

    assert (3 * fl_log n + 5 <= 3 * fl_log (S n) + 5).
    apply le_plus_left.
    apply le_mult_right.
    apply fl_log_monotone.
    omega.
    
    unfold mult; fold mult; omega.
Qed.

End make_array_naive.
