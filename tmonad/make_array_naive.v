Require Import Braun.tmonad.monad.
Require Import Braun.tmonad.insert.

Require Import Braun.logical.sequence.

Require Import Braun.common.braun.
Require Import Braun.common.array.
Require Import Braun.common.util.
Require Import Braun.common.log Braun.common.le_util.
Require Import Arith Arith.Even Arith.Div2 Omega.

Fixpoint man_time' n : nat :=
  match n with
    | 0 => 3
    | S n' => man_time' n' + 7 * (fl_log n') + 11
  end.

Definition make_array_naive_result (A:Set) (xs:list A) (b : @bin_tree A) c :=
  let n := length xs in
  Braun b n
  /\ c = man_time' n
  /\ SequenceR b xs.
Hint Unfold make_array_naive_result.

Load "make_array_naive_gen.v".

Next Obligation.
Proof.
  rename H into MANRxm.

  exists (7 * fl_log (length xs') + 4).
  intros xm0 Heqxm0; subst xm0.
  intros xn MANRxn.

  unfold proj1_sig.
  destruct (insert x bt) as [bt' [n IR]].
  unfold make_array_naive_result in *.
  destruct MANRxm as [Bbt [XMeqn SRBt]].

  unfold insert_result in IR.
  remember (IR (length xs') Bbt) as Q. 
  clear IR HeqQ.
  destruct Q as [Bbt' [SRinsert Neq]].

  repeat split;auto.

  subst xm.
  simpl.
  omega.
Qed.

(*

This is a start on the proof of big_oh(nlogn) for the
old version of man_time'.

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
*)