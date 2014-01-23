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
    | S n' => man_time' n' + 9 * (fl_log n') + 14
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
  clear H2 H3.
  rename H1 into MANRxs'.
  rename H0 into IRbt.

  destruct MANRxs' as [BTbt [EQxm SRbt]].

  unfold insert_result in *.
  remember (IRbt (length xs') BTbt) as ONE; clear HeqONE IRbt.
  destruct ONE as [BRir [SRimpl EQxm0]].

  repeat split; auto.
  subst.
  simpl.
  omega.
Qed.

Lemma man_time'_nlogn_helper : 
  forall n, 
    n * (9 * (fl_log n) + 14) + 3 <=
    23 * n * fl_log n + 3.
  Proof.
    intros n.
    apply le_plus_left.
    replace (n * (9 * fl_log n + 14)) with (9 * n * fl_log n + 14 * n).
    replace (23*n*fl_log n) with (9 * n * fl_log n + 14 * n * fl_log n).
    apply le_plus_right.
    replace (14 * n * fl_log n) with (14 * (n * fl_log n)).
    apply le_mult_right.

    destruct n; auto.

    assert (S n = S n * 1) as H;[omega|rewrite H at 1; clear H].
    apply le_mult_right.
    apply one_le_fl_log_S.

    apply mult_assoc.

    replace 23 with (9+14);[|omega].
    rewrite <- mult_plus_distr_r.
    replace ((9+14)*n) with (9*n+14*n);
      [reflexivity|rewrite mult_plus_distr_r;reflexivity].

    rewrite mult_plus_distr_l.
    replace (n * (9 * fl_log n)) with ((n * 9) * fl_log n);
      [|rewrite mult_assoc;reflexivity].
    replace (9*n) with (n*9); [|apply mult_comm].
    replace (14*n) with (n*14); [|apply mult_comm].
    reflexivity.
  Qed.

(*
  Lemma helper :
    forall n,
      n >= 1 ->
      23 * n * (fl_log n) + 3 <=  230 * n * (fl_log n).
    intros n Ngt1.
    destruct n.
    intuition.
    clear Ngt1.
    induction n.
    simpl.
    omega.
    (* inductive case goes here. but there has to be a better way *)
*)

  Lemma man_time'_nlogn:
    forall n,
      man_time' n <=  23 * n * (fl_log n) + 3.
  Proof.
    intros n.
    apply (le_trans (man_time' n)
                    (n * (9 * (fl_log n) + 14) + 3)
                    (23 * n * fl_log n + 3)); try (apply man_time'_nlogn_helper).

    induction n as [|n].
    simpl; omega.

    unfold man_time'; fold man_time'.

    apply (le_trans (man_time' n + 9 * fl_log n + 14)
                    ((n * (9 * fl_log n + 14) + 3) + 9 * fl_log n + 14)
                    (S n * (9 * fl_log (S n) + 14) + 3)).

    repeat (apply le_plus_left).
    assumption.

    replace (S n * (9 * fl_log (S n) + 14))
    with (n * (9 * fl_log (S n) + 14) + (9 * fl_log (S n) + 14)).
    
    assert (n * (9 * fl_log n + 14) <= n * (9 * fl_log (S n) + 14)).
    apply le_mult_right.
    apply le_plus_left.
    apply le_mult_right.
    apply fl_log_monotone.

    assert (9 * fl_log n + 14 <= 9 * fl_log (S n) + 14).
    apply le_plus_left.
    apply le_mult_right.
    apply fl_log_monotone.
    omega.
    
    unfold mult; fold mult; omega.
Qed.
