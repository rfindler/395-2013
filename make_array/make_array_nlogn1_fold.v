Require Import Braun.tmonad.monad.
Require Import Braun.insert.insert_log.
Require Import Braun.fold.fold.

Require Import Braun.logical.sequence.

Require Import Braun.common.braun.
Require Import Braun.common.array.
Require Import Braun.common.util Braun.common.big_oh.
Require Import Braun.common.log Braun.common.le_util.
Require Import Arith Arith.Even Arith.Div2 Omega.

(* Foldr version of make_array_naive *)
Section make_array_naive.
  Variable A : Set.
  
  Fixpoint man_time n : nat :=
    match n with
      | 0 => 4
      | S n' => man_time n' + insert_time n' + 14
    end.

  Definition make_array_naive_result (b : @bin_tree A) (xs : list A) (c : nat) : Prop :=
    let n := length xs in
    Braun b n
    /\ c = man_time n
    /\ SequenceR b xs.
  
  (* technically, we should count 4 more for the call to foldr, *)
  (* but that means that we cannot use make_array_naive_result  *)
  (* as the loop invariant argument to foldr so we just skip it *)
  Program Definition make_array_naive l : 
    {! b !:! @bin_tree A !<! c !>!
       make_array_naive_result b l c !} :=
    foldr make_array_naive_result
          (fun x y => x <- insert x y; +=4; <== x)
          bt_mt
          l.

  Next Obligation.
  Proof.
    clear am H2.
    rename H0 into IR.
    rename H1 into MC.

    unfold insert_result in IR.
    destruct MC as [BRy [ACCCeq SR]].
    unfold make_array_naive_result.
    remember (IR (length xs) BRy) as IRlxs.
    destruct IRlxs as [BRx0 [SRimpl EQxn]].
    simpl.
    repeat split;auto.
    omega.
  Qed.

  Next Obligation.
  Proof.
    unfold make_array_naive_result.
    repeat split; auto.
  Qed.

  Lemma man_time_helper:
    forall n,
      man_time n <= n * insert_time n + (n * 14) + 4.
    Proof.
      intros n.
      induction n as [|n].
      simpl; omega.
      unfold man_time; fold man_time.
      apply (le_trans (man_time n + insert_time n + 14)
                      ((n * insert_time n + n * 14 + 4)  + insert_time n + 14)
                      (S n * insert_time (S n) + S n * 14 + 4)); try omega.
      clear IHn.
      replace (S n * insert_time (S n)) with (n * insert_time (S n) + insert_time (S n)).

      assert (insert_time n <= insert_time (S n)) as ITLT.
      unfold insert_time.
      apply le_plus_left.
      apply le_mult_right.
      apply fl_log_monotone_Sn.

      assert (n * insert_time n <= n * insert_time (S n)) as NITLT.
      apply le_mult_right.
      assumption.

      omega.

      assert (S n = n+1) as SN;try omega.
      rewrite SN at 3; clear SN.
      rewrite mult_plus_distr_r.
      omega.
    Qed.

  Theorem man_time_nlogn : big_oh man_time (fun n => n * fl_log n).
  Proof.
    apply (big_oh_trans man_time
                        (fun n => n * fl_log n + n + 10)
                        (fun n => n * fl_log n)).
    exists 0.
    exists 20.
    intros n H; clear H.
    apply (le_trans (man_time n)
                    (n * insert_time n + (n * 14) + 4)
                    (20*(n * fl_log n + n + 10))).
    apply man_time_helper.
    unfold insert_time.
    repeat (rewrite mult_plus_distr_l).
    repeat (rewrite mult_assoc).
    replace (n * 9 * fl_log n) with (9 * n * fl_log n).
    replace (n * 6) with (6 * n); try (apply mult_comm).
    replace (n * 14) with (14 * n); try (apply mult_comm).
    replace (9 * n * fl_log n + 6 * n + 14 * n + 4)
    with (9 * n * fl_log n + 20 * n + 4); try omega.

    assert (9 * n * fl_log n <=  20 * n * fl_log n); try omega.
    apply le_mult_left.
    apply le_mult_left.
    omega.

    rewrite (mult_comm 9).
    reflexivity.

    apply (big_oh_trans (fun n => n * fl_log n + n + 10)
                        (fun n => n * fl_log n + n)
                        (fun n => n * fl_log n)).
    exists 1.
    exists 11.
    intros n L.
    destruct n; intuition.
    clear L.
    rewrite mult_plus_distr_l.

    assert ((S n * fl_log (S n)) <= 11 * (S n * fl_log (S n))); try omega.
    remember (mult_O_le (S n * fl_log (S n)) 11) as FACT.
    inversion FACT; intuition.

    apply big_oh_nlogn_plus_n__nlogn.
  Qed.

End make_array_naive.
