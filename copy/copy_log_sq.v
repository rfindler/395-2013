Require Import Braun.tmonad.monad Braun.common.index Braun.insert.insert_log.
Require Import Braun.common.braun Braun.common.util Braun.common.big_oh.
Require Import Braun.common.log Braun.common.le_util.
Require Import Braun.common.list_util Braun.common.sequence.
Require Import Arith Arith.Even Arith.Div2 Omega.
Require Import Program.Wf Init.Wf.

Include WfExtensionality.

(* START: copy_insert_time *)
Program Fixpoint copy_log_sq_time (n:nat) 
        {measure n} :=
  match n with
    | 0 => 3
    | S n' =>
      if (even_odd_dec n')
      then 13 + copy_log_sq_time (div2 n')
      else 16 + 
           copy_log_sq_time (div2 n') +
           insert_time (div2 n')
  end.
(* STOP: copy_insert_time *)

(* START: copy_insert_result *)
Definition copy_log_sq_result
           (A:Set) (x:A) (n:nat)
           (b:@bin_tree A) (c:nat):=
  Braun b n /\ 
  SequenceR b (mk_list x n) /\
  c = copy_log_sq_time (n).
(* STOP: copy_insert_result *)

(* this correctness condition is different than the other  *)
(* copy algorithm's correctness conditions, but it implies *)
(* the other; see sequence_constant_list_index_is_constant *)

Load "copy_log_sq_gen.v".

Next Obligation.
Proof.
  unfold copy_log_sq_result.
  repeat constructor; auto.
Qed.

Lemma copy_log_sq_time_even : 
  forall n',
    even n' ->
    copy_log_sq_time (S n') = copy_log_sq_time (div2 n') + 13.
Proof.
  intros n EVEN.
  unfold_sub copy_log_sq_time (copy_log_sq_time (S n)).
  destruct (even_odd_dec n).
  fold_sub copy_log_sq_time.
  omega.
  assert False.
  apply (not_even_and_odd n); auto.
  intuition.
Qed.

Next Obligation.
Proof.
  clear copy_log_sq.
  clear am H2.
  rename H1 into CIR.
  rename H into EVENNPRIME.

  inversion CIR as [BRAUNT [HIR TIME]].
  clear CIR.

  unfold copy_log_sq_result.
  repeat split.

  (* braun *)
  assert (S n' = div2 n' + div2 n' + 1) as QQ.
  replace (div2 n' + div2 n') with n'; try omega.
  apply even_double; auto.
  rewrite QQ; clear QQ.
  constructor; auto; try omega.

  (* correct *)
  simpl.
  replace (mk_list x n') with (interleave (mk_list x (div2 n')) (mk_list x (div2 n'))).
  apply SR_node; auto.
  replace (mk_list x n') with (mk_list x (div2 n'+div2 n')).
  apply interleave_mk_list_same_size.
  rewrite -> (even_double n') at 3; auto.

  (* running time *)
  rewrite copy_log_sq_time_even; auto; omega.
Qed. 

Lemma copy_log_sq_time_odd : 
  forall n',
    odd n' ->
    copy_log_sq_time (S n') =
    copy_log_sq_time (div2 n') + (insert_time (div2 n') + 16).
Proof.
  intros n EVEN.
  unfold_sub copy_log_sq_time (copy_log_sq_time (S n)).
  destruct (even_odd_dec n).
  assert False.
  apply (not_even_and_odd n); auto.
  intuition.
  fold_sub copy_log_sq_time.
  omega.
Qed.  

Next Obligation.
Proof.
  clear am0 H3.
  clear am H4.
  clear copy_log_sq.
  rename H1 into IR.
  rename H2 into CIR.

  destruct CIR as [BT [INDEX TIME]].

  unfold insert_result in IR.
  remember (IR (div2 n') BT) as IRN.
  clear IR HeqIRN.
  destruct IRN as [BRAUNS [SEQ INSERT_TIME]].

  repeat split.

  (* braun *)
  replace (S n') with (S (div2 n') + (div2 n') + 1).
  constructor; auto; try omega.
  replace (S (div2 n') + div2 n') with (S ((div2 n')+(div2 n'))); try omega.
  replace (div2 n' + div2 n') with (double (div2 n')); auto.
  rewrite <- (odd_double n'); auto; try omega.

  (* correctness *)
  remember INDEX as INDEXS. clear HeqINDEXS.
  apply SEQ in INDEXS.
  clear SEQ.
  simpl.
  replace (mk_list x n') with (interleave (x :: mk_list x (div2 n'))
                                          (mk_list x (div2 n'))).
  constructor; auto.
  replace (mk_list x n') with (mk_list x (div2 n' + div2 n' + 1)).
  rewrite <- interleave_case2.
  replace (div2 n'+div2 n'+1) with (S (div2 n'+div2 n')); try omega.
  simpl.
  rewrite interleave_mk_list_same_size.
  reflexivity.
  rewrite (odd_double n') at 3;auto.
  unfold double.
  replace  (div2 n' + div2 n' + 1) with (S (div2 n' + div2 n')); try omega.
  reflexivity.

  (* running time *)
  rewrite copy_log_sq_time_odd; auto; try omega.
Qed.

Program Fixpoint copy_log_sq_time2 (n:nat) {measure n} :=
  match n with
    | 0 => 3
    | S n' => 16 + copy_log_sq_time2 (div2 n') + insert_time (div2 n')
  end.

Lemma copy_log_sq_time12 : big_oh copy_log_sq_time copy_log_sq_time2.
Proof.
  exists 0.
  exists 1.
  intros n LT. clear LT.
  unfold mult.
  rewrite plus_0_r.
  apply (well_founded_induction 
           lt_wf 
           (fun n => copy_log_sq_time n <= copy_log_sq_time2 n)).
  clear n.
  intros n IND.
  destruct n.
  unfold_sub copy_log_sq_time (copy_log_sq_time 0).
  unfold_sub copy_log_sq_time2 (copy_log_sq_time2 0).
  omega.

  unfold_sub copy_log_sq_time2 (copy_log_sq_time2 (S n)).
  remember (even_or_odd n) as EO.
  clear HeqEO.
  destruct EO as [EVEN|ODD].

  rewrite copy_log_sq_time_even; auto.
  remember (IND (div2 n) (lt_div2' n)).
  omega.

  rewrite copy_log_sq_time_odd; auto.
  remember (IND (div2 n) (lt_div2' n)).
  omega.
Qed.

Program Fixpoint copy_log_sq_time3 (n:nat) {measure n} :=
  match n with
    | 0 => 1
    | S n' => copy_log_sq_time3 (div2 n') + insert_time (div2 n')
  end.

Lemma copy_log_sq_time23 : big_oh copy_log_sq_time2 copy_log_sq_time3.
Proof.
  exists 1.
  exists 16.
  intros n LT.
  destruct n; intuition.
  clear LT.
  unfold_sub copy_log_sq_time2 (copy_log_sq_time2 (S n)).
  unfold_sub copy_log_sq_time3 (copy_log_sq_time3 (S n)).
  rewrite mult_plus_distr_l.
  replace (16*insert_time (div2 n)) with ((15+1)*insert_time (div2 n)); try omega.
  rewrite mult_plus_distr_r.
  rewrite plus_assoc.
  replace (1*insert_time (div2 n)) with (insert_time (div2 n)); try omega.
  apply le_plus_left.
  remember (div2 n) as m; clear Heqm n; rename m into n.
  apply (le_trans (16 + copy_log_sq_time2 n)
                  (16 * copy_log_sq_time3 n + 15 * 1)
                  (16 * copy_log_sq_time3 n + 15 * insert_time n)).
  replace (15*1) with 15; try omega.
  apply (well_founded_induction 
           lt_wf 
           (fun n => 16 + copy_log_sq_time2 n <=
                     16 * copy_log_sq_time3 n + 15)).
  clear n. intros n IND.
  destruct n.
  unfold_sub copy_log_sq_time2 (copy_log_sq_time2 0).
  unfold_sub copy_log_sq_time3 (copy_log_sq_time3 0).
  omega.
  unfold_sub copy_log_sq_time2 (copy_log_sq_time2 (S n)).
  unfold_sub copy_log_sq_time3 (copy_log_sq_time3 (S n)).
  apply (le_trans (16 + (16 + copy_log_sq_time2 (div2 n) + insert_time (div2 n)))
                  (16 + (16 * copy_log_sq_time3 (div2 n) + 15 + insert_time (div2 n)))
                  (16 * (copy_log_sq_time3 (div2 n) + insert_time (div2 n)) + 15)).
  apply le_plus_right.
  apply le_plus_left.
  apply (IND (div2 n)); auto.
  rewrite mult_plus_distr_l.
  rewrite plus_comm.
  repeat (rewrite <- plus_assoc).
  apply le_plus_right.
  rewrite plus_comm.
  apply le_plus_left.
  clear IND.
  remember (div2 n) as m; clear Heqm n; rename m into n.
  unfold insert_time.
  omega.

  unfold insert_time.
  omega.
Qed.  

Definition copy_log_sq_time4 (n:nat) := fl_log n * insert_time n.

Lemma random_fl_log_le : forall n,
                           fl_log (S (div2 n)) <= fl_log (S (S (S n))).
Proof.
  intros.
  apply fl_log_monotone.
  apply (well_founded_induction 
           lt_wf
           (fun n => S (div2 n) <= S (S (S n)))).
  clear n; intros n IND; destruct n.
  simpl.
  omega.
  destruct n.
  simpl.
  omega.
  simpl.
  replace (S (S (div2 n))) with (1+(S (div2 n))); try omega.
  replace (S (S (S (S (S n))))) with (1+(S (S (S (S n))))); try omega.
  apply le_plus_right.
  apply (le_trans (S (div2 n))
                  (S (S (S n)))
                  (S (S (S (S n))))).
  apply IND.
  omega.
  omega.
Qed.

Lemma copy_log_sq_time34 : big_oh copy_log_sq_time3 copy_log_sq_time4.
Proof.
  exists 1.
  exists 1.
  intros n LT.  
  destruct n; intuition.
  clear LT.
  unfold mult.
  rewrite plus_0_r.
  unfold copy_log_sq_time4.
  unfold_sub copy_log_sq_time3 (copy_log_sq_time3 (S n)).
  apply (well_founded_induction 
           lt_wf 
           (fun n => copy_log_sq_time3 (div2 n) + insert_time (div2 n) <=
                     fl_log (S n) * insert_time (S n))).
  clear n; intros n IND.
  destruct n.
  unfold insert_time.
  simpl.
  omega.
  destruct n.
  unfold insert_time.
  simpl.
  omega.
  unfold div2.
  fold div2.
  unfold_sub copy_log_sq_time3 (copy_log_sq_time3 (S (div2 n))).
  apply (le_trans (copy_log_sq_time3 (div2 (div2 n)) + 
                   insert_time (div2 (div2 n)) +
                   insert_time (S (div2 n)))
                  (fl_log (S (div2 n)) * insert_time (S (div2 n))
                   + insert_time (S (div2 n)))
                  (fl_log (S (S (S n))) * insert_time (S (S (S n))))).
  apply le_plus_left.
  apply IND.
  apply (lt_trans (div2 n) (S n) (S (S n))); auto.
  replace (fl_log (S (S (S n)))) with (S (fl_log (div2 (S (S n))))); 
    [|rewrite fl_log_div2'; omega].
  unfold div2; fold div2.
  replace (S (fl_log (S (div2 n)))) with ((fl_log (S (div2 n))) + 1); [|omega].
  rewrite mult_plus_distr_r.
  replace (1*insert_time (S (S (S n)))) with (insert_time (S (S (S n)))); try omega.
  unfold insert_time.

  apply (le_trans (fl_log (S (div2 n)) * (9 * fl_log (S (div2 n)) + 6) +
                   (9 * fl_log (S (div2 n)) + 6))
                  (fl_log (S (div2 n)) * (9 * fl_log (S (div2 n)) + 6) +
                   (9 * fl_log (S (S (S n))) + 6))
                  (fl_log (S (div2 n)) * (9 * fl_log (S (S (S n))) + 6) +
                   (9 * fl_log (S (S (S n))) + 6))).
  apply le_plus_right.
  apply le_plus_left.
  apply le_mult_right.
  apply random_fl_log_le.

  apply le_plus_left.
  apply le_mult_right.
  apply le_plus_left.
  apply le_mult_right.
  apply random_fl_log_le.
Qed.

Theorem copy_log_sq_log_sq : big_oh copy_log_sq_time
                                    (fun n => fl_log n * fl_log n).
Proof.
  apply (big_oh_trans copy_log_sq_time
                      copy_log_sq_time4
                      (fun n => fl_log n * fl_log n)).
  apply (big_oh_trans copy_log_sq_time
                      copy_log_sq_time3
                      copy_log_sq_time4).
  apply (big_oh_trans copy_log_sq_time
                      copy_log_sq_time2
                      copy_log_sq_time3).
  apply copy_log_sq_time12.
  apply copy_log_sq_time23.
  apply copy_log_sq_time34.
  unfold copy_log_sq_time4.
  apply big_oh_mult.
  apply insert_time_log.
Qed.
