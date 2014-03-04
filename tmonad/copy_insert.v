Require Import Braun.tmonad.monad Braun.logical.index Braun.tmonad.insert.
Require Import Braun.common.braun Braun.common.util Braun.common.big_oh.
Require Import Braun.common.log.
Require Import Braun.logical.list_util Braun.logical.sequence.
Require Import Arith Arith.Even Arith.Div2 Omega.
Require Import Program.Wf Init.Wf.

Include WfExtensionality.

Program Fixpoint copy_insert_time (n:nat) {measure n} :=
  match n with
    | 0 => 3
    | S n' => if (even_odd_dec n')
              then 13 + copy_insert_time (div2 n')
              else 16 + copy_insert_time (div2 n') + insert_time (div2 n')
  end.

Definition copy_insert_result (A:Set) (x:A) (n:nat) (b:@bin_tree A) (c:nat):=
  Braun b n /\ 
  SequenceR b (mk_list x n) /\
  c = copy_insert_time (n).

Load "copy_insert_gen.v".

Next Obligation.
  unfold copy_insert_result.
  repeat constructor; auto.
Qed.

Lemma copy_insert_time_even : 
  forall n',
    even n' ->
    copy_insert_time (S n') = copy_insert_time (div2 n') + 13.
  intros n EVEN.
  unfold_sub copy_insert_time (copy_insert_time (S n)).
  destruct (even_odd_dec n).
  fold_sub copy_insert_time.
  omega.
  assert False.
  apply (not_even_and_odd n); auto.
  intuition.
Qed.

Next Obligation.
  clear copy_insert.
  clear am H2.
  rename H1 into CIR.
  rename H into EVENNPRIME.

  inversion CIR as [BRAUNT [HIR TIME]].
  clear CIR.

  unfold copy_insert_result.
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
  rewrite copy_insert_time_even; auto; omega.
Qed. 

Lemma copy_insert_time_odd : 
  forall n',
    odd n' ->
    copy_insert_time (S n') =
    copy_insert_time (div2 n') + (insert_time (div2 n') + 16).
  intros n EVEN.
  unfold_sub copy_insert_time (copy_insert_time (S n)).
  destruct (even_odd_dec n).
  assert False.
  apply (not_even_and_odd n); auto.
  intuition.
  fold_sub copy_insert_time.
  omega.
Qed.  

Next Obligation.
  clear am0 H3.
  clear am H4.
  clear copy_insert.
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
  rewrite copy_insert_time_odd; auto; try omega.
Qed.

Theorem copy_insert_log_sq : big_oh copy_insert_time (fun n => fl_log n * fl_log n).
admit.
Qed.
