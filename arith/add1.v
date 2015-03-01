Require Import Braun.monad.monad Braun.common.log.
Require Import Braun.common.util Braun.common.big_oh Braun.common.le_util.
Require Import Arith Arith.Even Arith.Div2.
Require Import Coq.Program.Wf Arith.Even Arith.Div2 Arith Init.Wf.

Include WfExtensionality.

Program Fixpoint add1_time (n:nat) {measure n} :=
  match n with
    | 0 => 3
    | S _ => if (even_odd_dec n)
             then 8
             else (add1_time (div2 n)) + 11
  end.

Definition add1_result (n:nat) (res:nat) (c:nat) := 
  n+1 = res /\ c = add1_time n.
Hint Unfold add1_result.

Load "add1_gen.v".

Next Obligation.
  split;auto.
  unfold_sub add1_time (add1_time (S wildcard')).
  fold_sub add1_time.
  dispatch_if EW EW'; intuition.
  assert False; intuition.
  apply (not_even_and_odd (S wildcard')); auto.
Qed.

Next Obligation.
  clear H2 am add1.
  rename H into EW.
  rename H1 into SR.

  destruct SR; subst sd2 an.

  split.
  replace (div2 (S wildcard') + 1 + (div2 (S wildcard') + 1))
  with (S (div2 (S wildcard') + div2 (S wildcard')) + 1);[|omega].
  replace (div2 (S wildcard') + div2 (S wildcard'))
  with (double (div2 (S wildcard')));[|unfold double;auto].
  rewrite <- odd_double; auto.

  unfold_sub add1_time (add1_time (S wildcard')).
  fold_sub add1_time.
  dispatch_if EW' EW''; intuition.
  assert False; intuition.
  apply (not_even_and_odd (S wildcard')); auto.
Qed.

(*
Program Fixpoint add1_time2 (n:nat) {measure n} :=
  match n with
    | 0 => 0
    | S _ => if (even_odd_dec n)
             then (add1_time2 (div2 n)) + 1
             else 1
  end.

Lemma add1_time12 : big_oh add1_time add1_time2.
  exists 1.
  exists 50.
  intros n LE.
  destruct n; intuition.
  clear LE.
  apply (well_founded_induction
           lt_wf
           (fun n => add1_time (S n) <= 50 * add1_time2 (S n))).
  clear n; intros n IND.
  unfold_sub add1_time (add1_time (S n)); fold_sub add1_time.
  unfold_sub add1_time2 (add1_time2 (S n)); fold add1_time2.
  dispatch_if COND1 COND1'; try omega.
  destruct n.
  simpl; omega.
  rewrite mult_plus_distr_l.
  replace (50*1) with (38+12); [|omega].
  rewrite plus_assoc.
  apply le_plus_left.
  apply le_add_right.
  apply IND; auto.
Qed.

*)

Theorem add1_log : big_oh add1_time fl_log.
Admitted.
