Require Import Braun.monad.monad Braun.common.log.
Require Import Braun.common.util Braun.common.big_oh Braun.common.le_util.
Require Import Arith Arith.Even Arith.Div2.
Require Import Coq.Program.Wf Arith.Even Arith.Div2 Arith Init.Wf.

Include WfExtensionality.

Program Fixpoint sub1_time (n:nat) {measure n} :=
  match n with
    | 0 => 3
    | S _ => if (even_odd_dec n)
             then (sub1_time (div2 n)) + 12
             else 8
  end.

Definition sub1_result (n:nat) (res:nat) (c:nat) := 
  n-1 = res /\ c = sub1_time n.
Hint Unfold sub1_result.

Load "sub1_gen.v".

Next Obligation.
  clear H2 am.
  rename H into EW.
  rename H1 into SR.

  destruct SR; subst sd2 an.

  split.

  rewrite (even_double (S wildcard')) at 1; auto.
  unfold double.
  remember (div2 (S wildcard')) as x.
  destruct x; try omega.

  destruct wildcard'.
  inversion EW.
  inversion H0.
  simpl in Heqx.
  inversion Heqx.

  unfold_sub sub1_time (sub1_time (S wildcard')).
  fold_sub sub1_time.
  dispatch_if EW' EW''; intuition.
  assert False; intuition.
  apply (not_even_and_odd (S wildcard')); auto.
Qed.

Next Obligation.
  split;auto.
  unfold_sub sub1_time (sub1_time (S wildcard')).
  fold_sub sub1_time.
  dispatch_if EW EW'; intuition.
  assert False; intuition.
  apply (not_even_and_odd (S wildcard')); auto.
Qed.


Program Fixpoint sub1_time2 (n:nat) {measure n} :=
  match n with
    | 0 => 0
    | S _ => if (even_odd_dec n)
             then (sub1_time2 (div2 n)) + 1
             else 1
  end.

Lemma sub1_time12 : big_oh sub1_time sub1_time2.
  exists 1.
  exists 50.
  intros n LE.
  destruct n; intuition.
  clear LE.
  apply (well_founded_induction
           lt_wf
           (fun n => sub1_time (S n) <= 50 * sub1_time2 (S n))).
  clear n; intros n IND.
  unfold_sub sub1_time (sub1_time (S n)); fold_sub sub1_time.
  unfold_sub sub1_time2 (sub1_time2 (S n)); fold sub1_time2.
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

Program Fixpoint sub1_time3 (n:nat) {measure n} :=
  match n with
    | 0 => 0
    | S _ => (sub1_time3 (div2 n)) + 1
  end.

Lemma sub1_time23 : big_oh sub1_time2 sub1_time3.
Proof.
exists 0.
exists 1.
intros.
rewrite mult_1_l.
apply (well_founded_ind
         lt_wf
         (fun n => sub1_time2 n <= sub1_time3 n)).
clear.
intros n IH.
destruct n.
compute.
auto.
assert (forall n, sub1_time3 (S n) = (sub1_time3 (div2 (S n)) + 1)).
intros.
unfold_sub sub1_time3 (sub1_time3 (S n0)).
simpl.
auto.
rewrite H.
unfold_sub sub1_time2 (sub1_time2 (S n)).
fold_sub sub1_time2.
dispatch_if EW EW.
simpl.
destruct n.
simpl.
auto.
apply plus_le_compat;auto.
apply IH.
inversion EW.
inversion H1.
rewrite even_div2.
apply lt_n_S.
repeat auto.
auto.
omega.
Qed.

Lemma sub1_time3_is_cl_log : forall n, sub1_time3 n = cl_log n.
Proof.
intros.
apply (well_founded_ind
         lt_wf
         (fun n => sub1_time3 n = cl_log n)).
intros.
destruct x.
auto.
unfold_sub sub1_time3 (sub1_time3 (S x)).
unfold_sub cl_log (cl_log (S x)).
destruct x.
auto.
replace ( S (cl_log (S (div2 x)))) with  (cl_log (S (div2 x)) + 1);[|omega].
rewrite plus_comm at 1.
replace (cl_log (S (div2 x)) + 1) with (1+cl_log (S (div2 x)));[|omega].
assert ( sub1_time3 (S (div2 x)) =  cl_log (S (div2 x))).
apply H.
apply lt_n_S.
auto.
rewrite H0.
auto.
Qed.

Lemma sub1_time3_O_cl_log : big_oh sub1_time3 cl_log.
  Proof.
exists 0.
exists 1.
intros.
rewrite mult_1_l.
rewrite sub1_time3_is_cl_log.
auto.
Qed.

Theorem sub1_log : big_oh sub1_time fl_log.
Proof.
  eapply big_oh_trans.
  apply sub1_time12.
  eapply big_oh_trans.
  apply sub1_time23.
  eapply big_oh_trans.
  apply sub1_time3_O_cl_log.
  apply cl_log_O_fl_log.
Qed.

