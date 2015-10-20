Require Import Program Div2 Omega.
Require Import Arith Arith.Even Arith.Div2 NPeano.
Require Import Coq.Program.Wf Init.Wf.
Require Import Coq.Arith.Max.
Require Import Coq.Arith.Mult.
Require Import Braun.common.util Braun.common.le_util.
Require Import Braun.common.log Braun.common.big_oh Braun.common.pow.
Require Import Braun.monad.monad Braun.arith.plus.

Include WfExtensionality.

Program Fixpoint tmult_time (n:nat) (m:nat) {measure n} :=
  match n with
    |0 => 1
    |S _ => if (even_odd_dec n)
            then (tmult_time (div2 n) m) + 1
            else
              (tmult_time (div2 n) m) +
              (plus_time_ub m (double ((div2 n)*m))) + 1
  end.


Definition tmult_result n m res (c:nat):= n*m = res /\ c <= tmult_time n m.
Hint Unfold tmult_result.
Load "mult_gen.v".


Lemma double_times : forall n m, double (n*m) = (double n) * m.
Proof.
  intros.
  unfold double.  
  rewrite mult_plus_distr_r.
  auto.
Qed.



Lemma even_tmult_time :  forall n m,
                          Even.even (S n) -> tmult_time (S n) m = tmult_time (div2 (S n)) m +1.
Proof.
  intros.
  unfold tmult_time.
  unfold tmult_time_func.
  rewrite fix_sub_eq_ext.
  fold tmult_time_func.
  simpl proj1_sig.
  unfold projT1.
  dispatch_if EW' EW'; auto.
  assert False.
  apply not_even_and_odd with (S n); auto.
  intuition.
Qed.  

Next Obligation.
Proof.
  unfold tmult_result in *.
  split.
  destruct H1.
  rewrite <- H0.
  rewrite double_times.
  assert  (double (div2 (S wildcard')) = (S wildcard')).
  apply eq_sym.
  apply even_double.
  apply H.
  rewrite H3.
  auto.
  destruct H1.
  rewrite even_tmult_time.
  rewrite plus_comm.
  assert (tmult_time (div2 (S wildcard')) m + 1 = 1 +  tmult_time (div2 (S wildcard')) m).
  rewrite plus_comm.
  auto.
  rewrite H3.
  apply plus_le_compat_l.
  apply H1. apply H.
Qed.

Lemma plus_succ : forall n, S n = n + 1.
  intros.
  rewrite plus_comm.
  auto.
Qed.


Lemma odd_tmult_time : forall n m,
                        Even.odd (S n) ->
                        tmult_time (S n) m =
                        (tmult_time (div2 (S n)) m) +
                        (plus_time_ub m (double ((div2 (S n))*m))) + 1.
Proof.
  intros.
  unfold tmult_time.
  unfold tmult_time_func.
  rewrite fix_sub_eq_ext.
  fold tmult_time_func.
  simpl proj1_sig.
  unfold projT1.
  dispatch_if EW' EW'; auto.
  assert False.
  apply not_even_and_odd with (S n); auto.
  exfalso. apply H0.
Qed.  
  
Next Obligation.
Proof.
  unfold tmult_result in *.
  split.
  unfold tplus_result in *.
  destruct H3.
  destruct H4.
  rewrite H0.
  rewrite <- H4.
  rewrite double_times.
  rewrite plus_comm.
  assert  (S wildcard' = S (double (div2 (S wildcard')))).
  apply odd_double.
  auto.
  rewrite H6 at 1.
  rewrite plus_succ.
  rewrite mult_plus_distr_r.
  rewrite mult_1_l.
  auto.
  unfold tplus_result in *.
  clear H3 H4.
  destruct H1.
  destruct H2.
  rewrite odd_tmult_time.
  rewrite <- plus_assoc.
  apply plus_le_compat.
  apply H3.
  apply plus_le_compat.
  rewrite H2.
  apply H1.
  auto.
  auto.  
Qed.

Program Fixpoint tmult_time2 (n:nat) (m:nat) {measure n} :=
  match n with
    |0 => 1
    |S _ =>
     (tmult_time2 (div2 n) m) +
     (plus_time_ub m (double ((div2 n)*m))) + 1
  end.


Lemma tmult_time2_Sn : forall n m, tmult_time2 (S n) m =
                                   (tmult_time2 (div2 (S n)) m) +
                                   (plus_time_ub m (double ((div2 (S n))*m))) + 1.
Proof.
  intros.
  unfold tmult_time2.
  unfold tmult_time2_func.
  rewrite fix_sub_eq_ext.
  fold tmult_time2_func.
  simpl proj1_sig.
  unfold projT1.
  auto.
Qed.

Lemma double_div2 : forall n, double (div2 n) <= n.
  Proof.
    intros.
    destruct (even_odd_dec n).
    rewrite <- even_double ; auto.
    rewrite odd_double ; auto.
  Qed.
    
Lemma tmult_time_1_2 : big_O2 tmult_time tmult_time2.
  Proof.
    exists 0.
    exists 1.
    intros n m _ _.
    rewrite mult_1_l.
    apply (well_founded_ind
             lt_wf
             (fun n => forall m, tmult_time n m <= tmult_time2 n m)).
    clear.
    intros n IND.
    destruct n.
    auto.
    destruct (even_odd_dec (S n)).
    intros.
    rewrite even_tmult_time ; auto.
    rewrite tmult_time2_Sn.
    apply plus_le_compat ; auto.
    apply le_plus_trans.
    apply IND.
    apply lt_div2.
    apply lt_0_Sn.
    intros.
    rewrite odd_tmult_time.
    rewrite tmult_time2_Sn.
    apply plus_le_compat ; auto. apply plus_le_compat ; auto. auto.
  Qed.
  

Lemma n_le_n2 : forall n, n <= n*n.
Proof.
  intros.
  destruct n; auto.
  rewrite <- mult_1_l at 1.
  apply mult_le_compat_r.
  omega.
Qed.


Program Fixpoint tmult_time3 (n:nat) (m:nat) {measure n} :=
  match n with
    |0 => 1
    |S _ =>
     (tmult_time3 (div2 n) m) +
     2*cl_log m + 2*cl_log (double((div2 n)*m)) + 4
  end.


Lemma tmult_time3_Sn : forall n m, tmult_time3 (S n) m =
                                   (tmult_time3 (div2 (S n)) m) +
                                   2*cl_log m + 2*cl_log (double((div2 (S n))*m)) + 4.
Proof.
  intros.
  unfold tmult_time3. unfold tmult_time3_func.
  rewrite fix_sub_eq_ext.
  fold tmult_time3_func.
  simpl proj1_sig.
  unfold projT1.
  auto.
Qed.

Lemma tmult_time_2_3 : big_O2 tmult_time2 tmult_time3.
Proof.
  exists 0.
  exists 1.
  intros n m _ _.
  rewrite mult_1_l.
  apply (well_founded_ind
           lt_wf
           (fun n => forall m, tmult_time2 n m <= tmult_time3 n m)).
  clear n m.
  intros n Ind m.
  destruct n.
  auto.
  rewrite tmult_time2_Sn.
  rewrite tmult_time3_Sn.
  rewrite <- plus_assoc.
  rewrite <- plus_assoc.
  rewrite <- plus_assoc.
  apply plus_le_compat.
  apply Ind.
  apply lt_div2.
  omega.
  eapply le_trans.
  apply plus_le_compat.
  apply plus_cin_time_log.
  apply le_refl.
  omega.
Qed.

Lemma double_div2_prod : forall n m, double((div2 n)*m) <= n*m.
Proof.
  intros.
  destruct (even_odd_dec n).
  rewrite <- even_div_product; auto.
  assert (Even.even (n*m)).
  apply even_mult_l; auto.
  rewrite <- even_double.
  apply le_refl.
  auto.
  replace n with (S (double (div2 n))) at 2.
  unfold double.
  remember (div2 n) as N.
  replace (S (N+N)) with (N+N+1);[|omega].
  repeat rewrite mult_plus_distr_r.
  remember (N*m) as L.
  omega.
  apply eq_sym.
  apply odd_double.
  auto.
Qed.
  
Program Fixpoint tmult_time4 (n:nat) (m:nat) {measure n} :=
  match n with
    |0 => 1
    |S _ =>
     (tmult_time4 (div2 n) m) +
     2*cl_log m + 2*cl_log (n*m) + 4
  end.

Lemma tmult_time4_Sn : forall n m, tmult_time4 (S n) m =
                                   (tmult_time4 (div2 (S n)) m) +
                                   2*cl_log m + 2*cl_log ((S n)*m) + 4.
Proof.
  intros.
  unfold tmult_time4. unfold tmult_time4_func.
  rewrite fix_sub_eq_ext.
  fold tmult_time4_func.
  simpl proj1_sig.
  unfold projT1.
  auto.
Qed.

Lemma tmult_time_3_4 : big_O2 tmult_time3 tmult_time4.
Proof.  
exists 0.
exists 1.
intros.
rewrite mult_1_l.
apply (well_founded_ind
           lt_wf
           (fun n => forall m, tmult_time3 n m <= tmult_time4 n m)).
clear.
intros.
destruct x.
auto.
rewrite tmult_time3_Sn.
rewrite tmult_time4_Sn.
apply plus_le_compat; auto.
repeat rewrite <- plus_assoc.
apply plus_le_compat.
auto.
apply plus_le_compat;auto.
apply mult_le_compat; auto.
apply cl_log_monotone.
apply double_div2_prod.
Qed.

Program Fixpoint tmult_time5 (n:nat) (m:nat) {measure n} :=
  match n with
    |0 => 1
    |S _ =>
     (tmult_time5 (div2 n) m) +
     2*cl_log m + 4*cl_log n + 4*cl_log m +4
  end.

Lemma tmult_time5_Sn : forall n m, tmult_time5 (S n) m =
                                   (tmult_time5 (div2 (S n)) m) +
                                   2*cl_log m + 4*cl_log (S n) + 4*cl_log m +4.
Proof.
  intros.
  unfold tmult_time5. unfold tmult_time5_func.
  rewrite fix_sub_eq_ext.
  fold tmult_time5_func.
  simpl proj1_sig.
  unfold projT1.
  auto.
Qed.

Lemma tmult_time_4_5 : big_O2 tmult_time4 tmult_time5.
Proof.  
exists 0.
exists 1.
intros.
rewrite mult_1_l.
apply (well_founded_ind
           lt_wf
           (fun n => forall m, tmult_time4 n m <= tmult_time5 n m)).
clear.
intros.
destruct x.
auto.
rewrite tmult_time4_Sn.
rewrite tmult_time5_Sn.
apply plus_le_compat; auto.
repeat rewrite <- plus_assoc.
apply plus_le_compat.
auto.
apply plus_le_compat.
auto.
eapply le_trans.
apply mult_le_compat_l.
apply cl_log_product.
omega.
Qed.

Program Fixpoint tmult_time6 (n:nat) (m:nat) {measure n} :=
  match n with
    |0 => 1
    |S _ =>
     (tmult_time6 (div2 n) m) +
     8*cl_log m + 8*cl_log n
  end.

Lemma tmult_time6_Sn : forall n m, tmult_time6 (S n) m =
                                   (tmult_time6 (div2 (S n)) m) +
                                   8*cl_log m + 8*cl_log (S n).
Proof.
  intros.
  unfold tmult_time6. unfold tmult_time6_func.
  rewrite fix_sub_eq_ext.
  fold tmult_time6_func.
  simpl proj1_sig.
  unfold projT1.
  auto.
Qed.

Lemma tmult_time_5_6 : big_O2 tmult_time5 tmult_time6.
Proof.  
exists 0.
exists 1.
intros.
rewrite mult_1_l.
apply (well_founded_ind
           lt_wf
           (fun n => forall m, tmult_time5 n m <= tmult_time6 n m)).
clear.
intros.
destruct x.
auto.
rewrite tmult_time5_Sn.
rewrite tmult_time6_Sn.
repeat rewrite <- plus_assoc.
apply plus_le_compat.
auto.
replace (2 * cl_log m + (4 * cl_log (S x) + (4 * cl_log m + 4)))
        with ((6 * cl_log m + 4 * cl_log (S x)) + 4);[|omega].
rewrite <- plus_assoc.
apply plus_le_compat.
omega.
replace (8 * cl_log (S x)) with (4 * cl_log (S x) + 4 * cl_log (S x));[|omega].
apply plus_le_compat; auto.
apply (le_trans (4*cl_log 1) (4*cl_log (S x)));auto.
apply mult_le_compat;auto.
apply cl_log_monotone.
omega.
Qed.
  
Theorem log_prod_big_oh :
  forall (k:nat) (f g : nat -> nat),
    monotone g ->
    f 0 = k /\ (forall n, f (S n) = f (div2 (S n)) + g (S n)) ->
    (exists m, 1 <= g m) ->
    big_oh f (fun n => (cl_log n) * (g n)).
Proof.
  intros.
  destruct H0.
  destruct H1.
  exists (max x 1).
  exists (max (k+1) 2).
  intros.
  eapply le_trans.
  apply log_prod_time.
  apply H.
  split.
  apply H0.
  apply H2.
  replace (k+1) with (S k);[|omega].
  replace 2 with (S 1);[|omega].
  rewrite <- succ_max_distr.
  replace (S (max k 1)) with (1 + (max k 1));[|omega].
  rewrite mult_plus_distr_r.
  rewrite mult_1_l.
  apply plus_le_compat; auto.
  assert (1 <= n).
  eapply le_trans.
  apply le_max_r.
  apply H3.
  eapply le_trans.
  assert (k <= k*((cl_log 1)*(g x))).
  unfold_sub cl_log (cl_log 1).
  rewrite cl_log_zero.
  rewrite mult_1_l.
  replace k with (k*1) at 1; try omega.
  apply mult_le_compat; auto.
  apply H5.
  apply mult_le_compat.
  apply le_max_l.
  apply mult_le_compat.
  apply cl_log_monotone; auto.
  apply H.
  apply max_lub_l with 1. auto.
Qed.


Theorem log_prod_big_O2 :
  forall (k:nat) (f g : nat -> nat -> nat),
    (forall m, monotone (fun n => g n m)) ->
    (forall m, f 0 m = k) /\ (forall n m, f (S n) m = f (div2 (S n)) m + g (S n) m) ->
    (exists l, forall m, 1 <= g l m) ->
    big_O2 f (fun n m => (cl_log n) * (g n m)).
Proof.
  intros.
  destruct H0.
  destruct H1.
  exists (max x 1).
  exists (max (k+1) 2).
  intros.
  eapply le_trans.
  apply log_prod_time2.
  apply H.
  split.
  apply H0.
  apply H2.
  replace (k+1) with (S k);[|omega].
  rewrite <- succ_max_distr.
  replace (S (max k 1)) with (1 + (max k 1));[|omega].
  rewrite mult_plus_distr_r.
  rewrite mult_1_l.
  apply plus_le_compat; auto.
  assert (1 <= n).
  eapply le_trans.
  apply le_max_r.
  apply H3.
  eapply le_trans.
  assert (k <= k*((cl_log 1)*(g x m))).
  unfold_sub cl_log (cl_log 1).
  rewrite cl_log_zero.
  rewrite mult_1_l.
  replace k with (k*1) at 1; try omega.
  apply mult_le_compat; auto.
  apply H6.
  apply mult_le_compat.
  apply le_max_l.
  apply mult_le_compat.
  apply cl_log_monotone; auto.
  apply H.
  apply max_lub_l with 1. auto.
Qed.
  

Theorem tmult_time_6_log_prod8 :
  big_O2 tmult_time6 (fun n m => (cl_log n) * (8*cl_log m + 8*cl_log n)).
Proof.
  intros.
  eapply log_prod_big_O2.
  unfold monotone.
  intros.
  apply plus_le_compat;auto;apply mult_le_compat;auto;apply cl_log_monotone;auto.
  split.
  compute.
  reflexivity.
  intros.
  rewrite plus_assoc.
  apply tmult_time6_Sn.
  exists 1.
  unfold_sub cl_log (cl_log 1).
  rewrite cl_log_zero.
  intros.
  omega.
Qed.

Theorem tmult_time_6_log_prod :
  big_O2 tmult_time6 (fun n m=> (cl_log n) * (cl_log m + cl_log n)).
Proof.
  intros.
  eapply big_O2_trans.
  apply tmult_time_6_log_prod8.
  apply big_O2_mult.
  exists 0.
  exists 8.
  intros.
  omega.
Qed.

Theorem tmult_time_is_log_prods :
  big_O2 tmult_time (fun n m => (cl_log n) * (cl_log m + cl_log n)).
Proof.
  intros.
  eapply big_O2_trans.
  apply tmult_time_1_2.
  eapply big_O2_trans.
  apply tmult_time_2_3.
  eapply big_O2_trans.
  apply tmult_time_3_4.
  eapply big_O2_trans.
  apply tmult_time_4_5.
  eapply big_O2_trans.
  apply tmult_time_5_6.
  apply tmult_time_6_log_prod.
Qed.