Require Import Program Div2 Omega.
Require Import Arith Arith.Even Arith.Div2 NPeano.
Require Import Coq.Program.Wf Init.Wf.
Require Import Coq.Arith.Max.
Require Import Braun.common.util Braun.common.le_util.
Require Import Braun.common.log Braun.common.big_oh Braun.common.pow.
Require Import Braun.monad.monad Braun.arith.add1.
Include WfExtensionality.


Program Fixpoint plus_cin_time_lb (n:nat) (m:nat) {measure (m + n)} : nat :=
  match n with
    | 0 => 1
    | S n' => 
      match m with
        | 0 => 1
        | S m' => plus_cin_time_lb (div2 n) (div2 m) + 1
      end
  end.

Next Obligation.
Proof.
  apply plus_lt_compat;auto.
Defined.

Program Fixpoint plus_cin_time_ub (n:nat) (m:nat) {measure (m + n)} : nat :=
  match n with
    | 0 => 1 + add1_time m
    | S n' => 
      match m with
        | 0 => 1 + add1_time n
        | S m' => plus_cin_time_ub (div2 n) (div2 m) + 1
      end
  end.

Next Obligation.
Proof.
  apply plus_lt_compat;auto.
Defined.

Lemma plus_cin_time_lb_0n : forall n, plus_cin_time_lb 0 n = 1.
Proof.
  intros n.
  unfold plus_cin_time_lb.
  unfold plus_cin_time_lb_func.
  rewrite fix_sub_eq_ext.
  fold plus_cin_time_lb_func.
  simpl proj1_sig.
  unfold projT1.
  auto.
Qed.

Lemma plus_cin_time_lb_n0 : forall n, plus_cin_time_lb n 0 = 1.
Proof.
  intros n.
  unfold plus_cin_time_lb.
  unfold plus_cin_time_lb_func.
  rewrite fix_sub_eq_ext.
  fold plus_cin_time_lb_func.
  simpl proj1_sig.
  unfold projT1.
  destruct n; auto.
Qed.

Lemma plus_cin_time_lb_SS : forall n' m', plus_cin_time_lb (S n') (S m') = 
                                          plus_cin_time_lb (div2 (S n')) (div2 (S m')) + 1.
Proof.
  intros n' m'.
  remember (plus_cin_time_lb (div2 (S n')) (div2 (S m')) + 34) as res.
  unfold plus_cin_time_lb in res.
  unfold plus_cin_time_lb.
  unfold plus_cin_time_lb_func.
  rewrite fix_sub_eq_ext.
  fold plus_cin_time_lb_func.
  simpl proj1_sig.
  unfold projT1.
  unfold projT2.
  destruct n'; destruct m'; auto.
Qed.

Lemma plus_cin_time_ub_0n : forall n, plus_cin_time_ub 0 n = 1 + add1_time n.
Proof.
  intros n.
  unfold plus_cin_time_ub.
  unfold plus_cin_time_ub_func.
  rewrite fix_sub_eq_ext.
  fold plus_cin_time_ub_func.
  simpl proj1_sig.
  unfold projT1.
  auto.
Qed.

Lemma plus_cin_time_ub_n0 : forall n, plus_cin_time_ub n 0 = 1 + add1_time n.
Proof.
  intros n.
  unfold plus_cin_time_ub.
  unfold plus_cin_time_ub_func.
  rewrite fix_sub_eq_ext.
  fold plus_cin_time_ub_func.
  simpl proj1_sig.
  unfold projT1.
  destruct n; auto.
Qed.


Lemma plus_cin_time_ub_SS : forall n' m', plus_cin_time_ub (S n') (S m') = 
                                          plus_cin_time_ub (div2 (S n')) (div2 (S m')) + 1.
Proof.
  intros n' m'.
  remember (plus_cin_time_ub (div2 (S n')) (div2 (S m')) + 34) as res.
  unfold plus_cin_time_ub in res.
  unfold plus_cin_time_ub.
  unfold plus_cin_time_ub_func.
  rewrite fix_sub_eq_ext.
  fold plus_cin_time_ub_func.
  simpl proj1_sig.
  unfold projT1.
  unfold projT2.
  destruct n'; destruct m'; auto.
Qed.

Lemma plus_cin_time_ub_as_log :
  forall n, plus_cin_time_ub n n = 2 + cl_log n.
Proof.  
  apply (well_founded_ind
           lt_wf
           (fun n => plus_cin_time_ub n n = 2 + cl_log n)).
  intros.
  destruct x. compute. auto.
  rewrite plus_cin_time_ub_SS.
  rewrite cl_log_div2'.
  rewrite H.
  omega.
  apply lt_div2.
  omega.
Qed.
  
  
Lemma plus_cin_time_lb_symmetric:
  forall a b,
    plus_cin_time_lb a b = plus_cin_time_lb b a.
Proof.
  intros a b.
  generalize dependent b.
  apply (well_founded_ind
           lt_wf
           (fun a => forall b : nat, plus_cin_time_lb a b = plus_cin_time_lb b a)).
  clear a; intros a IND b.
  destruct a.
  rewrite plus_cin_time_lb_0n; rewrite plus_cin_time_lb_n0; auto.
  destruct b.
  rewrite plus_cin_time_lb_0n; rewrite plus_cin_time_lb_n0; auto.
  rewrite plus_cin_time_lb_SS.
  rewrite plus_cin_time_lb_SS.
  rewrite plus_comm.
  unfold plus at 1.
  rewrite plus_comm.
  unfold plus at 1.
  apply f_equal.
  apply IND; auto.
Qed.

Lemma plus_time_ub_symmetric :
  forall a b,
    plus_cin_time_ub a b = plus_cin_time_ub b a.
Proof.
  intros a b.
  generalize dependent b.
   apply (well_founded_ind
           lt_wf
           (fun a => forall b : nat, plus_cin_time_ub a b = plus_cin_time_ub b a)).
   clear a; intros a IND b.
   destruct a.
   rewrite plus_cin_time_ub_0n; rewrite plus_cin_time_ub_n0; auto.
   destruct b.
   rewrite plus_cin_time_ub_0n; rewrite plus_cin_time_ub_n0; auto.
   rewrite plus_cin_time_ub_SS.
   rewrite plus_cin_time_ub_SS.
   rewrite plus_comm.
   unfold plus at 1.
   rewrite plus_comm.
   unfold plus at 1.
   apply f_equal.
   apply IND; auto.
Qed.

Lemma plus_cin_time_lb_right_arg_grows :
  forall a b b',
    b <= b' ->
    plus_cin_time_lb a b <= plus_cin_time_lb a b'.
Proof. 
  intros a.
  apply (well_founded_ind
           lt_wf
           (fun a => 
              forall b b' : nat,
                b <= b' -> plus_cin_time_lb a b <= plus_cin_time_lb a b')).
  clear a; intros a IND b b' LT.
  destruct a.
  repeat (rewrite plus_cin_time_lb_0n); auto.
  destruct b'.
  replace b with 0;[|omega].
  repeat (rewrite plus_cin_time_lb_n0); auto.
  destruct b.
  rewrite plus_cin_time_lb_n0.
  rewrite plus_cin_time_lb_SS.
  omega.
  repeat (rewrite plus_cin_time_lb_SS).
  apply plus_le_compat; auto.
  apply IND; auto.
  apply div2_monotone; auto.
Qed.

Lemma div2_1 : forall n, 2 <= n -> 1 <= div2 n.
Proof.
  intros.
  induction n.
  intuition.
  simpl.
  destruct n.
  intuition.
  omega.
Qed.


Lemma lt_implies_le : forall n m, n < m -> n <=m.
Proof.
  intros.
  omega.
Qed.

Lemma le_1_implies_S : forall n, 1<=n -> exists k, n = S k.
Proof.
  intros.
  inversion H.
  exists 0; auto.
  exists m ; auto.
Qed.

Lemma plus_cin_time_cl_log : forall n m,
                               plus_cin_time_ub n m <= 2*cl_log n + 2 * cl_log m + 2.
Proof.
  intros.
  apply (well_founded_induction
         lt_wf
         (fun n => forall m, plus_cin_time_ub n m <= 2*cl_log n + 2*cl_log m + 2)).
  intros.
  destruct x as [| x'].
  rewrite plus_cin_time_ub_0n.
  rewrite cl_log_zero.
  simpl (2*0).
  rewrite plus_0_l.
  destruct m0 as [| m0'].
  auto.
  rewrite plus_comm.
  apply plus_le_compat; auto.
  apply cl_log_bnd_add1_time.
  omega.
  destruct m0 as [| m0'].
  rewrite plus_cin_time_ub_n0.
  rewrite cl_log_zero.
  simpl (2*0).
  rewrite plus_comm.
  rewrite plus_0_r.
  apply plus_le_compat ; auto.
  apply cl_log_bnd_add1_time.
  omega.
  rewrite plus_cin_time_ub_SS.
  apply plus_le_compat ; auto.
  eapply le_trans.
  apply H.
  apply lt_div2.
  omega.
  replace (cl_log (S m0')) with (cl_log (div2 (S m0')) +1).
  rewrite mult_plus_distr_l.
  simpl (2*1).
  rewrite plus_assoc.
  apply plus_le_compat; auto.
  apply plus_le_compat; auto.
  apply mult_le_compat; auto.
  apply cl_log_monotone.
  apply lt_implies_le.
  apply lt_div2.
  omega.
  rewrite plus_comm.
  replace (1+ cl_log (div2 (S m0'))) with (S (cl_log (div2 (S m0')))).
  rewrite cl_log_div2'; auto.
  omega.
Qed.




Definition plus_cin_result (n:nat) (m:nat) (cin:bool) (res:nat) (c:nat) :=
  n+m+(if cin then 1 else 0)=res /\ plus_cin_time_lb n m <= c <= plus_cin_time_ub n m.
Hint Unfold plus_cin_result.

Load "plus_cin_gen.v".

Next Obligation.
Proof.
  split; auto.
  rewrite plus_cin_time_lb_0n.
  rewrite plus_cin_time_ub_0n.
  omega.
Qed.

Next Obligation.
Proof.
  split; auto.
  rewrite plus_cin_time_lb_0n.
  rewrite plus_cin_time_ub_0n.
  omega.
Qed.

Next Obligation.
Proof.
  clear H1 am plus_cin.
  rename H0 into ADDONERES.
  
  destruct ADDONERES as [CORRECT TIME].
  split; [auto|].

  rewrite plus_cin_time_lb_0n.
  rewrite plus_cin_time_ub_0n.
  omega.
Qed.

Next Obligation.
Proof.
  split; auto.
  rewrite plus_cin_time_lb_0n.
  rewrite plus_cin_time_ub_0n.
  omega.
Qed.

Next Obligation.
Proof.
  clear H1 am.
  rename H0 into ADDRESULT.

  destruct ADDRESULT as [CORRECT TIME].
  
  split.

  omega.

  rewrite plus_cin_time_lb_n0.
  rewrite plus_cin_time_ub_n0.
  omega.
Qed.

Next Obligation.
Proof.
  split.

  omega.

  rewrite plus_cin_time_lb_n0.
  rewrite plus_cin_time_ub_n0.
  omega.
Qed.

Next Obligation.
Proof.
  apply plus_lt_le_compat; auto.
  assert (div2 (S n') < S n');[auto|].
  omega.
Qed.

Next Obligation.
Proof.
  clear H1 am plus_cin.
  rename H0 into PLUS_CIN_RECUR.

  destruct PLUS_CIN_RECUR as [CORRECT TIME].

  split;[clear TIME|clear CORRECT].

  subst ndiv2plusmdiv2plusX.

  remember (S n') as n.
  remember (S m') as m.
  unfold double_plus_one, double, even_oddb in *.

  (destruct (even_odd_dec n) as [NEOFACT|NEOFACT]; [remember (even_double n NEOFACT)|
                                                    remember (odd_double n NEOFACT)]);
    (destruct (even_odd_dec m) as [MEOFACT|MEOFACT]; [remember (even_double m MEOFACT)|
                                                      remember (odd_double m MEOFACT)]);
    destruct cin; unfold double in *;
    unfold xorb, negb, andb, orb in *; try omega; try intuition.

  rewrite plus_cin_time_lb_SS.
  rewrite plus_cin_time_ub_SS.
  omega.
Qed.

Next Obligation.
Proof.
  clear H1 am plus_cin.
  rename H0 into PLUS_CIN_RECUR.

  destruct PLUS_CIN_RECUR as [CORRECT TIME].

  split;[clear TIME|clear CORRECT].

  remember (S n') as n.
  remember (S m') as m.
  unfold double_plus_one, double, even_oddb in *.

  (destruct (even_odd_dec n) as [NEOFACT|NEOFACT]; [remember (even_double n NEOFACT)|
                                                    remember (odd_double n NEOFACT)]);
    (destruct (even_odd_dec m) as [MEOFACT|MEOFACT]; [remember (even_double m MEOFACT)|
                                                      remember (odd_double m MEOFACT)]);
    destruct cin; unfold double in *;
    unfold xorb, negb, andb, orb in *; try omega; try intuition.

  rewrite plus_cin_time_lb_SS.
  rewrite plus_cin_time_ub_SS.
  omega.
Qed.

Definition plus_time_lb n m := plus_cin_time_lb n m + 1.
Definition plus_time_ub n m := plus_cin_time_ub n m + 1.
Definition tplus_result n m res c :=
  res = n+m /\ plus_time_lb n m <= c <= plus_time_ub n m.

Lemma plus_cin_time_log : forall n m,
                            plus_time_ub n m <= 2*cl_log n + 2*cl_log m + 3.
Proof.
  intros.
  unfold plus_time_ub.
  eapply le_trans.
  apply plus_le_compat.
  apply plus_cin_time_cl_log.
  auto.
  rewrite <- plus_assoc.
  apply plus_le_compat.
  apply le_refl.
  apply le_refl.
  Qed.


Lemma plus_time_lb_symmetric :
  forall a b,
    plus_time_lb a b = plus_time_lb b a.
Proof.
  intros a b.
  unfold plus_time_lb.
  rewrite plus_comm.
  unfold plus at 1.
  rewrite plus_comm.
  unfold plus.
  rewrite plus_cin_time_lb_symmetric.
  auto.
Qed.

Load "plus_gen.v".

Next Obligation.
Proof.
  clear H1 am.
  rename H0 into PLUSCIN. 
  
  destruct PLUSCIN as [TIME CORRECT].
  split.
  omega.
  unfold plus_time_lb, plus_time_ub.
  omega.
Qed.

Lemma plus_big_oh_log : big_oh (fun n => plus_time_ub n n) cl_log.
Proof.
  exists 3 6.
  intros n.
  destruct n. intuition.
  destruct n. intuition.
  destruct n. intuition.
  intros _.
  unfold plus_time_ub.
  apply (well_founded_ind
           lt_wf
           (fun n => plus_cin_time_ub (S (S (S n))) (S (S (S n))) + 1 <=
                     6 * cl_log (S (S (S n))))).
  clear n; intros n IND.
  rewrite plus_cin_time_ub_SS.
  rewrite cl_log_div2'.
  
  apply (le_trans (plus_cin_time_ub (div2 (S (S (S n)))) (div2 (S (S (S n)))) + 1 + 1)
                  (6 * cl_log (div2 (S (S (S n)))) + 1)).
  apply plus_le_compat;auto.
  destruct n.
  simpl div2.
  repeat (rewrite plus_cin_time_ub_SS; simpl div2).
  simpl.
  omega.
  
  destruct n.
  simpl div2.
  repeat (rewrite plus_cin_time_ub_SS; simpl div2).
  simpl.
  omega.

  destruct n.
  simpl div2.
  repeat (rewrite plus_cin_time_ub_SS; simpl div2).
  simpl.
  omega.

  simpl div2.
  apply IND.
  apply (lt_le_trans (div2 n) (S n));auto.
  omega.
Qed.

Lemma log_below_plus_time_nn : forall n, cl_log n <= plus_time_lb n n.
Proof.
  unfold plus_time_lb.
  intros n.
  apply (well_founded_ind
           lt_wf
           (fun n => cl_log n <= plus_cin_time_lb n n + 1)).
  clear n; intros n IND.

  destruct n.
  simpl.
  unfold_sub cl_log (cl_log 0).
  omega.

  destruct n.
  simpl.
  unfold_sub cl_log (cl_log 1).
  unfold_sub cl_log (cl_log 0).
  omega.

  rewrite plus_cin_time_lb_SS.
  rewrite cl_log_div2'.
  apply (le_trans 
           (S (cl_log (div2 (S (S n)))))
           (S (plus_cin_time_lb (div2 (S (S n))) (div2 (S (S n))) + 1))); [|omega].
  apply le_n_S.
  apply IND.
  auto.
Qed.

Lemma plus_time_lb_below_log_nn :
  forall n,
    plus_time_lb n n = cl_log n + 2.
Proof.
  intros.
  unfold plus_time_lb.
  replace (cl_log n + 2) with (cl_log n + 1 + 1);[|omega].
  assert (plus_cin_time_lb n n = cl_log n + 1).
  apply (well_founded_ind
           lt_wf
           (fun n => plus_cin_time_lb n n = cl_log n + 1)).
  clear. intros. destruct x. compute. auto.
  rewrite plus_cin_time_lb_SS.
  rewrite cl_log_div2'.
  rewrite H. omega.
  apply lt_div2.
  omega.
  rewrite H.
  auto.
Qed.
  
Lemma plus_big_theta_log : big_oh cl_log (fun n => plus_time_lb n n).
Proof.
  exists 0 1.
  intros n _.
  rewrite mult_1_l.
  apply log_below_plus_time_nn.
Qed.

Theorem plus_log :
  forall f,
    (forall n m, plus_time_lb n m <= f (min n m)
                 /\ f (max n m) <= plus_time_ub n n) -> 
    big_theta f cl_log.
Proof.
  intros f FACT.
  split.
  apply (big_oh_trans f (fun n => plus_time_ub n n)).
  exists 0 1.
  intros n _.
  remember (FACT n n) as TWO; clear HeqTWO.
  rewrite Nat.max_id in TWO.
  omega.
  apply plus_big_oh_log.
  
  apply big_oh_rev.
  apply (big_oh_trans cl_log (fun n => plus_time_lb n n)).
  apply plus_big_theta_log.
  exists 0 1.
  intros n _.
  remember (FACT n n) as TWO; clear HeqTWO.
  rewrite Nat.min_id in TWO.
  omega.
Qed.

Lemma plus_cin_time_lb_growth :
  forall n,
    plus_cin_time_lb n n + 1 <=
    2 * plus_cin_time_lb n n.
Proof.
  intros n.
  apply (well_founded_ind
           lt_wf
           (fun n => plus_cin_time_lb n n + 1 <= 2 * plus_cin_time_lb n n)).
  clear n; intros n IND.
  destruct n; [compute; omega|].
  destruct n; [compute; omega|].
  rewrite plus_cin_time_lb_SS.
  simpl div2.
  apply (le_trans (plus_cin_time_lb (S (div2 n)) (S (div2 n)) + 1 + 1)
                  (2 * plus_cin_time_lb (S (div2 n)) (S (div2 n)) + 1)).
  apply plus_le_compat;auto.
  apply (IND (S (div2 n))).
  apply lt_n_S; auto.
  rewrite mult_plus_distr_l.
  omega.
Qed.
