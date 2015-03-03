Require Import Program Div2 Omega.
Require Import Arith Arith.Even Arith.Div2.
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

Theorem plus_cin_linear : 
  forall f,
    (forall n, plus_cin_time_lb n n <= f n <= plus_cin_time_ub n n) ->
    big_oh f fl_log.
Admitted.
