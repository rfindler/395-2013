Require Import Braun.common.util Braun.common.le_util Braun.common.same_structure.
Require Import Braun.common.log Braun.common.big_oh Braun.common.le_util.
Require Import Braun.common.sequence Braun.common.list_util.
Require Import Braun.monad.monad.
Require Import Program.
Require Import Omega.
Require Import List Relations_1.
Require Import Sorting.Sorted Sorting.Permutation.
Require Import Min.
Require Import Div2.
Require Import Even.
Require Import Braun.sort.sorting Braun.sort.isort.
Require Import Coq.Program.Wf Arith.Even Arith.Div2 Arith Init.Wf.

Include WfExtensionality.

Definition clength_time (n:nat) := 7*n + 3.
Hint Unfold clength_time.

Definition clength_result (A:Set) (l:list A) (res:nat) (c:nat) :=
    res = length l /\
    c = clength_time (length l).
Hint Unfold clength_result.

Load "clength_gen.v".

Next Obligation.
Proof.
  clear H1 am.
  rename H0 into CR.

  destruct CR.
  unfold clength_result.
  unfold clength_time in *.
  split; simpl; omega.
Qed.

Definition split2_time (n:nat) := 15 * n + 5.

Definition split2_result (A:Set) (n:nat) (l:list A) (V:n <= length l) 
           (res:((list A)*(list A))) (c:nat) :=
    l = (fst res) ++ (snd res) /\
    length (fst res) = min n (length l) /\
    c = split2_time n.

Load "split2_gen.v".

Next Obligation.
Proof.
  unfold split2_result.
  unfold split2_time.
  simpl in *. auto.
Qed.

Next Obligation.
Proof.
  simpl in *. omega.
Defined.

Local Obligation Tactic := idtac.

Next Obligation.
Proof.
  unfold split2_result.
  unfold split2_time.
  intros A n l VL n' EQn. subst n.
  intros a l' EQl. subst l.
  simpl in VL.
  omega.
Qed.

Next Obligation.
Proof.
  intros A n l NLT n' n'EQ.
  subst n.
  intros a l' LEQ.
  subst l.
  simpl in NLT.
  omega.
Qed.

Next Obligation.
Proof.
  unfold split2_result.
  unfold split2_time.
  intros A n l VL n' EQn. subst n.
  intros a l' EQl. subst l.
  intros [xs1 xs2] _.
  intros xm EQxm. subst xm.
  intros an REC_P.
  destruct REC_P as [EQl' [EQlen_xs1 EQan]].
  subst l'.  subst an. 
  split. auto.
  split. simpl. auto.
  replace (S n') with (n'+1);[|omega].
  rewrite mult_plus_distr_l.
  omega.
Qed.

Definition merge_best_time (n:nat) (m:nat) := 17 * (min n m) + 3.
Definition merge_worst_time (n:nat) (m:nat) := 17 * (n + m) + 3.
Hint Unfold merge_best_time merge_worst_time.

Definition merge_result (A:Set) (A_cmp:A -> A -> Prop)
           (A_cmp_trans:Transitive A_cmp) (A_cmp_total:Total A_cmp)
           (A_cmp_dec:DecCmp A_cmp) (xs:list A) (ys:list A) (res : list A) (c : nat) :=
    (IsSorted A_cmp xs) ->
    (IsSorted A_cmp ys) ->
    (SortedOf A_cmp (xs ++ ys) res) /\
    merge_best_time (length xs) (length ys) <= c /\
    c <= merge_worst_time (length xs) (length ys).

Load "merge_gen.v".

Next Obligation.
Proof.
  unfold merge_result.
  intros A A_cmp A_cmp_trans A_cmp_total A_cmp_dec.
  intros xs ys _.
  intros EQxs. subst xs.
  simpl. simpl_list.
  intros xm EQxm. subst xm.
  unfold SortedOf.
  intros ISxs ISys.
  split. eauto.
  unfold merge_best_time, merge_worst_time.
  rewrite min_0_l.
  omega.
Qed.

Next Obligation.
Proof.
  unfold merge_result.
  intros A A_cmp A_cmp_trans A_cmp_total A_cmp_dec.
  intros xs ys _.
  intros x xs' EQxs.
  subst xs.
  intros EQys. subst ys.
  simpl.
  intros xm EQxm. subst xm.
  unfold SortedOf.
  intros ISxs ISys.
  rewrite app_nil_r.

  split. eauto.
  unfold merge_best_time, merge_worst_time.
  rewrite min_0_r.
  omega.
Qed.

Next Obligation.
Proof.
  unfold merge_result.
  intros A A_cmp A_cmp_trans A_cmp_total A_cmp_dec.
  intros xs ys _.
  intros x xs' EQxs. subst xs.
  intros y ys' EQys. subst ys.
  intros _ _.
  simpl. omega.
Qed.

Next Obligation.
Proof.
  unfold merge_result in *.
  intros A A_cmp A_cmp_trans A_cmp_total A_cmp_dec.
  intros xs ys _.
  intros x xs' EQxs. subst xs.
  intros y ys' EQys. subst ys.
  intros CMP _.
  intros res _.
  simpl. intros xm EQxm. subst xm.
  intros Nrec REC_P.
  intros ISxs ISys.

  edestruct REC_P as [SOres REC_T].
  unfold IsSorted in *.
  apply StronglySorted_inv in ISxs.
  intuition.
  auto.
  clear REC_P.
  destruct SOres as [PM ISres].
  
  split.
  split.
  eauto.
  unfold IsSorted in *.
  eapply SSorted_cons. auto.
  apply Forall_forall. intros a.
  intros IN.
  eapply Permutation_in in IN; [ idtac | apply Permutation_sym; apply PM ].
  clear PM.
  apply StronglySorted_inv in ISys.
  destruct ISys as [SSys Fys].
  rewrite Forall_forall in Fys.
  apply StronglySorted_inv in ISxs.
  destruct ISxs as [SSxs Fxs].
  rewrite Forall_forall in Fxs.
  apply in_app_or in IN.
  destruct IN as [IN|IN]; auto.
  destruct IN as [IN|IN].
  subst a. auto.
  eapply A_cmp_trans.
  apply CMP. auto.

  unfold merge_best_time, merge_worst_time in *.
  split; [ | omega ].
  destruct REC_T as [REC_T _].
  apply min_case_strong; intros LE.
  inversion LE. rename H0 into EQ. rewrite <- EQ in *.
  rewrite min_l in REC_T; try omega.
  subst m. 
  rewrite min_l in REC_T; try omega.
  
  inversion LE. rename H0 into EQ. rewrite EQ in *.
  rewrite min_l in REC_T; try omega.
  subst m. 
  rewrite min_r in REC_T; try omega.
Qed.

Next Obligation.
Proof.
  unfold merge_result.
  intros A A_cmp A_cmp_trans A_cmp_total A_cmp_dec.
  intros xs ys _.
  intros x xs' EQxs. subst xs.
  intros y ys' EQys. subst ys.
  intros CMP _.
  simpl. rewrite app_length.
  rewrite app_length. simpl. omega.
Qed.

Next Obligation.
Proof.
  unfold merge_result.
  intros A A_cmp A_cmp_trans A_cmp_total A_cmp_dec.
  intros xs ys _.
  intros x xs' EQxs. subst xs.
  intros y ys' EQys. subst ys.
  intros CMP _.
  intros res _.
  simpl. intros xm EQxm. subst xm.
  intros Nrec REC_P.
  intros ISxs ISys.

  edestruct REC_P as [SOres REC_T].
  auto.
  unfold IsSorted in *.
  apply StronglySorted_inv in ISys.
  intuition.
  clear REC_P.
  destruct SOres as [PM ISres].

  split.
  split.
  
  apply Permutation_sym.  
  eapply Permutation_trans.
  eapply Permutation_cons.
  apply Permutation_sym.
  apply PM.
  replace (x :: xs' ++ y :: ys') with
    ((x :: xs') ++ y :: ys').
  replace (y :: x :: xs' ++ ys') with
    (y :: (x :: xs') ++ ys').
  apply Permutation_cons_app.
  auto.
  simpl. auto.
  simpl. auto.

  unfold IsSorted in *.
  eapply SSorted_cons. auto.
  apply Forall_forall. intros a.
  intros IN.
  eapply Permutation_in in IN; [ idtac | apply Permutation_sym; apply PM ].
  clear PM.
  apply StronglySorted_inv in ISys.
  destruct ISys as [SSys Fys].
  rewrite Forall_forall in Fys.
  apply StronglySorted_inv in ISxs.
  destruct ISxs as [SSxs Fxs].
  rewrite Forall_forall in Fxs.
  destruct IN as [IN|IN].
  subst a. auto.
  apply in_app_or in IN.
  destruct IN as [IN|IN]; auto.
  eapply A_cmp_trans.
  apply A_cmp_total.
  apply CMP. auto.

  unfold merge_best_time, merge_worst_time in *.
  split; [|omega].
  (* XXX copy, ugh *)
  destruct REC_T as [REC_T _].
  apply min_case_strong; intros LE.
  inversion LE. rename H0 into EQ. rewrite <- EQ in *.
  rewrite min_r in REC_T; try omega.
  subst m. 
  rewrite min_l in REC_T; try omega.
  
  inversion LE. rename H0 into EQ. rewrite EQ in *.
  rewrite min_r in REC_T; try omega.
  subst m.
  rewrite min_r in REC_T; try omega.
Qed.

Next Obligation.
Proof.
  program_simpl.
Defined.

Lemma xs1_lt_l:
  forall A (x:A) (l' l xs1:list A) len,
    x :: l' = l ->
    len = length l ->
    length xs1 = min (div2 len) len ->
    length xs1 < length l.
Proof.
  intros A x l' l xs1 len EQl EQlen EQlen_xs1.
  subst len.
  rewrite min_div2 in EQlen_xs1. rewrite EQlen_xs1.
  clear EQlen_xs1.
  apply lt_div2.
  subst l. simpl. omega.
Qed.

Lemma xs1_eq_xs2:
  forall A len (l xs1 xs2:list A),
    len = length l ->
    even len ->
    l = xs1 ++ xs2 ->
    length xs1 = min (div2 len) (length l) ->
    length xs2 = length xs1.
Proof.
  intros A len l xs1 xs2 EQlen EVEN EQl EQlen_xs1.
  subst len.
  rewrite min_div2 in EQlen_xs1.
  rewrite EQl in *.
  rewrite app_length in *.
  apply even_double in EVEN.  
  rewrite <- EQlen_xs1 in EVEN.
  unfold double in EVEN. omega.
Qed.

Program Fixpoint mergesortc_worst_time n {measure n} :=
  match n with
    | 0 => 3
    | S n' => 
      if (even_odd_dec n)
      then (split2_time (div2 n) +
            mergesortc_worst_time (div2 n) +
            mergesortc_worst_time (div2 n) +
            merge_worst_time (div2 n) (div2 n) + 35)
      else  (mergesortc_worst_time n' +
             insert_worst_time n' + 20)
  end.

Solve Obligations using (intros; subst n; auto).
Solve Obligations using (apply lt_wf).

Program Fixpoint mergesortc_best_time n {measure n} :=
  match n with
    | 0 => 3
    | S n' => 
      if (even_odd_dec n)
      then (split2_time (div2 n) +
            mergesortc_best_time (div2 n) +
            mergesortc_best_time (div2 n) +
            merge_best_time (div2 n) (div2 n) + 35)
      else  (mergesortc_best_time n' +
             insert_best_time n' + 20)
  end.
Solve Obligations using (intros; subst n; auto).
Solve Obligations using (apply lt_wf).

Definition mergesortc_result 
           (A:Set) (A_cmp:A -> A -> Prop)
           (A_cmp_trans:Transitive A_cmp) (A_cmp_total:Total A_cmp)
           (A_cmp_dec:DecCmp A_cmp) (l:list A) (len:nat) (EQlen:len = length l)
           (res : list A) (c:nat) :=
    (SortedOf A_cmp l res) /\
    mergesortc_best_time (length l) <= c /\
    c <= mergesortc_worst_time (length l).

Load "mergesortc_gen.v".

Next Obligation.
Proof.
  unfold mergesortc_result.
  intros A A_cmp A_cmp_trans A_cmp_total A_cmp_dec
    l len EQlen _ x xm EQxm.
  subst l. subst xm. simpl.
  clear len EQlen.
  
  unfold SortedOf. unfold IsSorted.
  split. split. auto. apply SSorted_nil.

  unfold_sub mergesortc_best_time (mergesortc_best_time 0).
  unfold_sub mergesortc_worst_time (mergesortc_worst_time 0).
  omega.
Qed.

Next Obligation.
Proof.
  unfold mergesortc_result.
  intros A A_cmp A_cmp_trans A_cmp_total A_cmp_dec.
  intros l len EQlen _ x l' EQl' EVEN.
  subst len. subst l. simpl (length (x::l')).

  remember (lt_div2 (S (length l'))) as LT. omega.
Qed.

Next Obligation.
Proof.
  unfold mergesortc_result.
  intros A A_cmp A_cmp_trans A_cmp_total A_cmp_dec.
  intros l len EQlen MERGESORTC x l' EQl' EVEN [xs1 xs2] SPLIT_P.
  destruct SPLIT_P as [an [EQl [EQlen_xs1 _]]].
  simpl in *. subst len.
  rewrite min_div2 in EQlen_xs1. auto.
Qed.

Next Obligation.
Proof.
  unfold mergesortc_result.
  intros A A_cmp A_cmp_trans A_cmp_total A_cmp_dec l len EQlen.
  intros MERGESORTC x l' EQl' EVEN [xs1 xs2] SPLIT_P.
  destruct SPLIT_P as [an [EQl [EQlen_xs1 _]]].
  simpl in *.
  eapply xs1_lt_l; auto.
  apply EQl'. subst len. auto.
Qed.

Next Obligation.
Proof.
  unfold mergesortc_result.
  intros A A_cmp A_cmp_trans A_cmp_total A_cmp_dec l len EQlen.
  intros MERGESORTC x l' EQl' EVEN [xs1 xs2] SPLIT_P _ _.
  destruct SPLIT_P as [an [EQl [EQlen_xs1 _]]].
  simpl in *.
  rewrite (xs1_eq_xs2 A len l xs1 xs2 EQlen EVEN EQl EQlen_xs1).
  subst len.
  rewrite min_div2 in EQlen_xs1.
  auto.
Qed.

Next Obligation.
Proof.
  unfold mergesortc_result.
  intros A A_cmp A_cmp_trans A_cmp_total A_cmp_dec l len EQlen. 
  intros MERGESORTC x l' EQl' EVEN [xs1 xs2] SPLIT_P _ _.
  destruct SPLIT_P as [an [EQl [EQlen_xs1 _]]].
  simpl in *.
  rewrite (xs1_eq_xs2 A len l xs1 xs2 EQlen EVEN EQl EQlen_xs1).
  eapply xs1_lt_l; auto.
  apply EQl'. subst len. auto.
Qed.

Next Obligation.
Proof.
  unfold mergesortc_result.
  intros A A_cmp A_cmp_trans A_cmp_total A_cmp_dec.
  intros l len EQlen MERGESORTC.
  intros x l' EQl.
  intros E.
  intros [xs1 xs2] _.
  unfold fst, snd in *.
  intros xs1' _.
  intros xs2' _.
  intros res _.
  intros xm EQxm.
  subst xm.
  intros Nmerge MERGE_P.
  intros Nrec2 REC2_P.
  intros Nrec1 REC1_P.
  intros Nsplit SPLIT_P.
  destruct SPLIT_P as [EQlapp [EQlen_xs1 SPLIT_P]].
  remember (xs1_eq_xs2 A len l xs1 xs2 EQlen E EQlapp EQlen_xs1) as EQlen_xs2.
  rewrite EQlen_xs2 in *.
  rewrite <- EQl.
  destruct REC1_P as [SO1 REC1_P].
  destruct REC2_P as [SO2 REC2_P].
  edestruct MERGE_P as [SOr MERGE_T].
  unfold SortedOf in SO1. intuition.
  unfold SortedOf in SO2. intuition.
  clear MERGE_P.
  destruct SO2 as [PM2 SS2].
  destruct SO1 as [PM1 SS1].
  destruct SOr as [PMr SSr].
  rewrite <- (Permutation_length PM1) in *.
  rewrite <- (Permutation_length PM2) in *.  
  subst l.
  split.

  split.
  rewrite EQlapp.
  apply Permutation_sym.
  eapply Permutation_trans.
  apply Permutation_sym.
  apply PMr.
  apply Permutation_app.
  apply Permutation_sym. auto.
  apply Permutation_sym. auto.
  auto.

  clear SS1 SS2 PMr SSr res.
  clear xs2' PM2.
  clear xs1' PM1.
  clear A_cmp A_cmp_trans A_cmp_total A_cmp_dec.
  clear HeqEQlen_xs2.
  rewrite EQlapp.
  remember EQlen as EQlen'. clear HeqEQlen'.
  rewrite app_length.
  rewrite <- EQlen in EQlen_xs1.
  rewrite EQlapp in EQlen.
  rewrite app_length in EQlen.
  rewrite EQlen_xs2 in *.
  rewrite min_div2 in EQlen_xs1.
  rewrite EQlen_xs1 in *.
  remember (div2 len) as D.

  destruct D as [|D].
  simpl in EQlen'.
  unfold snd in *.
  unfold fst in *.
  assert (xs1 = nil).
  destruct xs1; intuition.
  subst xs1.
  simpl in EQlapp.
  subst xs2.
  simpl in EQlen_xs2.
  intuition.
  
  clear MERGESORTC.
  unfold snd in *.
  unfold fst in *.
  subst len.
  rewrite EQlen' in *.
  simpl.
  subst Nsplit.

  destruct xs1;[simpl in EQlen_xs1; intuition|].
  
  assert (x = a);[simpl in EQlapp;congruence|subst a].
  assert (l' = xs1++xs2); [simpl in EQlapp;congruence|subst l'].
  clear EQlapp.
  simpl length in REC2_P, REC1_P, EQlen_xs2, MERGE_T, EQlen_xs1, HeqD, EQlen', E.
  replace (length (xs1 ++ xs2)) with (length xs1 + length xs2) in *;
    [|rewrite app_length; auto].
  assert (length xs1 = D) as DEQ;[congruence|rewrite DEQ in *;clear EQlen_xs1 DEQ].
  remember (length xs2) as D'; clear HeqD'; subst D'.
  clear xs1 xs2.
  replace (S (D + S D)) with (S (S (D+D))) in *;[|omega].
  unfold_sub mergesortc_best_time (mergesortc_best_time (S (S (D+D)))).
  fold mergesortc_best_time.
  unfold_sub mergesortc_worst_time (mergesortc_worst_time (S (S (D+D)))).
  fold mergesortc_worst_time.
  destruct (even_odd_dec (S (S (D+D)))).
  replace (div2 (S (S (D + D)))) with (S D).
  replace (div2 (D+D)) with D;[|auto].
  omega.

  assert False.
  apply (not_even_and_odd (S (S (D+D)))); auto.
  intuition.
Qed.

Next Obligation.
Proof.
  unfold mergesortc_result.
  program_simpl.
Qed.

Next Obligation.
Proof.
  unfold mergesortc_result.
  program_simpl.
Qed.

Next Obligation.
Proof.
  unfold mergesortc_result.
  intros A A_cmp A_cmp_trans
    A_cmp_total A_cmp_dec.  
  intros l len EQlen _.
  intros x l' EQl.
  intros O.
  intros res' _.
  intros res _.
  intros xm EQxm.
  subst xm.
  intros Ninsert INSERT_P.
  intros Nrec [SOres' REC_P].
  destruct INSERT_P as [SOres INSERT_P].
  destruct SOres'. auto.
  unfold SortedOf in *.
  destruct SOres as [PMres ISres].
  destruct SOres' as [PMres' ISres'].
  split.

  split.
  apply Permutation_sym.
  eapply Permutation_trans.
  apply Permutation_sym.
  apply PMres.
  subst l.
  apply perm_skip.
  apply Permutation_sym.
  apply PMres'.
  auto.

  clear ISres ISres'.
  clear res PMres.
  clear A_cmp A_cmp_trans A_cmp_total A_cmp_dec.
  rewrite <- (Permutation_length PMres') in *.
  clear res' PMres'.

  subst l.
  simpl length in *.
  subst len.
  unfold_sub mergesortc_best_time (mergesortc_best_time (S (length l'))).
  fold mergesortc_best_time.
  unfold_sub mergesortc_worst_time (mergesortc_worst_time (S (length l'))).
  fold mergesortc_worst_time.
  destruct (even_odd_dec (S (length l'))).
  
  assert False.
  apply (not_even_and_odd (S (length l'))); auto.
  intuition.
  omega.
Qed.

Next Obligation.
Proof.
  unfold mergesortc_result.
  program_simpl.
Defined.

Program Fixpoint mergesortc_worst_time2 n {measure n} :=
  match n with
    | 0 => 3
    | S n' => 
      if (even_odd_dec n)
      then (split2_time (div2 n) +
            mergesortc_worst_time2 (div2 n) +
            mergesortc_worst_time2 (div2 n) +
            merge_worst_time (div2 n) (div2 n) + 35)
      else  ((match n' with
                | 0 => 3
                | S n'' => 
                  (split2_time (div2 n') +
                   mergesortc_worst_time2 (div2 n') +
                   mergesortc_worst_time2 (div2 n') +
                   merge_worst_time (div2 n') (div2 n') + 35)
              end) +
             insert_worst_time n' + 20)
  end.
Solve Obligations using (intros; subst n; auto).
Solve Obligations using (apply lt_wf).

Lemma worst_12 : forall n, mergesortc_worst_time n = mergesortc_worst_time2 n.
Proof.
  apply (well_founded_induction 
           lt_wf
           (fun n => mergesortc_worst_time n = mergesortc_worst_time2 n)).
  intros n INDn.
  destruct n.
  unfold_sub mergesortc_worst_time (mergesortc_worst_time 0).
  unfold_sub mergesortc_worst_time2 (mergesortc_worst_time2 0).
  auto.
  unfold_sub mergesortc_worst_time (mergesortc_worst_time (S n)).
  fold mergesortc_worst_time.
  unfold_sub mergesortc_worst_time2 (mergesortc_worst_time2 (S n)).
  fold mergesortc_worst_time2.
  destruct (even_odd_dec (S n)).
  rewrite INDn; auto.
  destruct n; auto.
  apply lt_n_S; auto.
  destruct n.
  unfold insert_worst_time.
  unfold_sub mergesortc_worst_time (mergesortc_worst_time 0).
  omega.
  rewrite INDn; auto.
  unfold_sub mergesortc_worst_time2 (mergesortc_worst_time2 (S n)).
  fold mergesortc_worst_time2.
  destruct (even_odd_dec (S n)).
  destruct n; auto.
  inversion o.
  assert False.
  apply (not_even_and_odd (S n)); auto.
  intuition.
Qed.

Program Fixpoint mergesortc_worst_time3 n {measure n} :=
  match n with
    | 0 => 3
    | S n' => 
      if (even_odd_dec n)
      then (split2_time (div2 n) +
            mergesortc_worst_time3 (div2 n) +
            mergesortc_worst_time3 (div2 n) +
            merge_worst_time (div2 n) (div2 n) + 35)
      else match n' with
             | 0 => 3 + insert_worst_time n' + 20
             | S n'' => 
               (split2_time (div2 n') +
                mergesortc_worst_time3 (div2 n') +
                mergesortc_worst_time3 (div2 n') +
                merge_worst_time (div2 n') (div2 n') + 35
                + insert_worst_time n' + 20)
           end
  end.
Solve Obligations using (intros; subst n; auto).
Solve Obligations using (apply lt_wf).

Lemma worst_23 : forall n, mergesortc_worst_time2 n = mergesortc_worst_time3 n.
Proof.
  apply (well_founded_induction 
           lt_wf
           (fun n => mergesortc_worst_time2 n = mergesortc_worst_time3 n)).
  intros n INDn.
  destruct n.
  unfold_sub mergesortc_worst_time2 (mergesortc_worst_time2 0).
  unfold_sub mergesortc_worst_time3 (mergesortc_worst_time3 0).
  auto.
  unfold_sub mergesortc_worst_time2 (mergesortc_worst_time2 (S n)).
  fold mergesortc_worst_time2.
  unfold_sub mergesortc_worst_time3 (mergesortc_worst_time3 (S n)).
  fold mergesortc_worst_time3.
  rewrite INDn; [|destruct n; try apply lt_n_S; auto].
  rewrite INDn; auto.
  clear INDn.
  destruct (even_odd_dec (S n)); auto.
  destruct n; auto.
Qed.

Program Fixpoint mergesortc_worst_time4 n {measure n} :=
  match n with
    | 0 => 3
    | S n' => 
      match n' with
        | 0 => if (even_odd_dec n)
               then (split2_time (div2 n) +
                     mergesortc_worst_time4 (div2 n) +
                     mergesortc_worst_time4 (div2 n) +
                     merge_worst_time (div2 n) (div2 n) + 35)
               else 3 + insert_worst_time n' + 20
        | S n'' => 
          if (even_odd_dec n)
          then (split2_time (div2 n) +
                mergesortc_worst_time4 (div2 n) +
                mergesortc_worst_time4 (div2 n) +
                merge_worst_time (div2 n) (div2 n) + 35)
          else 
            (split2_time (div2 n') +
             mergesortc_worst_time4 (div2 n') +
             mergesortc_worst_time4 (div2 n') +
             merge_worst_time (div2 n') (div2 n') + 35
             + insert_worst_time n' + 20)
      end
  end.
Solve Obligations using (intros; subst n; auto).
Solve Obligations using (apply lt_wf).

Lemma worst_34 : forall n, mergesortc_worst_time3 n = mergesortc_worst_time4 n.
Proof.
  apply (well_founded_induction 
           lt_wf
           (fun n => mergesortc_worst_time3 n = mergesortc_worst_time4 n)).
  intros n INDn.
  destruct n.
  unfold_sub mergesortc_worst_time3 (mergesortc_worst_time3 0).
  unfold_sub mergesortc_worst_time4 (mergesortc_worst_time4 0).
  auto.
  unfold_sub mergesortc_worst_time3 (mergesortc_worst_time3 (S n)).
  fold mergesortc_worst_time3.
  unfold_sub mergesortc_worst_time4 (mergesortc_worst_time4 (S n)).
  fold mergesortc_worst_time4.
  destruct (even_odd_dec (S n)).
  destruct n.
  unfold_sub mergesortc_worst_time3 (mergesortc_worst_time3 0).
  unfold_sub mergesortc_worst_time4 (mergesortc_worst_time4 0).
  omega.
  rewrite INDn; try apply lt_n_S; auto.
  rewrite INDn; auto.
Qed.

Program Fixpoint mergesortc_worst_time5 n {measure n} :=
  match n with
    | 0 => 3
    | S n' => 
      match n' with
        | 0 => 32
        | S _ => 
          if (even_odd_dec n)
          then (split2_time (div2 n) +
                mergesortc_worst_time5 (div2 n) +
                mergesortc_worst_time5 (div2 n) +
                merge_worst_time (div2 n) (div2 n) + 35)
          else 
            (split2_time (div2 n') +
             mergesortc_worst_time5 (div2 n') +
             mergesortc_worst_time5 (div2 n') +
             merge_worst_time (div2 n') (div2 n') + 35
             + insert_worst_time n' + 20)
      end
  end.
Solve Obligations using (intros; subst n; auto).
Solve Obligations using (apply lt_wf).

Lemma worst_45 : forall n, mergesortc_worst_time4 n = mergesortc_worst_time5 n.
Proof.
  apply (well_founded_induction 
           lt_wf
           (fun n => mergesortc_worst_time4 n = mergesortc_worst_time5 n)).
  intros n INDn.
  destruct n.
  unfold_sub mergesortc_worst_time4 (mergesortc_worst_time4 0).
  unfold_sub mergesortc_worst_time5 (mergesortc_worst_time5 0).
  auto.
  destruct n.
  unfold_sub mergesortc_worst_time4 (mergesortc_worst_time4 1).
  fold mergesortc_worst_time4.
  unfold_sub mergesortc_worst_time5 (mergesortc_worst_time5 1).
  unfold_sub mergesortc_worst_time4 (mergesortc_worst_time4 0).
  simpl.
  auto.
  unfold_sub mergesortc_worst_time4 (mergesortc_worst_time4 (S (S n))).
  fold mergesortc_worst_time4.
  unfold_sub mergesortc_worst_time5 (mergesortc_worst_time5 (S (S n))).
  fold mergesortc_worst_time5.
  repeat (rewrite INDn).
  auto.
  destruct n; auto.
  apply lt_n_S; auto.
Qed.


Program Fixpoint mergesortc_worst_time6 n {measure n} :=
  match n with
    | 0 => 3
    | S n' => 
      match n' with
        | 0 => 32
        | S _ => 
          split2_time (div2 n) +
          mergesortc_worst_time6 (div2 n) +
          mergesortc_worst_time6 (div2 n) +
          merge_worst_time (div2 n) (div2 n) + 35
          + insert_worst_time n' + 20
      end
  end.
Solve Obligations using (intros; subst n; auto).
Solve Obligations using (apply lt_wf).

Lemma worst_56 : big_oh mergesortc_worst_time5 mergesortc_worst_time6.
Proof.
  exists 0.
  exists 1.
  intros n _.
  replace (1 * mergesortc_worst_time6 n) with (mergesortc_worst_time6 n); [|omega].
  apply (well_founded_induction 
           lt_wf
           (fun n => mergesortc_worst_time5 n <= mergesortc_worst_time6 n)).
  clear n.
  intros n INDn.
  destruct n.
  unfold_sub mergesortc_worst_time5 (mergesortc_worst_time5 0).
  unfold_sub mergesortc_worst_time6 (mergesortc_worst_time6 0).
  auto.
  unfold_sub mergesortc_worst_time5 (mergesortc_worst_time5 (S n)).
  fold mergesortc_worst_time5.
  unfold_sub mergesortc_worst_time6 (mergesortc_worst_time6 (S n)).
  fold mergesortc_worst_time6.
  destruct n; auto.
  destruct (even_odd_dec (S (S n))).
  apply le_plus_trans.
  apply le_plus_trans.
  repeat (apply plus_le_compat; try auto; try (apply INDn; apply lt_n_S; auto)).
  replace (div2 (S n)) with (S (div2 n)).
  repeat (apply plus_le_compat; try auto; try (apply INDn; apply lt_n_S; auto)).
  apply odd_div2.
  inversion o as [WHATEVER E WHATEVERELSE].
  inversion E.
  auto.
Qed.

Program Fixpoint mergesortc_worst_time7 n {measure n} :=
  match n with
    | 0 => 1
    | S n' => 
      match n' with
        | 0 => 1
        | S _ => 
          (div2 n) + n +
          mergesortc_worst_time7 (div2 n) +
          mergesortc_worst_time7 (div2 n)
      end
  end.
Solve Obligations using (intros; subst n; auto).
Solve Obligations using (apply lt_wf).

Lemma worst_67 : big_oh mergesortc_worst_time6 mergesortc_worst_time7.
Proof.
  exists 1.
  exists 60.
  intros n LT.
  destruct n.
  intuition.
  clear LT.
  apply (well_founded_induction 
           lt_wf
           (fun n => mergesortc_worst_time6 (S n) <=
                     60 * mergesortc_worst_time7 (S n))).
  clear n.
  intros n INDn.
  unfold_sub mergesortc_worst_time6 (mergesortc_worst_time6 (S n)).
  fold mergesortc_worst_time6.
  unfold_sub mergesortc_worst_time7 (mergesortc_worst_time7 (S n)).
  fold mergesortc_worst_time7.
  destruct n;[omega|].

  unfold split2_time.
  unfold merge_worst_time.
  unfold insert_worst_time.
  
  replace (15 * S n) with (15 *(n+1));[|omega].
  repeat (rewrite mult_plus_distr_l).
  repeat (rewrite plus_assoc).

  replace (15 * div2 (S (S n)) + 5 + mergesortc_worst_time6 (S (div2 n)) +
           mergesortc_worst_time6 (S (div2 n)) + 17 * div2 (S (S n)) +
           17 * div2 (S (S n)) + 3 + 35 + 15 * n + 15 * 1 + 9 + 20)
  with (32 * div2 (S (S n)) + 
        17 * div2 (S (S n)) + 15 * n + 87 +
        mergesortc_worst_time6 (S (div2 n)) +
        mergesortc_worst_time6 (S (div2 n)));[|omega].

  replace (60 * S (S n)) with ((10 + 50) * (S (S n)));[|omega].
  rewrite mult_plus_distr_r.
  replace (50* (S (S n))) with (50 * (n + 2));[|omega].
  rewrite mult_plus_distr_l.
  repeat (rewrite plus_assoc).
  repeat (apply plus_le_compat; try omega; try (apply INDn; auto)).
Qed.

Program Fixpoint mergesortc_worst_time8 n {measure n} :=
  match n with
    | 0 => 0
    | S _ => 
      n +
      mergesortc_worst_time8 (div2 n) +
      mergesortc_worst_time8 (div2 n)
  end.
Solve Obligations using (intros; subst n; auto).
Solve Obligations using (apply lt_wf).

Lemma worst_78 : big_oh mergesortc_worst_time7 mergesortc_worst_time8.
Proof.
  exists 1.
  exists 8.
  intros n LT.
  destruct n. intuition.
  clear LT.
  apply (well_founded_induction 
           lt_wf
           (fun n => mergesortc_worst_time7 (S n) <=
                     8 * mergesortc_worst_time8 (S n))).
  clear n; intros n IND.
  unfold_sub mergesortc_worst_time7 (mergesortc_worst_time7 (S n)).
  fold mergesortc_worst_time7.
  unfold_sub mergesortc_worst_time8 (mergesortc_worst_time8 (S n)).
  destruct n.
  unfold_sub mergesortc_worst_time8 (mergesortc_worst_time8 0).
  omega.
  repeat (rewrite mult_plus_distr_l).
  apply plus_le_compat.
  apply plus_le_compat.
  replace 8 with (7+1);[|omega].
  rewrite mult_plus_distr_r.
  apply plus_le_compat; [|omega].
  apply (le_trans (div2 (S (S n)))
                  (div2 (S (S n)) + div2 (S (S n)))); [omega|].
  apply (le_trans (div2 (S (S n)) + div2 (S (S n)))
                  (S (S n)));[|omega].
  apply div2_doubled_le_n.
  apply IND; auto.
  apply IND; auto.
Qed.

Lemma worst_89 : big_oh mergesortc_worst_time8 (fun n => n * cl_log n).
Proof.
  exists 1.
  exists 4.
  intros n LT.
  destruct n. intuition.
  clear LT.
  apply (well_founded_induction 
           lt_wf
           (fun n => mergesortc_worst_time8 (S n) <=
                     4 * ((S n) * cl_log (S n)))).
  clear n; intros n IND.
  unfold_sub mergesortc_worst_time8 (mergesortc_worst_time8 (S n)).
  destruct n.
  unfold_sub mergesortc_worst_time8 (mergesortc_worst_time8 0).
  unfold_sub cl_log (cl_log 1).
  unfold_sub cl_log (cl_log 0).
  omega.
  apply (le_trans (S (S n) + 
                   mergesortc_worst_time8 (S (div2 n)) +
                   mergesortc_worst_time8 (S (div2 n)))
                  (S (S n) + 
                   (4 * (S (div2 n) * cl_log (S (div2 n)))) +
                   (4 * (S (div2 n) * cl_log (S (div2 n)))))).
  apply plus_le_compat.
  apply plus_le_compat; [omega|].
  apply IND; auto.
  apply IND; auto.
  clear IND.

  replace (S (S n) + 4 * (S (div2 n) * cl_log (S (div2 n))) +
           4 * (S (div2 n) * cl_log (S (div2 n))))
  with (S (S n) + 2 * 4 * (S (div2 n) * cl_log (S (div2 n)))); [|omega].
  replace (2 * 4) with 8;[|omega].
  replace (S (div2 n)) with (div2 n + 1) at 1;[|omega].
  rewrite mult_comm at 1.
  rewrite mult_plus_distr_r.
  unfold mult at 3.
  rewrite plus_0_r.
  rewrite mult_comm.
  rewrite mult_plus_distr_l.
  rewrite plus_assoc.
  rewrite mult_assoc.

  apply (le_trans
           (S (S n) + 8 * div2 n * cl_log (S (div2 n)) + 8 * cl_log (S (div2 n)))
           (S (S n) + 4 * n * cl_log (S (div2 n)) + 8 * cl_log (S (div2 n)))).
  apply plus_le_compat;[|omega].
  apply plus_le_compat;[omega|].
  apply mult_le_compat;[|omega].
  
  replace 8 with (4 * 2);[|omega].
  rewrite <- mult_assoc.
  apply mult_le_compat; [omega|].
  unfold mult.
  rewrite plus_0_r.
  apply div2_doubled_le_n.
  
  replace (S (div2 n)) with (div2 (S (S n))); auto.
  rewrite cl_log_div2'.
  replace (S (cl_log (div2 (S (S n))))) 
  with ((cl_log (div2 (S (S n))))+1);[|omega].
  rewrite mult_plus_distr_l.
  replace (4 * (S (S n) * cl_log (div2 (S (S n))) + S (S n) * 1))
  with (4 * (S (S n) * cl_log (div2 (S (S n))) + S (S n)));[|omega].
  rewrite mult_plus_distr_l.
  replace (4 * (S (S n) * cl_log (div2 (S (S n)))) + 4 * S (S n))
  with ((1+3) * S (S n) + 4 * (S (S n) * cl_log (div2 (S (S n)))));[|omega].
  rewrite mult_plus_distr_r.
  replace (1 * (S (S n))) with (S (S n)); [|omega].
  rewrite <- plus_assoc.
  rewrite <- plus_assoc.
  apply plus_le_compat;[omega|].
  replace (S (S n)) with (n+2) at 4;[|omega].
  rewrite mult_plus_distr_r.
  rewrite mult_plus_distr_l.
  replace (4 * (2 * cl_log (div2 (S (S n)))))
  with (8 * cl_log (div2 (S (S n))));[|omega].
  rewrite plus_assoc.
  apply plus_le_compat;auto.
  rewrite mult_assoc.
  omega.
Qed.

Program Fixpoint mergesortc_best_time2 n {measure n} :=
  match n with
    | 0 => 3
    | S n' => 
      if (even_odd_dec n)
      then (split2_time (div2 n) +
            mergesortc_best_time2 (div2 n) +
            mergesortc_best_time2 (div2 n) +
            merge_best_time (div2 n) (div2 n) + 35)
      else  ((match n' with
                | 0 => 3
                | S n'' => 
                  (split2_time (div2 n') +
                   mergesortc_best_time2 (div2 n') +
                   mergesortc_best_time2 (div2 n') +
                   merge_best_time (div2 n') (div2 n') + 35)
              end) +
             insert_best_time n' + 20)
  end.
Solve Obligations using (intros; subst n; auto).
Solve Obligations using (apply lt_wf).

Lemma best_12 : forall n, mergesortc_best_time n = mergesortc_best_time2 n.
Proof.
  apply (well_founded_induction 
           lt_wf
           (fun n => mergesortc_best_time n = mergesortc_best_time2 n)).
  intros n INDn.
  destruct n.
  unfold_sub mergesortc_best_time (mergesortc_best_time 0).
  unfold_sub mergesortc_best_time2 (mergesortc_best_time2 0).
  auto.
  unfold_sub mergesortc_best_time (mergesortc_best_time (S n)).
  fold mergesortc_best_time.
  unfold_sub mergesortc_best_time2 (mergesortc_best_time2 (S n)).
  fold mergesortc_best_time2.
  destruct (even_odd_dec (S n)).
  rewrite INDn; auto.
  destruct n; auto.
  apply lt_n_S; auto.
  destruct n.
  unfold insert_best_time.
  unfold_sub mergesortc_best_time (mergesortc_best_time 0).
  omega.
  rewrite INDn; auto.
  unfold_sub mergesortc_best_time2 (mergesortc_best_time2 (S n)).
  fold mergesortc_best_time2.
  destruct (even_odd_dec (S n)).
  destruct n; auto.
  inversion o.
  assert False.
  apply (not_even_and_odd (S n)); auto.
  intuition.
Qed.

Program Fixpoint mergesortc_best_time3 n {measure n} :=
  match n with
    | 0 => 3
    | S n' => 
      if (even_odd_dec n)
      then (split2_time (div2 n) +
            mergesortc_best_time3 (div2 n) +
            mergesortc_best_time3 (div2 n) +
            merge_best_time (div2 n) (div2 n) + 35)
      else match n' with
             | 0 => 3 + insert_best_time n' + 20
             | S n'' => 
               (split2_time (div2 n') +
                mergesortc_best_time3 (div2 n') +
                mergesortc_best_time3 (div2 n') +
                merge_best_time (div2 n') (div2 n') + 35
                + insert_best_time n' + 20)
           end
  end.
Solve Obligations using (intros; subst n; auto).
Solve Obligations using (apply lt_wf).

Lemma best_23 : forall n, mergesortc_best_time2 n = mergesortc_best_time3 n.
Proof.
  apply (well_founded_induction 
           lt_wf
           (fun n => mergesortc_best_time2 n = mergesortc_best_time3 n)).
  intros n INDn.
  destruct n.
  unfold_sub mergesortc_best_time2 (mergesortc_best_time2 0).
  unfold_sub mergesortc_best_time3 (mergesortc_best_time3 0).
  auto.
  unfold_sub mergesortc_best_time2 (mergesortc_best_time2 (S n)).
  fold mergesortc_best_time2.
  unfold_sub mergesortc_best_time3 (mergesortc_best_time3 (S n)).
  fold mergesortc_best_time3.
  rewrite INDn; [|destruct n; try apply lt_n_S; auto].
  rewrite INDn; auto.
  clear INDn.
  destruct (even_odd_dec (S n)); auto.
  destruct n; auto.
Qed.

Program Fixpoint mergesortc_best_time4 n {measure n} :=
  match n with
    | 0 => 3
    | S n' => 
      match n' with
        | 0 => if (even_odd_dec n)
               then (split2_time (div2 n) +
                     mergesortc_best_time4 (div2 n) +
                     mergesortc_best_time4 (div2 n) +
                     merge_best_time (div2 n) (div2 n) + 35)
               else 3 + insert_best_time n' + 20
        | S n'' => 
          if (even_odd_dec n)
          then (split2_time (div2 n) +
                mergesortc_best_time4 (div2 n) +
                mergesortc_best_time4 (div2 n) +
                merge_best_time (div2 n) (div2 n) + 35)
          else 
            (split2_time (div2 n') +
             mergesortc_best_time4 (div2 n') +
             mergesortc_best_time4 (div2 n') +
             merge_best_time (div2 n') (div2 n') + 35
             + insert_best_time n' + 20)
      end
  end.
Solve Obligations using (intros; subst n; auto).
Solve Obligations using (apply lt_wf).

Lemma best_34 : forall n, mergesortc_best_time3 n = mergesortc_best_time4 n.
Proof.
  apply (well_founded_induction 
           lt_wf
           (fun n => mergesortc_best_time3 n = mergesortc_best_time4 n)).
  intros n INDn.
  destruct n.
  unfold_sub mergesortc_best_time3 (mergesortc_best_time3 0).
  unfold_sub mergesortc_best_time4 (mergesortc_best_time4 0).
  auto.
  unfold_sub mergesortc_best_time3 (mergesortc_best_time3 (S n)).
  fold mergesortc_best_time3.
  unfold_sub mergesortc_best_time4 (mergesortc_best_time4 (S n)).
  fold mergesortc_best_time4.
  destruct (even_odd_dec (S n)).
  destruct n.
  unfold_sub mergesortc_best_time3 (mergesortc_best_time3 0).
  unfold_sub mergesortc_best_time4 (mergesortc_best_time4 0).
  omega.
  rewrite INDn; try apply lt_n_S; auto.
  rewrite INDn; auto.
Qed.

Program Fixpoint mergesortc_best_time5 n {measure n} :=
  match n with
    | 0 => 3
    | S n' => 
      match n' with
        | 0 => 28
        | S _ => 
          if (even_odd_dec n)
          then (split2_time (div2 n) +
                mergesortc_best_time5 (div2 n) +
                mergesortc_best_time5 (div2 n) +
                merge_best_time (div2 n) (div2 n) + 35)
          else 
            (split2_time (div2 n') +
             mergesortc_best_time5 (div2 n') +
             mergesortc_best_time5 (div2 n') +
             merge_best_time (div2 n') (div2 n') + 35
             + insert_best_time n' + 20)
      end
  end.
Solve Obligations using (intros; subst n; auto).
Solve Obligations using (apply lt_wf).

Lemma best_45 : forall n, mergesortc_best_time4 n = mergesortc_best_time5 n.
Proof.
  apply (well_founded_induction 
           lt_wf
           (fun n => mergesortc_best_time4 n = mergesortc_best_time5 n)).
  intros n INDn.
  destruct n.
  unfold_sub mergesortc_best_time4 (mergesortc_best_time4 0).
  unfold_sub mergesortc_best_time5 (mergesortc_best_time5 0).
  auto.
  destruct n.
  unfold_sub mergesortc_best_time4 (mergesortc_best_time4 1).
  fold mergesortc_best_time4.
  unfold_sub mergesortc_best_time5 (mergesortc_best_time5 1).
  unfold_sub mergesortc_best_time4 (mergesortc_best_time4 0).
  simpl.
  auto.
  unfold_sub mergesortc_best_time4 (mergesortc_best_time4 (S (S n))).
  fold mergesortc_best_time4.
  unfold_sub mergesortc_best_time5 (mergesortc_best_time5 (S (S n))).
  fold mergesortc_best_time5.
  repeat (rewrite INDn).
  auto.
  destruct n; auto.
  apply lt_n_S; auto.
Qed.

Program Fixpoint mergesortc_best_time6 n {measure n} :=
  match n with
    | 0 => 3
    | S n' => 
      match n' with
        | 0 => 28
        | S _ => 
          (split2_time (div2 n') +
           mergesortc_best_time6 (div2 n') +
           mergesortc_best_time6 (div2 n') +
           merge_best_time (div2 n') (div2 n') + 35)
      end
  end.
Solve Obligations using (intros; subst n; auto).
Solve Obligations using (apply lt_wf).

Lemma mergesortc_best_time5_monotonic :
  forall n, mergesortc_best_time5 n <= mergesortc_best_time5 (S n).
Proof.
  apply (well_founded_induction 
           lt_wf
           (fun n => mergesortc_best_time5 n <= mergesortc_best_time5 (S n))).
  intros n IND.
  destruct n.
  unfold_sub mergesortc_best_time5 (mergesortc_best_time5 0).
  unfold_sub mergesortc_best_time5 (mergesortc_best_time5 1).
  omega.
  unfold_sub mergesortc_best_time5 (mergesortc_best_time5 (S n)).
  fold mergesortc_best_time5.
  remember (S n) as m.
  unfold_sub mergesortc_best_time5 (mergesortc_best_time5 (S m)).
  fold mergesortc_best_time5.
  subst m.
  destruct n.
  simpl.
  omega.
  destruct (even_odd_dec (S (S (S n))));
  destruct (even_odd_dec (S (S n))).
  inversion e.
  assert False;[apply (not_even_and_odd (S (S n))); auto|intuition].
  clear e o.

  replace (split2_time (div2 (S n)) + 
           mergesortc_best_time5 (div2 (S n)) +
           mergesortc_best_time5 (div2 (S n)) +
           merge_best_time (div2 (S n)) (div2 (S n)) + 35 + 
           insert_best_time (S n) + 20)
  with (split2_time (div2 (S n)) + 
        merge_best_time (div2 (S n)) (div2 (S n)) + 35 + 
        insert_best_time (S n) + 20 +
        mergesortc_best_time5 (div2 (S n)) +
        mergesortc_best_time5 (div2 (S n)));[|omega].
  replace (split2_time (div2 (S (S (S n)))) + 
           mergesortc_best_time5 (S (div2 (S n))) +
           mergesortc_best_time5 (S (div2 (S n))) +
           merge_best_time (div2 (S (S (S n)))) (div2 (S (S (S n)))) + 35)
  with  (split2_time (div2 (S (S (S n)))) + 
         merge_best_time (div2 (S (S (S n)))) (div2 (S (S (S n)))) + 35 +
         mergesortc_best_time5 (S (div2 (S n))) +
         mergesortc_best_time5 (S (div2 (S n))));[|omega].
  apply plus_le_compat;[|apply IND;auto].
  apply plus_le_compat;[|apply IND;auto].

  clear IND.
  unfold split2_time.
  unfold merge_best_time.
  unfold insert_best_time.
  replace (div2 (S (S (S n)))) with (S (div2 (S n)));[|simpl;auto].
  rewrite min_same.
  rewrite min_same.
  omega.

  apply le_plus_trans.
  apply le_plus_trans.
  apply plus_le_compat; auto.

  inversion o.
  assert False;[apply (not_even_and_odd (S (S n))); auto|intuition].
Qed.

Lemma best_56 : big_oh mergesortc_best_time6 mergesortc_best_time5.
Proof.
  exists 0.
  exists 1.
  intros n _.
  rewrite mult_1_l.
  apply (well_founded_induction 
           lt_wf
           (fun n => mergesortc_best_time6 n <= mergesortc_best_time5 n)).
  clear n.
  intros n INDn.
  destruct n.
  unfold_sub mergesortc_best_time6 (mergesortc_best_time6 0).
  unfold_sub mergesortc_best_time5 (mergesortc_best_time5 0).
  omega.
  unfold_sub mergesortc_best_time6 (mergesortc_best_time6 (S n)).
  fold mergesortc_best_time6.
  unfold_sub mergesortc_best_time5 (mergesortc_best_time5 (S n)).
  fold mergesortc_best_time5.
  destruct n; auto.
  destruct (even_odd_dec (S (S n))).
  replace (div2 (S (S n))) with (S (div2 (S n)));[|apply odd_div2;inversion e;auto].
  replace (div2 (S n)) with (div2 n);
    [|apply even_div2;
       inversion e as [|XYZ ODD PDQ];
       inversion ODD;
       auto].

  apply plus_le_compat; [|omega].
  apply plus_le_compat.
  apply plus_le_compat.
  apply plus_le_compat.

  unfold split2_time.
  omega.

  apply (le_trans (mergesortc_best_time6 (div2 n))
                  (mergesortc_best_time5 (div2 n))).
  apply INDn.
  apply (lt_le_trans (div2 n) (S n)); auto.
  apply mergesortc_best_time5_monotonic.

  apply (le_trans (mergesortc_best_time6 (div2 n))
                  (mergesortc_best_time5 (div2 n))).
  apply INDn.
  apply (lt_le_trans (div2 n) (S n)); auto.
  apply mergesortc_best_time5_monotonic.

  unfold merge_best_time.
  rewrite min_same.
  rewrite min_same.
  omega.

  apply le_plus_trans.
  apply le_plus_trans.
  apply plus_le_compat; auto.
  apply plus_le_compat; auto.
  apply plus_le_compat; [|apply INDn;auto].
  apply plus_le_compat; [|apply INDn;auto].
  auto.
Qed.

Program Fixpoint mergesortc_best_time7 n {measure n} :=
  match n with
    | 0 => 0
    | S n' => 
      match n' with
        | 0 => 0
        | S _ => 
          (mergesortc_best_time7 (div2 n') +
           mergesortc_best_time7 (div2 n') +
           n)
      end
  end.
Solve Obligations using (intros; subst n; auto).
Solve Obligations using (apply lt_wf).

Lemma best_67 : big_oh mergesortc_best_time7 mergesortc_best_time6.
Proof.
  exists 1 3.
  intros n LT.
  destruct n. intuition.
  clear LT.
  apply (well_founded_induction
           lt_wf
           (fun n =>  mergesortc_best_time7 (S n) <= 3 * mergesortc_best_time6 (S n))).
  clear n.
  intros n IND.
  unfold_sub mergesortc_best_time7 (mergesortc_best_time7 (S n)).
  fold mergesortc_best_time7.
  unfold_sub mergesortc_best_time6 (mergesortc_best_time6 (S n)).
  fold mergesortc_best_time6.
  destruct n.
  omega.
  unfold split2_time, merge_best_time.
  rewrite min_same.
  repeat (rewrite mult_plus_distr_l).
  repeat (rewrite plus_assoc).
  replace (3 * (15 * div2 (S n)) + 
           3 * 5 + 
           3 * mergesortc_best_time6 (div2 (S n)) +
           3 * mergesortc_best_time6 (div2 (S n)) + 
           3 * (17 * div2 (S n)) + 
           3 * 3 + 
           3 * 35)
  with (3 * mergesortc_best_time6 (div2 (S n)) +
        3 * mergesortc_best_time6 (div2 (S n)) + 
        ((2+94) * div2 (S n) +
         129));[|omega].
  apply plus_le_compat.
  
  remember (div2 (S n)) as m.
  destruct m.
  program_simpl.
  unfold_sub mergesortc_best_time7 (mergesortc_best_time7 0).
  omega.

  apply plus_le_compat;apply IND;
  apply lt_S_n;
  rewrite Heqm;
  auto.

  replace (S (S n)) with (n+2);[|omega].
  rewrite mult_plus_distr_r.
  replace (2 * div2 (S n) + 94 * div2 (S n) + 129)
  with (2 * div2 (S n) + (94 * div2 (S n) + 129));[|omega].
  apply plus_le_compat;[|omega].
  
  unfold mult; rewrite plus_0_r.
  replace (div2 (S n) + div2 (S n)) with (double (div2 (S n)));[|unfold double;auto].
  destruct (even_odd_dec (S n)).

  rewrite <- even_double; auto.
  inversion o.
  rewrite <- even_div2; auto.
  rewrite <- even_double; auto.
Qed.

Lemma fl_log_growth_limited : 
  forall n:nat, 
    fl_log (n + 5) <= fl_log (n + 3) + 1.
Proof.
  apply (well_founded_ind
           lt_wf
           (fun n => fl_log (n + 5) <= fl_log (n + 3) + 1)).
  intros n IND.
  destruct n.
  program_simpl.
  destruct n.
  program_simpl.
  destruct n.
  program_simpl.
  destruct n.
  program_simpl.
  destruct n.
  program_simpl.
  destruct n.
  program_simpl.
  replace (S (S (S (S (S (S n))))) + 5) with (S (n+10));[|omega].
  rewrite fl_log_div2'.
  replace (div2 (n+10)) with (div2 n + 5);
    [|(replace (n+10) with (10+n);[|omega]);
       simpl; omega].
  apply (le_trans (S (fl_log (div2 n + 5)))
                  (S (fl_log (div2 n + 3) +1))).
  apply le_n_S.
  apply IND.
  apply (lt_le_trans (div2 n) (S n));auto.
  omega.
  replace (S (fl_log (div2 n + 3) + 1))
  with (fl_log (div2 n + 3) + 2);[|omega].
  replace (S (S (S (S (S (S n))))) + 3)
  with (S ((S (S (S (S (S n))))) + 3));[|omega].
  rewrite fl_log_div2'.
  replace (S (fl_log (div2 (S (S (S (S (S n)))) + 3))) + 1)
  with (fl_log (div2 (S (S (S (S (S n)))) + 3)) + 2);[|omega].
  apply plus_le_compat;auto.
  apply fl_log_monotone.
  replace (S (S (S (S (S n)))) + 3) with (S (S (S (S (S (S (n+2)))))));[|omega].
  replace (div2 (S (S (S (S (S (S (n + 2)))))))) 
  with (div2 (n+2) + 3);[|simpl;auto].
  apply plus_le_compat;auto.
  apply div2_monotone; omega.
  omega.
Qed.

Lemma strange_fact : 
  forall n,
    odd n -> 
    S (S (div2 n)) * cl_log (S (S (div2 (S n)))) + cl_log (S (S (div2 (S n)))) <=
    S (S (div2 n)) * cl_log (S (S (div2 n))) + n + 5.
Proof.
  intros n OD.
  repeat (rewrite <- fl_log_cl_log_relationship).
  rewrite <- odd_div2; auto.
  replace (S (S (div2 n))) with (div2 (S (S (S (S n)))));[|unfold div2;auto].
  replace (S (div2 n)) with (div2 (S (S n)));[|unfold div2;auto].
  repeat (rewrite <- fl_log_div2').
  replace (S (S (S (S (S n))))) with (n+5);[|omega].
  replace (S (S (S (S n)))) with (n+4);[|omega].
  replace (S (S (S n))) with (n+3);[|omega].
  apply (le_trans (div2 (n + 4) * fl_log (n + 5) + fl_log (n + 5))
                  (div2 (n + 4) * (fl_log (n + 3) + 1) + fl_log (n + 5))).
  apply plus_le_compat;auto.
  apply mult_le_compat;auto.
  apply fl_log_growth_limited.
  
  rewrite mult_plus_distr_l.
  rewrite mult_1_r.
  rewrite (odd_double n) at 7; auto.
  unfold double.
  replace (div2 (n+4)) with (div2 n + 2);
    [|(replace (n+4) with (S (S (S (S n))));[|omega]);
       simpl;
       omega].
  replace ((div2 n + 2) * fl_log (n + 3) +
           S (div2 n + div2 n) + 5)
  with ((div2 n + 2) * fl_log (n + 3) +
        (div2 n + 2) + (div2 n + 4));[|omega].
  apply plus_le_compat;auto.
  apply (well_founded_induction 
           lt_wf
           (fun n => fl_log (n+5) <= div2 n + 4)).
  clear n OD.
  intros n IND.
  destruct n.
  program_simpl.
  destruct n.
  program_simpl.
  simpl div2.
  apply (le_trans (fl_log (S (S n) + 5))
                  (S (fl_log (n + 5)))).
  replace (S (S n) + 5) with (S (n+6));[|omega].
  rewrite fl_log_div2'.
  apply le_n_S.
  apply fl_log_monotone.
  replace (n+6) with (6+n);[|omega].
  replace (div2 (6+n)) with (div2 n + 3);[|simpl;omega].
  apply plus_le_compat;auto.
  clear IND.
  apply (ind_0_1_SS (fun n => div2 n <= n));
    (intros ;simpl; omega).
  replace (S (div2 n) + 4) with (S (div2 n + 4));[|omega].
  apply le_n_S.
  apply IND;auto.
Qed.

Lemma best7_nlogn : big_oh (fun n => n * cl_log n) mergesortc_best_time7.
Proof.
  exists 2.
  exists 3.
  intros n LT.
  destruct n. intuition.
  destruct n. intuition.
  clear LT.
  apply (well_founded_induction
           lt_wf
           (fun n => (S (S n)) * cl_log (S (S n)) <= 3 * mergesortc_best_time7 (S (S n)))).
  clear n; intros n IND.
  unfold_sub mergesortc_best_time7 (mergesortc_best_time7 (S (S n))).
  destruct n.
  program_simpl.
  remember (div2 n) as m.
  destruct m.
  unfold_sub mergesortc_best_time7 (mergesortc_best_time7 1).
  destruct n.
  program_simpl.
  destruct n.
  compute.
  omega.
  simpl in Heqm.
  intuition.

  rewrite cl_log_div2'.
  replace (div2 (S (S (S n)))) with (S (div2 (S n)));[|unfold div2;auto].

  destruct n.
  unfold div2 in Heqm; intuition.
  destruct n.
  unfold div2 in Heqm; intuition.
  simpl in Heqm.
  assert (m = div2 n);[omega|subst m; clear Heqm].

  replace (div2 (S (S (S n)))) with (S (div2 (S n)));[|unfold div2;auto].

  destruct (even_odd_dec n).

  (* even case *)
  replace n with (double (div2 n)) at 1;[|rewrite even_double;auto].
  unfold double.
  rewrite odd_div2;[|constructor;auto].
  replace (div2 (S (S n))) with (S (div2 n));[|unfold div2;auto].
  replace (S (S (S (S (S (div2 n + div2 n)))))) 
  with ((S (S (div2 n))) + (S (S (div2 n))) + 1);[|omega].
  replace (S (cl_log (S (S (div2 n))))) with ((cl_log (S (S (div2 n))))+1);[|omega].
  repeat (rewrite mult_plus_distr_l).
  repeat (rewrite mult_plus_distr_r).
  repeat (rewrite mult_1_r).
  repeat (rewrite mult_1_l).

  replace (S (S (div2 n)) * cl_log (S (S (div2 n))) +
           S (S (div2 n)) * cl_log (S (S (div2 n))) + cl_log (S (S (div2 n))) +
           (S (S (div2 n)) + S (S (div2 n)) + 1))
  with (S (S (div2 n)) * cl_log (S (S (div2 n))) +
        S (S (div2 n)) * cl_log (S (S (div2 n))) + 
        (cl_log (S (S (div2 n))) + (S (S (div2 n)) + S (S (div2 n)) + 1)));[|omega].
  apply plus_le_compat.

  apply plus_le_compat; 
    apply IND;
    apply (lt_le_trans (div2 n) (S n)); auto.
  
  replace (3 * S (S (S (S (S n))))) with (2*n+10+n+5);[|omega].
  replace (cl_log (S (S (div2 n))) + (S (S (div2 n)) + S (S (div2 n)) + 1))
  with (cl_log (S (S (div2 n))) + ((div2 n) + (div2 n)) + 5);[|omega].
  replace (div2 n + div2 n) with (double (div2 n));[|unfold double;auto].
  rewrite <- even_double; auto.
  apply plus_le_compat;auto.
  apply plus_le_compat;auto.

  rewrite <- fl_log_cl_log_relationship.
  apply (le_trans (S (fl_log (S (div2 n))))
                  (S (S (div2 n)))).
  apply le_n_S.
  apply fl_log_decr.
  apply (le_trans (S (S (div2 n))) (S (S n))).
  apply le_n_S.
  apply le_n_S.
  apply div2_le.
  omega.

  (* odd case *)
  replace n with (S (double (div2 n))) at 1;[|rewrite odd_double;auto].
  unfold double.
  replace (S (S (S (S (S (S (div2 n + div2 n)))))))
  with ((S (S (div2 n))) + (S (S (div2 n))) + 2);[|omega].
  replace (S (cl_log (S (S (div2 (S n)))))) 
  with ((cl_log (S (S (div2 (S n))))) + 1) ;[|omega].
  repeat (rewrite mult_plus_distr_r).
  repeat (rewrite mult_plus_distr_l).
  repeat (rewrite plus_assoc).
  repeat (rewrite mult_1_r).
  replace ( S (S (div2 n)) * cl_log (S (S (div2 (S n)))) +
            S (S (div2 n)) +
            S (S (div2 n)) * cl_log (S (S (div2 (S n)))) + 
            S (S (div2 n)) +
            2 * cl_log (S (S (div2 (S n)))) + 2)
  with (S (S (div2 n)) * cl_log (S (S (div2 (S n)))) + 
        S (S (div2 n)) * cl_log (S (S (div2 (S n)))) + 
        2 * cl_log (S (S (div2 (S n)))) + 5 +
        (S ((div2 n) + (div2 n))));[|omega].
  replace ((div2 n) + (div2 n)) with (double (div2 n));[|unfold double;auto].
  rewrite <- odd_double; auto.
  replace (3 * S (S (S (S (S n))))) with (2*n + 10 + 5 + n);[|omega].
  repeat (rewrite plus_assoc).
  apply plus_le_compat;auto.
  apply plus_le_compat;auto.

  replace (3 * mergesortc_best_time7 (S (S (div2 n))) +
           3 * mergesortc_best_time7 (S (S (div2 n))) + 2 * n + 10)
  with ((3 * mergesortc_best_time7 (S (S (div2 n))) + n + 5) +
        (3 * mergesortc_best_time7 (S (S (div2 n))) + n + 5));[|omega].
  replace (S (S (div2 n)) * cl_log (S (S (div2 (S n)))) +
           S (S (div2 n)) * cl_log (S (S (div2 (S n)))) +
           2 * cl_log (S (S (div2 (S n)))))
  with ((S (S (div2 n)) * cl_log (S (S (div2 (S n)))) + 
         cl_log (S (S (div2 (S n))))) +
        (S (S (div2 n)) * cl_log (S (S (div2 (S n)))) +
         cl_log (S (S (div2 (S n))))));[|omega].
  apply plus_le_compat;
    (apply (le_trans (S (S (div2 n)) * cl_log (S (S (div2 (S n)))) + 
                      cl_log (S (S (div2 (S n)))))
                     (S (S (div2 n)) * cl_log (S (S (div2 n))) + n + 5));
     [apply strange_fact; auto|
      (apply plus_le_compat;auto);
        (apply plus_le_compat;auto);
        apply IND;
        apply (lt_le_trans (div2 n) (S n)); auto]).
Qed.
  
Lemma mergesortc_worst:
  big_oh mergesortc_worst_time (fun n => n * cl_log n).
Proof.
  apply (big_oh_trans mergesortc_worst_time
                      mergesortc_worst_time5
                      (fun n => n * cl_log n)).
  exists 0.
  exists 1.
  intros n _.
  unfold mult; rewrite plus_0_r.
  rewrite worst_12.
  rewrite worst_23.
  rewrite worst_34.
  rewrite worst_45.
  omega.
  apply (big_oh_trans mergesortc_worst_time5
                      mergesortc_worst_time6
                      (fun n => n * cl_log n)).
  apply worst_56.
  apply (big_oh_trans mergesortc_worst_time6
                      mergesortc_worst_time7
                      (fun n => n * cl_log n)).
  apply worst_67.
  apply (big_oh_trans mergesortc_worst_time7
                      mergesortc_worst_time8
                      (fun n => n * cl_log n)).
  apply worst_78.
  apply worst_89.
Qed.

Lemma mergesortc_best : 
  big_oh (fun n => n * cl_log n) mergesortc_best_time.
Proof.
  apply (big_oh_trans (fun n => n * cl_log n)
                      mergesortc_best_time7).
  apply best7_nlogn.
  apply (big_oh_trans mergesortc_best_time7 mergesortc_best_time6).
  apply best_67.
  apply (big_oh_trans mergesortc_best_time6 mergesortc_best_time5).
  apply best_56.
  exists 0.
  exists 1.
  intros n _.
  rewrite mult_1_l.
  rewrite <- best_45.
  rewrite <- best_34.
  rewrite <- best_23.
  rewrite <- best_12.
  auto.
Qed.

Definition mergesort_best_time (n:nat) :=
  clength_time n + mergesortc_best_time n + 10.
Definition mergesort_worst_time (n:nat) :=
  clength_time n + mergesortc_worst_time n + 10.
Hint Unfold mergesort_best_time mergesort_worst_time.

Definition mergesort_result
           (A:Set) (A_cmp:A -> A -> Prop)
           (A_cmp_trans:Transitive A_cmp) (A_cmp_total:Total A_cmp)
           (A_cmp_dec:DecCmp A_cmp) (l:list A) (res:list A) (c:nat) :=
  (SortedOf A_cmp l res) /\
  mergesort_best_time (length l) <= c /\
  c <= mergesort_worst_time (length l).

Load "mergesort_gen.v".

Next Obligation.
Proof.
  program_simpl.
  unfold clength_result in *.
  omega.
Qed.

Next Obligation.
Proof.
  unfold mergesort_result.
  unfold mergesortc_result.
  intros A A_cmp A_cmp_trans A_cmp_total A_cmp_dec l len CLENGTHRES res _.
  intros Nmsc [SOres [SORTED TIME]].
  intros Nlen [EQlen LEN_P].
  subst len. subst Nlen.
  split. auto.
  remember (length l) as L.
  clear CLENGTHRES SORTED A A_cmp A_cmp_trans A_cmp_total A_cmp_dec res l HeqL.
  unfold mergesort_best_time, mergesort_worst_time in *.
  omega.
Qed.

Theorem mergesort_worst :
  big_oh mergesort_worst_time (fun n => n * cl_log n).
Proof.
  apply big_oh_plus.
  apply big_oh_plus.
  apply big_oh_plus.
  
  exists 2.
  exists 7.
  intros n LT.
  destruct n. intuition.
  destruct n. intuition.

  apply mult_le_compat; auto.
  unfold_sub cl_log (cl_log (S (S n))).
  replace (S (S n)) with (S (S n) * 1) at 1;[|omega].
  apply mult_le_compat; auto.
  omega.

  apply big_oh_k___nlogn.
  apply mergesortc_worst.
  apply big_oh_k___nlogn.
Qed.

Theorem mergesort_best_rev:
  big_oh (fun n => n * cl_log n) mergesort_best_time.
Proof.
  apply (big_oh_trans (fun n => n * cl_log n) mergesortc_best_time).
  apply mergesortc_best.
  exists 0.
  exists 1.
  intros n _.
  rewrite mult_1_l.
  unfold mergesort_best_time.
  omega.
Qed.  

Theorem mergesort_best:
  big_omega mergesort_best_time (fun n => n * cl_log n).
Proof.
  apply big_oh_rev.
  apply mergesort_best_rev.
Qed.

Theorem mergesort_running_time:
  forall f,
    (forall n, mergesort_best_time n <= f n <= mergesort_worst_time n) ->
    big_theta f (fun n => n * cl_log n).
Proof.
  intros f ASS.
  split.
  apply (big_oh_trans f mergesort_worst_time);[|apply mergesort_worst].
  exists 0.
  exists 1.
  intros n _.
  rewrite mult_1_l.
  remember (ASS n).
  omega.

  apply big_oh_rev.
  apply (big_oh_trans (fun n : nat => n * cl_log n) mergesort_best_time).
  apply mergesort_best_rev.
  exists 0.
  exists 1.
  intros n _.
  rewrite mult_1_l.
  remember (ASS n).
  omega.
Qed.
