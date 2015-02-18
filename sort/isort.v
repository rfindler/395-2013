Require Import Braun.common.util Braun.common.same_structure.
Require Import Braun.common.log Braun.common.big_oh.
Require Import Braun.common.sequence Braun.common.list_util.
Require Import Braun.monad.monad.
Require Import Program.
Require Import Omega.
Require Import List Relations_1.
Require Import Sorting.Sorted Sorting.Permutation.
Require Import Braun.sort.sorting.

Definition insert_best_time (n:nat) := 5.
Definition insert_worst_time (n:nat) := 15 * n + 9.

Definition insert_result 
  (A:Set) (A_cmp:A -> A -> Prop)
  (A_cmp_trans:Transitive A_cmp) (A_cmp_total:Total A_cmp)
  (A_cmp_dec:DecCmp A_cmp) (a:A) (l:list A)
  (res:list A) (c:nat):=
  (IsSorted A_cmp l) ->
  (SortedOf A_cmp (cons a l) res) /\
  insert_best_time (length l) <= c /\
  c <= insert_worst_time (length l).

Load "insert_gen.v".

Next Obligation.
  unfold insert_result.
  intro IS.
  split.
  unfold SortedOf. unfold IsSorted.
  split. apply Permutation_refl.
  eapply SSorted_cons.
  auto. apply Forall_forall.
  intros x. simpl. intuition.
  unfold insert_best_time, insert_worst_time.
  omega.
Qed.

Next Obligation.
  unfold insert_result.
  intro IS.
  rename wildcard' into CMP.
  clear Heq_anonymous.
  split.

  unfold SortedOf. split. apply Permutation_refl.
  unfold IsSorted in *.
  eapply SSorted_cons. auto.
  apply Forall_forall.
  intros x. simpl. intros [EQ | IN].
  subst x. auto.
  apply StronglySorted_inv in IS.
  destruct IS as [SS IS].
  eapply A_cmp_trans. apply CMP.
  rewrite Forall_forall in IS.
  apply IS. auto.

  unfold insert_best_time, insert_worst_time.
  omega.
Qed.

Next Obligation.
  unfold insert_result.
  intros IS.
  rename wildcard' into CMP.
  clear Heq_anonymous.
  rename H0 into IH.
  clear H1 am.

  assert (IsSorted A_cmp l') as IS'.
  clear IH. unfold IsSorted in *.
  apply StronglySorted_inv in IS.
  destruct IS.
  auto.

  destruct (IH IS') as [SO [OM OH]].
  clear IH.
  split.

  unfold SortedOf. split.
  unfold SortedOf in SO.
  destruct SO as [PM IS''].
  apply Permutation_cons_step. auto.

  unfold SortedOf in SO.
  unfold IsSorted in *.
  destruct SO as [PM IS''].
  eapply SSorted_cons. auto.
  apply Forall_forall.
  intros x IN.

  apply StronglySorted_inv in IS.
  destruct IS as [IS F]. clear IS'.
  rewrite Forall_forall in F.

  destruct res' as [|y res'].
  simpl in IN. contradiction.
  apply StronglySorted_inv in IS''.
  destruct IS'' as [IS'' F'].
  rewrite Forall_forall in F'.

  eapply Permutation_in in IN.
  Focus 2.
   apply Permutation_sym. apply PM.
  simpl in IN. destruct IN as [EQ | IN].
  subst x.
  apply A_cmp_total. apply CMP.
  auto.

  unfold insert_best_time, insert_worst_time in *.
  replace (length (a' :: l')) with (S (length l')); auto.
  omega.
Qed.

Definition isort_best_time (n:nat) := 14 * n + (insert_best_time n) * n + 3.
Definition isort_worst_time (n:nat) := 14 * n + (insert_worst_time n) * n + 3.

Definition isort_result (A:Set) (A_cmp:A -> A -> Prop)
  (A_cmp_trans:Transitive A_cmp) (A_cmp_total:Total A_cmp)
  (A_cmp_dec:DecCmp A_cmp)
  (l:list A) (res : list A) (c : nat) :=
    (SortedOf A_cmp l res) /\
    (isort_best_time (length l)) <= c /\
    c <= (isort_worst_time (length l)).

Load "isort_gen.v".

Next Obligation.  
 split. 
 split. auto. 
 apply SSorted_nil.
 unfold isort_best_time, isort_worst_time in *.
 unfold insert_best_time, insert_worst_time.
 simpl.
 omega.
Defined.

Local Obligation Tactic := idtac.

Next Obligation.
  unfold isort_result.
  unfold isort_best_time, isort_worst_time in *.
  intros A A_cmp A_cmp_trans A_cmp_total A_cmp_dec.
  intros l a d EQl d' _ r' _ xm EQxm.
  simpl in EQxm.
  subst xm.
  intros an INSERT_P.
  intros am REC_P.

  destruct REC_P as [SOd' REC_P].
  unfold SortedOf in *.
  destruct SOd' as [PMdd' ISd'].
  edestruct INSERT_P as [SO [OM OH]]; clear INSERT_P.
  auto.
  destruct SO as [PMad'r' ISr']. 
  split. split; auto.
  apply Permutation_sym.
  eapply Permutation_trans.
  apply Permutation_sym.
  apply PMad'r'.
  apply perm_skip.
  apply Permutation_sym.
  apply PMdd'.

  apply Permutation_length in PMdd'.
  rewrite <- PMdd' in *.
  clear PMdd' ISd' PMad'r' ISr'.
  simpl.
  remember (length d) as L.
  clear A A_cmp A_cmp_trans A_cmp_total A_cmp_dec a d d' r' HeqL l EQl.

  unfold insert_best_time,insert_worst_time in *.
  split; [omega|].
  assert (forall n, S (L + n) = 1 + L + n) as CLEAN;
    [intros;omega|repeat (rewrite CLEAN); clear CLEAN].
  replace (S L) with (L+1);[|omega].
  repeat (rewrite plus_assoc).
  replace (L + 1 + L + 1 + L + 1 + L + 1 + L + 1 + L + 1 + L + 1 + L + 1 + L + 1 +
           L + 1 + L + 1 + L + 1 + L + 1 + L + 0 + 1 + L +
           (L + 1 + L + 1 + L + 1 + L + 1 + L + 1 + L + 1 + L + 1 + L + 1 + L + 1 +
            L + 1 + L + 1 + L + 1 + L + 1 + L + 1 + L + 0 + 9) * 
           S L + 3)
  with (15 * L + 17 +
        (L + 1 + L + 1 + L + 1 + L + 1 + L + 1 + L + 1 + L + 1 + L + 1 + L + 1 +
         L + 1 + L + 1 + L + 1 + L + 1 + L + 1 + L + 0 + 9) * 
        S L);[|omega].
  replace (L + 1 + L + 1 + L + 1 + L + 1 + L + 1 + L + 1 + L + 1 + L + 1 + L + 1 +
           L + 1 + L + 1 + L + 1 + L + 1 + L + 1 + L + 0 + 9)
  with (15 * L + 23);[|omega].
  replace (S (15 * L + 17 + (15 * L + 23) * S L)) 
  with (15 * L + 18 + (15 * L + 23) * (S L));[|omega].
  apply (le_trans (am + an + 14)
                  (14 * L + (15 * L + 9) * L + 3
                   + 15 * L + 9 + 14));[omega|].
  replace (S L) with (L+1);[|omega].
  repeat (rewrite mult_plus_distr_l).
  repeat (rewrite mult_plus_distr_r).
  omega.
Qed.

Definition isort_worst_time2 (n:nat) := n + (insert_worst_time n) * n + 3.
Lemma isort_worst_12 : big_oh isort_worst_time isort_worst_time2.
Proof.
  exists 1.
  exists 14.
  intros n LT.
  destruct n.
  intuition.
  clear LT.
  unfold isort_worst_time, isort_worst_time2.
  rewrite mult_plus_distr_l.
  rewrite mult_plus_distr_l.
  apply plus_le_compat;try omega.
  apply plus_le_compat;try omega.
  rewrite mult_assoc.
  apply mult_le_compat; omega.
Qed.

Definition isort_worst_time3(n:nat) := n*n+n+1.
Lemma isort_worst_23 : big_oh isort_worst_time2 isort_worst_time3.
Proof.
  exists 1.
  unfold isort_worst_time2, isort_worst_time3, insert_worst_time.
  exists 15.
  intros n LT.
  destruct n.
  intuition.
  clear LT.
  replace (S n) with (n+1);[|omega].
  repeat (rewrite mult_plus_distr_r).
  repeat (rewrite mult_plus_distr_l).
  repeat (rewrite mult_plus_distr_r).
  repeat (rewrite plus_assoc).
  repeat (rewrite mult_1_r).
  repeat (rewrite mult_1_l).
  rewrite mult_assoc.
  omega.
Qed.

Definition isort_worst_time4 (n:nat) := n*n.
Lemma isort_worst_34 : big_oh isort_worst_time3 isort_worst_time4.
Proof.
  exists 1.
  exists 3.
  intros n LT.
  destruct n.
  intuition.
  clear LT.
  unfold isort_worst_time3, isort_worst_time4.
  replace (S n) with (n+1);[|omega].
  repeat (rewrite mult_plus_distr_r).
  repeat (rewrite mult_plus_distr_l).
  repeat (rewrite plus_assoc).
  repeat (rewrite mult_1_r).
  repeat (rewrite mult_1_l).
  rewrite mult_assoc.
  replace (n * n + n + n + 1 + n + 1 + 1) with (n * n + 3*n + 3);[|omega].
  replace (3 * n * n + 3 * n + 3 * n + 3) with (3 * n * n + 6 * n + 3);[|omega].
  apply plus_le_compat;[|omega].
  apply plus_le_compat;[|omega].
  apply mult_le_compat;omega.
Qed.

Theorem isort_is_nsquared : big_oh isort_worst_time (fun n => n * n).
Proof.
  apply (big_oh_trans isort_worst_time isort_worst_time2).
  apply isort_worst_12.
  apply (big_oh_trans isort_worst_time2 isort_worst_time3).
  apply isort_worst_23.
  apply isort_worst_34.
Qed.
