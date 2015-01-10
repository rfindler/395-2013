Require Import Braun.common.util Braun.common.same_structure.
Require Import Braun.common.log Braun.common.big_oh.
Require Import Braun.common.sequence Braun.common.list_util.
Require Import Braun.monad.monad.
Require Import Program.
Require Import Omega.
Require Import List Relations_1.
Require Import Sorting.Sorted Sorting.Permutation.
Require Import Braun.clrs.sorting.

Definition insert_best_time (n:nat) := 1.
Definition insert_worst_time (n:nat) := 2 * n + 1.
Hint Unfold insert_best_time insert_worst_time.

Program Fixpoint insert
  {A:Set} {A_cmp:A -> A -> Prop}
  (A_cmp_trans:Transitive A_cmp) (A_cmp_total:Total A_cmp)
  (A_cmp_dec:DecCmp A_cmp) (a:A) (l:list A)
  : {! res !:! list A !<! c !>!
    (IsSorted A_cmp l) ->
    (SortedOf A_cmp (cons a l) res) /\
    insert_best_time (length l) <= c /\
    c <= insert_worst_time (length l) !} :=
  match l with
    | nil =>
      += 1;
      <== (cons a nil)
    | cons a' l' =>
      match A_cmp_dec a a' with
        | left _ =>
          += 2;
          <== (cons a l)
        | right _ =>
          res' <- (insert A_cmp_trans A_cmp_total A_cmp_dec a l');
          += 2;
          <== (cons a' res')
      end
  end.

Next Obligation.
  rename H0 into IS.
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
  rename wildcard' into CMP.
  clear Heq_anonymous.
  rename H0 into IS.
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
  rename wildcard' into CMP.
  clear Heq_anonymous.
  rename H0 into IH.
  clear H2 am.
  rename H1 into IS.

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
  omega.
Qed.

Definition isort_best_time (n:nat) := n * (insert_best_time n) + 1.
Definition isort_worst_time (n:nat) := n * (insert_worst_time n) + 1.
Hint Unfold isort_best_time isort_worst_time.

Program Fixpoint isort {A:Set} {A_cmp:A -> A -> Prop}
  (A_cmp_trans:Transitive A_cmp) (A_cmp_total:Total A_cmp)
  (A_cmp_dec:DecCmp A_cmp)
  (l:list A)
  : {! res !:! list A !<! c !>!
    (SortedOf A_cmp l res) /\
    (isort_best_time (length l)) <= c /\
    c <= (isort_worst_time (length l)) !} :=
  match l with
    | nil =>
      += 1;
      <== nil
    | cons a d =>
      d' <- isort A_cmp_trans A_cmp_total A_cmp_dec d;
      r' <- insert A_cmp_trans A_cmp_total A_cmp_dec a d';
      += 1;
      <== r'
  end.

Next Obligation.  
 split. 
 split. auto. 
 apply SSorted_nil.
 unfold isort_best_time, isort_worst_time in *.
 omega.
Defined.

Local Obligation Tactic := idtac.

Next Obligation.
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

  unfold insert_best_time, insert_worst_time in *.
  simpl in *.
  rewrite plus_0_r in *.
  rewrite mult_1_r in *.
  split. omega.
  clear OM.  
  destruct REC_P as [_ REC_OH].
  replace (L + L + 1) with (S (L + L)) in *; try omega.
  replace (L + S L + 1) with (S (S (L + L))) in *; try omega.
  rewrite plus_succ_r in *.
  rewrite plus_succ_r.
  repeat rewrite mult_succ_r in *.
  omega.
Qed.
