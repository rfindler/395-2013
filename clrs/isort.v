Require Import Braun.common.util Braun.common.same_structure.
Require Import Braun.common.log Braun.common.big_oh.
Require Import Braun.common.sequence Braun.common.list_util.
Require Import Braun.monad.monad.
Require Import Program.
Require Import Omega.
Require Import List Relations_1.
Require Import Sorting.Sorted Sorting.Permutation.
Require Import Braun.clrs.sorting.

Program Fixpoint insert
  {A:Set} {A_cmp:A -> A -> Prop}
  (A_cmp_trans:Transitive A_cmp) (A_cmp_total:Total A_cmp)
  (A_cmp_dec:DecCmp A_cmp) (a:A) (l:list A)
  : {! res !:! list A !<! c !>!
    (IsSorted A_cmp l) ->
    (SortedOf A_cmp (cons a l) res) /\
    (exists k_0, k_0 > 0 /\ k_0 <= c) /\
    (exists k_2, k_2 > 0 /\ c <= (length l) + k_2) !} :=
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
  split.
  exists 1. omega.
  exists 1. omega.
Defined.

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

  split.

  exists 2. omega.
  exists 2. omega.
Defined.

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
  destruct OM as [n_0 OM].
  destruct OH as [n_1 OH].
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

  destruct OM as [OM_n OM_k].
  rename n_0 into k_0.
  rename n_1 into k_1.
  destruct OH as [OH_k1 OH_k].
  split.
  exists k_0. omega.

  exists (k_1 + 2).
  repeat split; try omega.
Defined.
  
Program Fixpoint isort {A:Set} {A_cmp:A -> A -> Prop}
  (A_cmp_trans:Transitive A_cmp) (A_cmp_total:Total A_cmp)
  (A_cmp_dec:DecCmp A_cmp)
  (l:list A)
  : {! res !:! list A !<! c !>!
    (SortedOf A_cmp l res) /\
    (exists k_1, k_1 > 0 /\ (length l) + k_1 <= c) /\
    (exists k_4, k_4 > 0 /\ c <= (length l) * (length l) + k_4) !} :=
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
 split.
 exists 1. omega.
 exists 1. omega.
Defined.

Next Obligation.
 clear am H15 H13.
 clear am0 H8.
 clear H9.
 clear H10 H14.
 clear H11 H12.
 rename an0 into am.
 rename H1 into SOd'.
 rename H0 into INSERT_P.
 rename H7 into GEam.
 rename H5 into LEam.
 rename H2 into k_1.
 rename H3 into k_4.
 rename H6 into NZk_1.
 rename H4 into NZk_4.

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
 destruct OM as [k_5 [NZk_5 GEan]].
 destruct OH as [k_7 [NZk_7 LEan]].
 clear PMdd' ISd' PMad'r' ISr'.
 remember (length d) as LEN.
 clear A A_cmp A_cmp_trans A_cmp_total A_cmp_dec a d d' r' HeqLEN.
 split.

 exists (k_1 + k_5).
 repeat split; try omega.

 exists (k_4 + k_7).
 repeat split; try omega.
 rewrite mult_succ_r.
 omega.
Defined.
