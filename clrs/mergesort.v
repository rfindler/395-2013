Require Import Braun.common.util Braun.common.same_structure.
Require Import Braun.common.log Braun.common.big_oh.
Require Import Braun.common.sequence Braun.common.list_util.
Require Import Braun.monad.monad.
Require Import Program.
Require Import Omega.
Require Import List Relations_1.
Require Import Sorting.Sorted Sorting.Permutation.
Require Import Braun.clrs.sorting.
Require Import Min.
Require Import Div2.
Require Import Even.

Program Fixpoint clength {A:Set} (l:list A)
  : {! res !:! nat !<! c !>!
    res = length l /\
    c = length l + 1 !}
  :=
  match l with
    | nil =>
      += 1;
      <== 0
    | cons _ l' =>
      n' <- clength l' ;
      += 1 ;
      <== 1 + n'
  end.

Next Obligation.
  omega.
Qed.

Program Fixpoint split_at {A:Set} (n:nat) (l:list A)
  : {! res !:! ((list A)*(list A)) !<! c !>!
    l = (fst res) ++ (snd res) /\
    length (fst res) = min n (length l) /\
    (exists k_0, 2 * (length (fst res)) + k_0 <= c) /\
    (exists k_1, c <= 2 * (length (fst res)) + k_1) !}
  :=
  match n with
    | O =>
      += 1;
      <== (nil, l)
    | S n' =>
      match l with
        | nil =>
          += 2;
          <== (nil, nil)
        | cons a l' =>
          res <- split_at n' l' ;
          += 2;
          <== (cons a (fst res), (snd res))
      end
  end.

Next Obligation.
  repeat split; auto.
  exists 1. omega.
  exists 1. omega.
Qed.

Next Obligation.
  repeat split; auto.
  exists 1. omega.
  exists 2. omega.
Qed.

Next Obligation.
  split. auto.
  simpl in *.
  rename l0 into bs.
  rename l1 into cs.
  clear am H11 H10.
  clear H0. clear H1.
  rename H7 into EQlenbs.
  rewrite <- EQlenbs.
  clear EQlenbs.
  rename H2 into k_0.
  rename H5 into LEan.
  rename H4 into GEan.
  rename H3 into k_1.
  clear H8 H9.
  split. auto.
  split.

  exists k_0. omega.
  exists k_1. omega.
Qed.

Lemma min_div2:
  forall L,
    min (div2 L) L = (div2 L).
Proof.
  intros L.
  apply min_l.
  generalize L. clear L.
  apply ind_0_1_SS; simpl.

  auto. auto.
  intros L IH.
  omega.
Qed.

Program Fixpoint split_evenly {A:Set} (l:list A)
  : {! res !:! ((list A)*(list A)) !<! c !>!
    l = (fst res) ++ (snd res) /\
    length (fst res) = div2 (length l) /\
    (length (snd res) = div2 (length l) \/
      length (snd res) = div2 (length l) + 1) /\
    (exists k_0, (length l) + div2 (length l) + k_0 <= c) /\
    (exists k_1, c <= (length l) + div2 (length l) + k_1) !} :=
  len <- clength l ;
  res <- split_at (div2 len) l ;
  <== res.

Next Obligation.
  simpl in *.
  clear am0 H12 H11.
  rename l0 into bs.
  rename l1 into cs.
  clear H9 H10.
  rename H3 into k_0.
  rename H6 into LEan.
  rename H4 into k_1.
  rename H5 into GEan.
  clear H. clear H0.
  clear H2.
  rename H8 into EQlenbs.
  remember (length (bs ++ cs)) as L.
  rewrite app_length in HeqL.
  rewrite min_div2 in EQlenbs.
  replace (length bs) with (div2 L) in *; try auto.
  clear EQlenbs.
  split. auto.
  split. auto.
  remember (length cs) as C in *.
  clear A bs cs HeqC.
  split; [idtac | split; [ exists k_0; omega | exists (k_1 + L + 1); omega] ]. 
  clear k_0 an LEan k_1 GEan.

  destruct (even_or_odd L) as [E | O].
  apply even_double in E.
  rewrite E in HeqL at 1.
  left. clear E. remember (div2 L) as D. clear HeqD L.
  unfold double in *. omega.
  apply odd_double in O.
  rewrite O in HeqL at 1.
  right. clear O. remember (div2 L) as D. clear HeqD L.
  unfold double in *. omega.
Qed.

Program Fixpoint merge
  {A:Set} {A_cmp:A -> A -> Prop}
  (A_cmp_trans:Transitive A_cmp) (A_cmp_total:Total A_cmp)
  (A_cmp_dec:DecCmp A_cmp) (xs:list A) (ys:list A)
  {measure (length (xs ++ ys))} 
  : {! res !:! list A !<! c !>!
    (IsSorted A_cmp xs) ->
    (IsSorted A_cmp ys) ->
    (SortedOf A_cmp (xs ++ ys) res) /\
    (exists k_0, k_0 <= c) /\
    (exists k_0, c <= (length xs) + (length ys) + k_0) !} :=
  match ys with
    | nil =>
      += 1;
      <== xs
    | cons y ys' =>
      match xs with
        | nil =>
          += 1;
          <== ys
        | cons x xs' =>
          match A_cmp_dec x y with
            | left _ =>
              res <- merge A_cmp_trans A_cmp_total A_cmp_dec xs' ys ;
              += 3;
              <== cons x res
            | right _ =>
              res <- merge A_cmp_trans A_cmp_total A_cmp_dec xs ys' ;
              += 3;
              <== cons y res
          end
      end
  end.

Next Obligation.
  simpl_list. clear merge.
  clear H1. rename H0 into IS.
  split.
  unfold SortedOf.
  eauto.
  split. exists 1. omega.
  exists 1. omega.
Qed.

Next Obligation.
  clear merge.
  clear H0. rename H1 into IS.
  split.
  unfold SortedOf.
  eauto.
  split. exists 1. omega.
  exists 1. omega.
Qed.

Next Obligation.
  clear Heq_anonymous. rename wildcard' into CMP.
  clear am H3.
  rename H1 into ISxs.
  rename H2 into ISys.
  rename H0 into IH.
  clear merge.
  edestruct IH.
  unfold IsSorted in *.
  apply StronglySorted_inv in ISxs.
  intuition.
  auto.
  clear IH. rename H into ISres.
  destruct H0 as
    [ [k_0 LEan]
      [k_1 GEan] ].
  unfold SortedOf in *.
  destruct ISres as [PM ISres].
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

  split.
  exists k_0. omega.
  exists (k_1 + 2). simpl in GEan. omega.
Qed.

Next Obligation.
  simpl. rewrite app_length.
  rewrite app_length. simpl. omega.
Qed.

Next Obligation.
  clear Heq_anonymous. rename wildcard' into CMP.
  clear am H3.
  rename H1 into ISxs.
  rename H2 into ISys.
  rename H0 into IH.
  clear merge.
  edestruct IH.
  auto.
  unfold IsSorted in *.
  apply StronglySorted_inv in ISys.
  intuition.
  clear IH. rename H into ISres.
  destruct H0 as
    [ [k_0 LEan]
      [k_1 GEan] ].
  unfold SortedOf in *.
  destruct ISres as [PM ISres].
  split.
  split.

  apply Permutation_sym.
  eapply Permutation_trans.
  eapply Permutation_cons.
  apply Permutation_sym.
  apply PM.
  replace (x :: xs' ++ y :: ys') with
    ((x :: xs') ++ y :: ys').  
  remember (x :: xs') as xs.
  apply Permutation_cons_app.
  auto.
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

  split.
  exists k_0. omega.
  exists (k_1 + 2). simpl in GEan. omega.
Qed.

Program Fixpoint mergesort
  {A:Set} {A_cmp:A -> A -> Prop}
  (A_cmp_trans:Transitive A_cmp) (A_cmp_total:Total A_cmp)
  (A_cmp_dec:DecCmp A_cmp) (l:list A)
  {measure (length l)}
  : {! res !:! list A !<! c !>!
    (SortedOf A_cmp l res) /\
    (exists k_0, (length l) * fl_log (length l) + k_0 <= c) /\
    (exists k_0, c <= (length l) * fl_log (length l) + k_0) !} :=
  match l with
    | nil =>
      += 1;
      <== nil
    | cons x l' =>
      match l' with
        | nil =>
          += 1;
          <== l
        | cons x' l'' =>
          xs12 <- split_evenly l ;
          xs1' <- mergesort A_cmp_trans A_cmp_total A_cmp_dec (fst xs12) ;
          xs2' <- mergesort A_cmp_trans A_cmp_total A_cmp_dec (snd xs12) ;
          res <- merge A_cmp_trans A_cmp_total A_cmp_dec xs1' xs2' ;
          += 2 ;
          <== res
      end
  end.

Next Obligation.
  clear mergesort.
  unfold SortedOf. unfold IsSorted.
  split. split. auto. apply SSorted_nil.
  split. exists 1. omega.
  exists 1. omega.
Qed.

Next Obligation.
  clear mergesort.
  unfold SortedOf. unfold IsSorted.
  split. split. auto. apply SSorted_cons.
  apply SSorted_nil. apply Forall_forall.
  intros x' IN. contradiction.
  split.
  exists 0. omega.
  exists 0. omega.
Qed.

Next Obligation.
  clear mergesort.
  clear am H5 H4.
  clear H2 H3.
  rename H into EQ.
  rewrite EQ in *.
  simpl in *.
  rename l0 into xs1.
  rename l1 into xs2.
  rename H0 into EQ1.
  rename H1 into EQ2.
  clear A_cmp A_cmp_trans A_cmp_total A_cmp_dec.
  rewrite app_length in *.
  remember (length xs1) as L1.
  remember (length xs2) as L2.

  destruct xs1 as [|x1 xs1].
  simpl in *. subst L1. subst xs2.
  simpl in *. omega.
  simpl in EQ.
  inversion EQ. clear EQ.
  subst x1. rename H1 into EQ.

  destruct xs2 as [|x2 xs2].
  simpl in *. subst L2.
  rewrite app_nil_r in EQ. subst xs1.
  simpl in HeqL1. rewrite HeqL1 in EQ2.
  simpl in EQ2.
  destruct EQ2; congruence.

  simpl in *. omega.
Qed.

Next Obligation.
  clear mergesort.
  clear am H10 H9.
  clear am0 H3 H2.
  clear H.
  clear H7 H8.
  rename H4 into EQ.
  rewrite EQ in *.
  simpl in *.
  rename l0 into xs1.
  rename l1 into xs2.
  clear H0 H1.
  rename H5 into EQ1.
  rename H6 into EQ2.
  clear A_cmp A_cmp_trans A_cmp_total A_cmp_dec.
  rewrite app_length in *.
  remember (length xs1) as L1.
  remember (length xs2) as L2.

  destruct xs1 as [|x1 xs1].
  simpl in *. subst L1. subst xs2.
  simpl in *. omega.
  simpl in EQ.
  inversion EQ. clear EQ.
  subst x1. rename H1 into EQ.

  destruct xs2 as [|x2 xs2].
  simpl in *. subst L2.
  rewrite app_nil_r in EQ. subst xs1.
  simpl in HeqL1. rewrite HeqL1 in EQ2.
  simpl in EQ2.
  destruct EQ2; congruence.

  simpl in *. omega.
Qed.

Next Obligation.
Admitted.
