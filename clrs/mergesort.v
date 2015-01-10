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
Require Import Braun.clrs.isort.

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

Program Fixpoint mergesortc
  {A:Set} {A_cmp:A -> A -> Prop}
  (A_cmp_trans:Transitive A_cmp) (A_cmp_total:Total A_cmp)
  (A_cmp_dec:DecCmp A_cmp) (l:list A) (len:nat) (EQlen:len = length l)
  {measure (length l)}
  : {! res !:! list A !<! c !>!
    (SortedOf A_cmp l res) /\
    (exists k_0, (length l) * cl_log (length l) + k_0 <= c) /\
    (exists k_0, c <= (length l) * cl_log (length l) + k_0) !} :=
  match l with
    | nil =>
      += 1;
      <== nil
    | cons x l' =>
      match even_odd_dec len with
        | left EVEN =>
          xs12 <- split_at (div2 len) l ;
          xs1' <- @mergesortc A A_cmp A_cmp_trans A_cmp_total A_cmp_dec
                              (fst xs12) (div2 len) _ _ ;
          xs2' <- @mergesortc A A_cmp A_cmp_trans A_cmp_total A_cmp_dec
                              (snd xs12) (div2 len) _ _ ;
          res <- merge A_cmp_trans A_cmp_total A_cmp_dec xs1' xs2' ;
          += 2 ;
          <== res
        | right ODD =>
          res' <- @mergesortc A A_cmp A_cmp_trans A_cmp_total A_cmp_dec
                              l' (pred len) _ _ ;
          res <- insert A_cmp_trans A_cmp_total A_cmp_dec x res' ;
          += 2 ;
          <== res
      end
  end.
          
Next Obligation.
  clear mergesortc.
  unfold SortedOf. unfold IsSorted.
  split. split. auto. apply SSorted_nil.
  split. exists 1. omega.
  exists 1. omega.
Qed.

Local Obligation Tactic := idtac.

Next Obligation.
  intros A A_cmp A_cmp_trans A_cmp_total A_cmp_dec
    l len EQlen _ x l' EQl' _ EVEN _
    [xs1 xs2] SPLIT_P.
  destruct SPLIT_P as [an [EQl [EQlen_xs1 _]]].
  simpl in *. subst len.
  rewrite min_div2 in EQlen_xs1. auto.
Qed.

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

Next Obligation.
  intros A A_cmp A_cmp_trans A_cmp_total A_cmp_dec
    l len EQlen _ x l' EQl' _ EVEN _
    [xs1 xs2] SPLIT_P.
  destruct SPLIT_P as [an [EQl [EQlen_xs1 _]]].
  simpl in *.
  eapply xs1_lt_l; auto.
  apply EQl'. subst len. auto.
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

Next Obligation.
  intros A A_cmp A_cmp_trans A_cmp_total A_cmp_dec
    l len EQlen _ x l' EQl' _ EVEN _
    [xs1 xs2] SPLIT_P _ _.
  destruct SPLIT_P as [an [EQl [EQlen_xs1 _]]].
  simpl in *.
  rewrite (xs1_eq_xs2 A len l xs1 xs2 EQlen EVEN EQl EQlen_xs1).
  subst len.
  rewrite min_div2 in EQlen_xs1.
  auto.
Qed.

Next Obligation.
  intros A A_cmp A_cmp_trans A_cmp_total A_cmp_dec
    l len EQlen _ x l' EQl' _ EVEN _
    [xs1 xs2] SPLIT_P _ _.
  destruct SPLIT_P as [an [EQl [EQlen_xs1 _]]].
  simpl in *.
  rewrite (xs1_eq_xs2 A len l xs1 xs2 EQlen EVEN EQl EQlen_xs1).
  eapply xs1_lt_l; auto.
  apply EQl'. subst len. auto.
Qed.

Lemma le_add:
  forall x x' y y',
    x <= x' ->
    y <= y' ->
    x + y <= x' + y'.
Proof.
  intros. omega.
Qed.

Lemma le_mult:
  forall x x' y y',
    x <= x' ->
    y <= y' ->
    x * y <= x' * y'.
Proof.
  induction x as [|x]; simpl.
  intros. apply le_0_n.
  intros.
  destruct H. simpl.
  apply le_add; auto.
  simpl. apply le_add; auto.
  eapply IHx; auto.
  omega.
Qed.
  
Next Obligation.
  intros A A_cmp A_cmp_trans
    A_cmp_total A_cmp_dec.  
  intros l len EQlen _.
  intros x l' EQl.
  intros _ E _.
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
  rewrite EQl.
  destruct REC1_P as [SO1 REC1_P].
  destruct REC2_P as [SO2 REC2_P].
  edestruct MERGE_P as [SOr [MERGE_OM MERGE_OH]].
  unfold SortedOf in SO1. intuition.
  unfold SortedOf in SO2. intuition.
  clear MERGE_P.
  destruct SO2 as [PM2 SS2].
  destruct SO1 as [PM1 SS1].
  destruct SOr as [PMr SSr].
  rewrite <- (Permutation_length PM1) in *.
  rewrite <- (Permutation_length PM2) in *.  
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
  rewrite app_length.
  rewrite EQlen_xs2 in *.
  rewrite <- EQlen in EQlen_xs1.
  rewrite min_div2 in EQlen_xs1.
  rewrite EQlen_xs1 in *.  
  clear EQlen_xs2 xs2 EQlen_xs1 xs1 EQlapp.
  remember (div2 len) as D.

  destruct D as [|D].
  destruct l as [|x' l].
  congruence.
  simpl in EQlen.
  rewrite EQlen in HeqD, E.
  inversion E. clear n H.
  rename H0 into O.
  simpl in HeqD.
  destruct (length l) as [|LEN].
  inversion O. congruence.

  replace (cl_log (S D + S D)) with (S (cl_log (S D))).
Focus 2.
  replace (S D) with (D + 1); try omega.
  replace (D + 1 + (D + 1)) with (D + 1 + D + 1); try omega.
  rewrite <- cl_log_even. omega.

  rewrite mult_succ_r.
  rewrite mult_plus_distr_r.
  replace (2 * S D) with (S D + S D) in SPLIT_P; try omega.
  rename len into L.
  clear A l EQlen x l' EQl.

  destruct REC2_P as [REC2_OM REC2_OH].
  destruct REC1_P as [REC1_OM REC1_OH].
  destruct SPLIT_P as [SPLIT_OM SPLIT_OH].
  split.
  
  clear SPLIT_OH MERGE_OH REC2_OH REC1_OH.
  destruct SPLIT_OM as [KMsplit SPLIT_OM].
  destruct MERGE_OM as [KMmerge MERGE_OM].
  destruct REC2_OM as [KMrec2 REC2_OM].
  destruct REC1_OM as [KMrec1 REC1_OM].
  exists (KMrec2 + KMrec1 + KMsplit + KMmerge).
  replace (S D * cl_log (S D) + S D * cl_log (S D) + (S D + S D) +
    (KMrec2 + KMrec1 + KMsplit + KMmerge)) with
  ((S D + S D + KMsplit) +
    ((S D * cl_log (S D) + KMrec1) +
      ((S D * cl_log (S D) + KMrec2) +
        ((KMmerge))))); try omega.

  clear SPLIT_OM MERGE_OM REC2_OM REC1_OM.
  destruct SPLIT_OH as [KHsplit SPLIT_OH].
  destruct MERGE_OH as [KHmerge MERGE_OH].
  destruct REC2_OH as [KHrec2 REC2_OH].
  destruct REC1_OH as [KHrec1 REC1_OH].
  exists (KHrec2 + KHrec1 + KHsplit + KHmerge + S D + S D + 2).
  replace (S D * cl_log (S D) + S D * cl_log (S D) + (S D + S D) +
    (KHrec2 + KHrec1 + KHsplit + KHmerge + S D + S D + 2)) with
  ((S D + S D + KHsplit) +
    ((S D * cl_log (S D) + KHrec1) +
      ((S D * cl_log (S D) + KHrec2) +
        ((S D + S D + KHmerge + 2))))); try omega.
Qed.

Next Obligation.
  intros A A_cmp A_cmp_trans
    A_cmp_total A_cmp_dec.  
  intros l len EQlen _.
  intros x l' EQl.
  intros _ O _.
  intros res' _.
  intros res _.
  intros xm EQxm.
  subst xm.
  intros Ninsert INSERT_P.
  intros Nrec REC_P.
  destruct REC_P as [SOres' REC_P].
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
  apply perm_skip.
  apply Permutation_sym.
  apply PMres'.
  auto.

  clear ISres ISres'.
  clear res PMres.
  clear A_cmp A_cmp_trans A_cmp_total A_cmp_dec.
  rewrite <- (Permutation_length PMres') in *.
  clear res' PMres'.

  destruct len as [|len].
  inversion O.
  rewrite EQl.
  rewrite <- EQlen in *.
  rewrite <- EQl in EQlen.
  simpl in EQlen.
  replace (length l') with len in *; try congruence.
  clear A l x l' EQlen EQl.
  apply odd_S2n in O.
  destruct O as [p EQp].
  unfold double in EQp.
  rewrite EQp.
  replace (S (p + p)) with (p + p + 1); try omega.
  rewrite cl_log_odd.
  replace (p + p + 1) with (S (p + p)); try omega.
  replace len with (p + p) in *; try omega.
  clear len EQp.

  destruct REC_P as [REC_OM REC_OH].
  destruct INSERT_P as [INSERT_OM INSERT_OH].

  destruct p as [|p].
  (* p = zero *)
  simpl in *.
  split.

  clear INSERT_OH REC_OH.
  destruct INSERT_OM as [KMinsert [_ INSERT_OM]].
  destruct REC_OM as [KMrec REC_OM].
  exists (KMrec + KMinsert + 1). omega.

  clear INSERT_OM REC_OM.
  destruct INSERT_OH as [KHinsert [_ INSERT_OH]].
  destruct REC_OH as [KHrec REC_OH].
  exists (KHrec + KHinsert + 1). omega.

  (* p = S n *)
  replace (S p + S p) with (p + 1 + p + 1) in *; try omega.  
  rewrite <- cl_log_even in *.
  replace (p + 1 + p + 1) with (S p + S p) in *; try omega.
  replace (p + 1) with (S p) in *; try omega.

  split.

  clear INSERT_OH REC_OH.
  destruct INSERT_OM as [KMinsert [_ INSERT_OM]].
  destruct REC_OM as [KMrec REC_OM].
  exists (KMrec + KMinsert + 1).
  replace (S (S p + S p) * (cl_log (S p) + 1) + (KMrec + KMinsert + 1)) with
    ((S (S p + S p) * (cl_log (S p) + 1) + KMrec) +
      ((KMinsert) +
        ((1)))); try omega.
  apply le_add; try omega.
  eapply le_trans; [ | apply REC_OM ].
  apply le_add; auto.
  apply le_mult; auto.

  (* xxx This is false. I'll have to change the lower bound to
  something a little bit wider, but I'm worrid how that will affect
  the other proofs. :( *)
  
  admit.

  rewrite mult_succ_l.
    clear INSERT_OM REC_OM.
  destruct INSERT_OH as [KHinsert [_ INSERT_OH]].
  destruct REC_OH as [KHrec REC_OH].
  exists (KHrec + KHinsert + S p + S p + 1). omega.
Qed.

(* xxx make a merge sort that doesn't take a length and computes it *)
