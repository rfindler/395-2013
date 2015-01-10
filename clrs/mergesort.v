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

Definition clength_time (n:nat) := n + 1.
Hint Unfold clength_time.

Program Fixpoint clength {A:Set} (l:list A)
  : {! res !:! nat !<! c !>!
    res = length l /\
    c = clength_time (length l) !}
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
  unfold clength_time.
  omega.
Qed.

Definition split_at_best_time (n:nat) := 2 * n + 1.
Definition split_at_worst_time (n:nat) := 2 * n + 2.
Hint Unfold split_at_best_time split_at_worst_time.

Program Fixpoint split_at {A:Set} (n:nat) (l:list A)
  : {! res !:! ((list A)*(list A)) !<! c !>!
    l = (fst res) ++ (snd res) /\
    length (fst res) = min n (length l) /\
    split_at_best_time (length (fst res)) <= c /\
    c <= split_at_worst_time (length (fst res))!}
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
  unfold split_at_best_time, split_at_worst_time.
  repeat split; auto. omega.
Qed.

Local Obligation Tactic := idtac.

Next Obligation.
  intros A n l n' EQn. subst n.
  intros a l' EQl. subst l.
  intros [xs1 xs2] _.
  simpl. intros xm EQxm. subst xm.
  intros an REC_P.
  destruct REC_P as [EQl' [EQlen_xs1 REC_P]].
  subst l'.  
  split. auto.
  rewrite <- EQlen_xs1.
  split. auto.
  clear EQlen_xs1.
  unfold split_at_best_time, split_at_worst_time in *.
  omega.
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

Definition merge_best_time (n:nat) := 1.
Definition merge_worst_time (n:nat) := 3 * n + 1.
Hint Unfold merge_best_time merge_worst_time.

Program Fixpoint merge
  {A:Set} {A_cmp:A -> A -> Prop}
  (A_cmp_trans:Transitive A_cmp) (A_cmp_total:Total A_cmp)
  (A_cmp_dec:DecCmp A_cmp) (xs:list A) (ys:list A)
  {measure (length (xs ++ ys))} 
  : {! res !:! list A !<! c !>!
    (IsSorted A_cmp xs) ->
    (IsSorted A_cmp ys) ->
    (SortedOf A_cmp (xs ++ ys) res) /\
    merge_best_time (length (xs ++ ys)) <= c /\
    c <= merge_worst_time (length (xs ++ ys)) !} :=
  match ys with
    | nil =>
      += 1;
      <== xs
    | cons y ys' =>
      match xs with
        | nil =>
          += 2 ;
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
  intros A A_cmp A_cmp_trans A_cmp_total A_cmp_dec.
  intros xs ys _.
  intros EQys. subst ys.
  simpl. simpl_list.
  intros xm EQxm. subst xm.
  unfold SortedOf.
  intros ISxs ISys.
  split. eauto.
  unfold merge_best_time, merge_worst_time.
  omega.
Qed.

Next Obligation.
  intros A A_cmp A_cmp_trans A_cmp_total A_cmp_dec.
  intros xs ys _.
  intros y ys' EQys.
  subst ys.
  intros EQxs. subst xs.
  simpl.
  intros xm EQxm. subst xm.
  unfold SortedOf.
  intros ISxs ISys.

  split. eauto.
  unfold merge_best_time, merge_worst_time.
  omega.
Qed.

Next Obligation.
  intros A A_cmp A_cmp_trans A_cmp_total A_cmp_dec.
  intros xs ys _.
  intros y ys' EQys. subst ys.
  intros x xs' EQxs. subst xs.
  intros _ CMP _.
  simpl. omega.
Qed.

Next Obligation.
  intros A A_cmp A_cmp_trans A_cmp_total A_cmp_dec.
  intros xs ys _.
  intros y ys' EQys. subst ys.
  intros x xs' EQxs. subst xs.
  intros _ CMP _.
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
  omega.
Qed.

Next Obligation.
  intros A A_cmp A_cmp_trans A_cmp_total A_cmp_dec.
  intros xs ys _.
  intros y ys' EQys. subst ys.
  intros x xs' EQxs. subst xs.
  intros _ CMP _.
  simpl. rewrite app_length.
  rewrite app_length. simpl. omega.
Qed.

Next Obligation.
  intros A A_cmp A_cmp_trans A_cmp_total A_cmp_dec.
  intros xs ys _.
  intros y ys' EQys. subst ys.
  intros x xs' EQxs. subst xs.
  intros _ CMP _.
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

  rewrite app_length in *.
  simpl.
  unfold merge_best_time, merge_worst_time in *.
  omega.
Qed.

Next Obligation.
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

Definition mergesortc_best_time (n:nat) :=
  n * (cl_log n) + 1.
Definition mergesortc_worst_time (n:nat) :=
  match n with
    | O =>
      1
    | S _ =>
      n * (cl_log n) + 3 * n + 2
  end.
Hint Unfold mergesortc_best_time mergesortc_worst_time.

Program Fixpoint mergesortc
  {A:Set} {A_cmp:A -> A -> Prop}
  (A_cmp_trans:Transitive A_cmp) (A_cmp_total:Total A_cmp)
  (A_cmp_dec:DecCmp A_cmp) (l:list A) (len:nat) (EQlen:len = length l)
  {measure (length l)}
  : {! res !:! list A !<! c !>!
    (SortedOf A_cmp l res) /\
    mergesortc_best_time (length l) <= c /\
    c <= mergesortc_worst_time (length l) !} :=
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
  intros A A_cmp A_cmp_trans A_cmp_total A_cmp_dec
    l len EQlen _ x xm EQxm.
  subst l. subst xm. simpl.
  clear len EQlen.
  
  unfold SortedOf. unfold IsSorted.
  split. split. auto. apply SSorted_nil.
  
  unfold mergesortc_best_time, mergesortc_worst_time.
  omega.
Qed.

Next Obligation.
  intros A A_cmp A_cmp_trans A_cmp_total A_cmp_dec
    l len EQlen _ x l' EQl' _ EVEN _
    [xs1 xs2] SPLIT_P.
  destruct SPLIT_P as [an [EQl [EQlen_xs1 _]]].
  simpl in *. subst len.
  rewrite min_div2 in EQlen_xs1. auto.
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
  edestruct MERGE_P as [SOr MERGE_T].
  unfold SortedOf in SO1. intuition.
  unfold SortedOf in SO2. intuition.
  clear MERGE_P.
  destruct SO2 as [PM2 SS2].
  destruct SO1 as [PM1 SS1].
  destruct SOr as [PMr SSr].
  rewrite app_length in *.
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

  unfold mergesortc_best_time, mergesortc_worst_time in *.
  unfold split_at_best_time, split_at_worst_time in *.
  unfold merge_best_time, merge_worst_time in *.

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

  split; try omega.
  replace (0 + 2) with 2; try omega.
  remember (S D + S D) as SDSD.
  destruct SDSD as [|t].
  omega.
  rewrite HeqSDSD in *.
  clear t HeqSDSD.
  
  replace (S D * cl_log (S D) + S D * cl_log (S D) + (S D + S D) + 3 * (S D + S D) +
    2)
    with
      ((S D + S D + 2) + (S D * cl_log (S D) + S D * cl_log (S D) + 3 * (S D + S D))); try omega.
  apply le_add.
  omega.

  (* xxx need to fiddle with the function *)
  admit.
Qed.

Next Obligation.
  program_simpl.
Qed.

Next Obligation.
  program_simpl.
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

  unfold mergesortc_best_time, mergesortc_worst_time in *.
  unfold insert_best_time, insert_worst_time in *.

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

  destruct p as [|p].
  (* p = zero *)
  simpl in *.
  omega.

  (* p = S n *)
  replace (S p + S p) with (p + 1 + p + 1) in *; try omega.  
  rewrite <- cl_log_even in *.
  replace (p + 1 + p + 1) with (S p + S p) in *; try omega.
  replace (p + 1) with (S p) in *; try omega.

  remember (S p + S p) as SpSp.
  destruct SpSp as [|t].
  omega.
  rewrite HeqSpSp in *.
  clear t HeqSpSp.

  rewrite mult_succ_l.

  split.
  cut ((cl_log (S p) + 1) <= Ninsert + 2). intros LE.
  omega.
  clear REC_P.

  (* xxx false! *)
  admit.

  rewrite mult_succ_r.
  cut (Ninsert + 2 <= (cl_log (S p) + 1) + 3). intros LE.
  omega.
  clear REC_P.

  (* xxx false! *)
  admit.
Qed.

Next Obligation.
  program_simpl.
Defined.

Definition mergesort_best_time (n:nat) :=
  clength_time n + mergesortc_best_time n.
Definition mergesort_worst_time (n:nat) :=
  clength_time n + mergesortc_worst_time n.
Hint Unfold mergesort_best_time mergesort_worst_time.

Program Definition mergesort
  {A:Set} {A_cmp:A -> A -> Prop}
  (A_cmp_trans:Transitive A_cmp) (A_cmp_total:Total A_cmp)
  (A_cmp_dec:DecCmp A_cmp) (l:list A)
  : {! res !:! list A !<! c !>!
    (SortedOf A_cmp l res) /\
    mergesort_best_time (length l) <= c /\
    c <= mergesort_worst_time (length l) !} :=
  len <- clength l ;
  res <- mergesortc A_cmp_trans A_cmp_total A_cmp_dec l len _ ;
  <== res.

Solve Obligations using program_simpl.

Next Obligation.
  intros A A_cmp A_cmp_trans A_cmp_total A_cmp_dec
    l len _ res _.
  intros Nmsc [SOres MSC_P].
  intros Nlen [EQlen LEN_P].
  subst len. subst Nlen.
  split. auto.
  remember (length l) as L.
  clear A A_cmp A_cmp_trans A_cmp_total A_cmp_dec res SOres l HeqL.
  unfold mergesort_best_time, mergesort_worst_time in *.
  omega.
Qed.

Theorem mergesort_best:
  big_omega mergesort_best_time (fun n => n * cl_log n).
Proof.
  unfold big_omega, mergesort_best_time.
  unfold clength_time, mergesortc_best_time.

  exists 0. exists 1.
  intros n LE.
  omega.
Qed.

Theorem mergesort_worst:
  big_oh mergesort_worst_time (fun n => n * cl_log n).
Proof.
  unfold big_oh, mergesort_worst_time.
  unfold clength_time, mergesortc_worst_time.

  exists 1. exists 1.
  intros n LE.
  destruct n as [|n].
  omega.

  (* xxx it's not worth figuring this out until the numbers above are right *)
  admit.
Qed.
