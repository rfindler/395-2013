Require Import Braun.common.util Braun.common.le_util Braun.common.same_structure.
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

Definition split_at_time (n:nat) := 2 * n + 1.

Program Fixpoint split_at {A:Set} (n:nat) (l:list A) (V:n <= length l)
  : {! res !:! ((list A)*(list A)) !<! c !>!
    l = (fst res) ++ (snd res) /\
    length (fst res) = min n (length l) /\
    c = split_at_time n !}
  :=
  match n with
    | O =>
      += 1;
      <== (nil, l)
    | S n' =>
      match l with
        | nil =>
          _
        | cons a l' =>
          res <- split_at n' l' _ ;
          += 2;
          <== (cons a (fst res), (snd res))
      end
  end.

Next Obligation.
  unfold split_at_time.
  simpl in *. omega.
Qed.

Next Obligation.
  simpl in *. omega.
Qed.

Local Obligation Tactic := idtac.

Next Obligation.
  unfold split_at_time.
  intros A n l VL n' EQn. subst n.
  intros a l' EQl. subst l.
  intros [xs1 xs2] _.
  simpl. intros xm EQxm. subst xm.
  intros an REC_P.
  destruct REC_P as [EQl' [EQlen_xs1 EQan]].
  subst l'.  subst an.
  split. auto.
  clear VL.
  rewrite <- EQlen_xs1.
  split. auto.
  clear EQlen_xs1.
  omega.
Qed.

(* xxx I think we know more for the way merge is called by merge sort
(with equal input) *)

Definition merge_best_time (n:nat) (m:nat) := 3 * (min n m) + 1.
Definition merge_worst_time (n:nat) (m:nat) := 3 * (n + m) + 1.
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
    merge_best_time (length xs) (length ys) <= c /\
    c <= merge_worst_time (length xs) (length ys) !} :=
  match xs with
    | nil =>
      += 1;
      <== ys
    | cons x xs' =>
      match ys with
        | nil =>
          += 2 ;
          <== xs
        | cons y ys' =>
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
  intros A A_cmp A_cmp_trans A_cmp_total A_cmp_dec.
  intros xs ys _.
  intros x xs' EQxs. subst xs.
  intros y ys' EQys. subst ys.
  intros _ CMP _.
  simpl. omega.
Qed.

Next Obligation.
  intros A A_cmp A_cmp_trans A_cmp_total A_cmp_dec.
  intros xs ys _.
  intros x xs' EQxs. subst xs.
  intros y ys' EQys. subst ys.
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
  intros A A_cmp A_cmp_trans A_cmp_total A_cmp_dec.
  intros xs ys _.
  intros x xs' EQxs. subst xs.
  intros y ys' EQys. subst ys.
  intros _ CMP _.
  simpl. rewrite app_length.
  rewrite app_length. simpl. omega.
Qed.

Next Obligation.
  intros A A_cmp A_cmp_trans A_cmp_total A_cmp_dec.
  intros xs ys _.
  intros x xs' EQxs. subst xs.
  intros y ys' EQys. subst ys.
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

Inductive Mergesortc_Best_Time mbt ibt
  : nat -> nat -> Prop :=
| MBT_O :
  Mergesortc_Best_Time mbt ibt O 1
| MBT_Sn_even :
  forall n D,
    even (S n) ->
    Mergesortc_Best_Time mbt ibt (div2 (S n)) D ->
    Mergesortc_Best_Time mbt ibt (S n)
    (split_at_time (div2 (S n)) + D + D + mbt (div2 (S n)) (div2 (S n)) + 2)
| MBT_Sn_odd :
  forall n D,
    odd (S n) ->
    Mergesortc_Best_Time mbt ibt n D ->
    Mergesortc_Best_Time mbt ibt (S n) (D + ibt n + 2).
Hint Constructors Mergesortc_Best_Time.

Lemma Mergesortc_Best_Time_fun :
  forall mbt ibt n m m',
    Mergesortc_Best_Time mbt ibt n m ->
    Mergesortc_Best_Time mbt ibt n m' ->
    m = m'.
Proof.
  intros mbt ibt.
  apply (well_founded_induction lt_wf
  (fun n => forall  m m',
    Mergesortc_Best_Time mbt ibt n m ->
    Mergesortc_Best_Time mbt ibt n m' ->
    m = m')).

  intros n IH m m' MBT MBT'.
  inversion MBT.
  subst n m.
  inversion MBT'. auto.

  rename H into E.
  rename H0 into MBT1.
  subst n m.
  inversion MBT'.
  subst n0 m'.
  clear H0. rename H1 into MBT1'.
  replace D0 with D. auto.
  eapply (@IH _ _ _ _ MBT1 MBT1').

  rename H0 into O.
  apply (not_even_and_odd _ E) in O. contradiction.

  subst n m.
  rename H into O.
  rename H0 into MBT1.
  inversion MBT'.

  rename H0 into E.
  apply (not_even_and_odd _ E) in O. contradiction.

  subst m' n0.
  clear H0.
  rename H1 into MBT1'.
  replace D0 with D. auto.
  eapply (@IH _ _ _ _ MBT1 MBT1').
  
Grab Existential Variables.
auto.

auto.

Qed.

Definition mergesortc_best_time_c (n:nat) :
  { m : nat |
    Mergesortc_Best_Time
    merge_best_time insert_best_time
    n m }.
Proof.
  generalize n. clear n.
  apply (well_founded_induction lt_wf).
  intros n IH.
  destruct n as [|n'].
  eauto.
  destruct (even_odd_dec (S n')) as [E | O].
  destruct (IH (div2 (S n'))) as [D MBT]. auto.
  eauto.
  destruct (IH n') as [D MBT]. auto.
  eauto.
Defined.

Definition mergesortc_best_time (n:nat) :=
  proj1_sig (mergesortc_best_time_c n).
    
Lemma mergesortc_best_time_O:
  mergesortc_best_time 0 = 1.
Proof.
  program_simpl.
Qed.

Lemma mergesortc_best_time_Sn_even:
  forall n,
    even n ->
    (exists m, n = S m) ->
    mergesortc_best_time n = (split_at_time (div2 n) +
          mergesortc_best_time (div2 n) +
          mergesortc_best_time (div2 n) +
          merge_best_time (div2 n) (div2 n) + 2).
Proof.
  intros n E [m EQn]. subst n.
  unfold mergesortc_best_time.
  destruct (mergesortc_best_time_c (S m)) as [D0 MBT0].
  destruct (mergesortc_best_time_c (div2 (S m))) as [D1 MBT1].
  inversion MBT0.
  clear H0. subst m.
  subst D0.
  rename H1 into MBT1'.
  simpl.
  rewrite (Mergesortc_Best_Time_fun _ _ _ _ _ MBT1 MBT1'). auto.

  rename H0 into O.
  apply (not_even_and_odd _ E) in O. contradiction.
Qed.

Lemma mergesortc_best_time_Sn_odd:
  forall n n',
    odd n ->
    n = S n' ->
    mergesortc_best_time n = (mergesortc_best_time n' +
          insert_best_time n' + 2).
Proof.
  intros n n' O EQn. subst n.

  unfold mergesortc_best_time.
  destruct (mergesortc_best_time_c (S n')) as [D0 MBT0].
  destruct (mergesortc_best_time_c n') as [D1 MBT1].
  inversion MBT0.

  rename H0 into E.
  apply (not_even_and_odd _ E) in O. contradiction.
  
  clear H0. subst n.
  subst D0.
  rename H1 into MBT1'.
  simpl.
  rewrite (Mergesortc_Best_Time_fun _ _ _ _ _ MBT1 MBT1'). auto.
Qed.

Definition mergesortc_worst_time_c (n:nat) :
  { m : nat |
    Mergesortc_Best_Time
    merge_worst_time insert_worst_time
    n m }.
Proof.
  generalize n. clear n.
  apply (well_founded_induction lt_wf).
  intros n IH.
  destruct n as [|n'].
  eauto.
  destruct (even_odd_dec (S n')) as [E | O].
  destruct (IH (div2 (S n'))) as [D MBT]. auto.
  eauto.
  destruct (IH n') as [D MBT]. auto.
  eauto.
Defined.

Definition mergesortc_worst_time (n:nat) :=
  proj1_sig (mergesortc_worst_time_c n).
    
Lemma mergesortc_worst_time_O:
  mergesortc_worst_time 0 = 1.
Proof.
  program_simpl.
Qed.

Lemma mergesortc_worst_time_Sn_even:
  forall n,
    even n ->
    (exists m, n = S m) ->
    mergesortc_worst_time n = (split_at_time (div2 n) +
          mergesortc_worst_time (div2 n) +
          mergesortc_worst_time (div2 n) +
          merge_worst_time (div2 n) (div2 n) + 2).
Proof.
  intros n E [m EQn]. subst n.
  unfold mergesortc_worst_time.
  destruct (mergesortc_worst_time_c (S m)) as [D0 MBT0].
  destruct (mergesortc_worst_time_c (div2 (S m))) as [D1 MBT1].
  inversion MBT0.
  clear H0. subst m.
  subst D0.
  rename H1 into MBT1'.
  simpl.
  rewrite (Mergesortc_Best_Time_fun _ _ _ _ _ MBT1 MBT1'). auto.

  rename H0 into O.
  apply (not_even_and_odd _ E) in O. contradiction.
Qed.

Lemma mergesortc_worst_time_Sn_odd:
  forall n n',
    odd n ->
    n = S n' ->
    mergesortc_worst_time n = (mergesortc_worst_time n' +
          insert_worst_time n' + 2).
Proof.
  intros n n' O EQn. subst n.

  unfold mergesortc_worst_time.
  destruct (mergesortc_worst_time_c (S n')) as [D0 MBT0].
  destruct (mergesortc_worst_time_c n') as [D1 MBT1].
  inversion MBT0.

  rename H0 into E.
  apply (not_even_and_odd _ E) in O. contradiction.
  
  clear H0. subst n.
  subst D0.
  rename H1 into MBT1'.
  simpl.
  rewrite (Mergesortc_Best_Time_fun _ _ _ _ _ MBT1 MBT1'). auto.
Qed.

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
          xs12 <- split_at (div2 len) l _ ;
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
  program_simpl.
Qed.

Next Obligation.
  intros A A_cmp A_cmp_trans A_cmp_total A_cmp_dec
    l len EQlen _ x l' EQl' _ EVEN _.
  subst len. subst l. simpl (length (x::l')).

  remember (lt_div2 (S (length l'))) as LT. omega.
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
  remember EQlen as EQlen'. clear HeqEQlen'.
  rewrite app_length.
  rewrite <- EQlen in EQlen_xs1.
  rewrite EQlapp in EQlen.
  rewrite app_length in EQlen.
  rewrite EQlen_xs2 in *.
  rewrite min_div2 in EQlen_xs1.
  rewrite EQlen_xs1 in *.
  clear EQlen_xs2 EQlen_xs1 EQlapp xs1 xs2.
  remember (div2 len) as D.

  destruct D as [|D].
  destruct l as [|x' l].
  congruence.
  simpl in EQlen'.
  rewrite EQlen' in HeqD, E.
  inversion E. clear n H.
  rename H0 into O.
  simpl in HeqD.
  destruct (length l) as [|LEN].
  inversion O. congruence.

  subst len.
  rewrite mergesortc_best_time_Sn_even; eauto.
  rewrite mergesortc_worst_time_Sn_even; eauto.
  replace (div2 (S D + S D)) with (div2 (2 * S D)).
  rewrite div2_double.
  omega.
  replace (2 * S D) with (S D + S D); try omega.
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

  rewrite (mergesortc_best_time_Sn_odd (length (x :: l')) (length l')).
  rewrite (mergesortc_worst_time_Sn_odd (length (x :: l')) (length l')).
  omega.
  subst. auto.
  auto.
  subst. auto.
  auto.
Qed.

Next Obligation.
  program_simpl.
Defined.

Theorem mergesortc_worst:
  big_oh mergesortc_worst_time (fun n => n * cl_log n + 1).
Proof.
  unfold big_oh.
  exists 0. exists 4.
  intros n LE. clear LE. generalize n. clear n.
  apply (well_founded_induction lt_wf
    (fun n =>
      mergesortc_worst_time n <= 4 * (n * cl_log n + 1))).
  intros n IH.
  destruct n as [|n].

  rewrite mergesortc_worst_time_O. omega.

  destruct (even_or_odd (S n)) as [E | O].
  
  rewrite mergesortc_worst_time_Sn_even; eauto.
  assert ((div2 (S n)) < S n) as LEd; eauto.
  apply IH in LEd. clear IH.
  unfold split_at_time, merge_worst_time.
  apply even_2n in E.
  destruct E as [p EQ].
  rewrite EQ in *.
  assert ((div2 (double p)) = p) as EQp.
  unfold double. replace (p + p) with ( 2 * p) ; try omega.
  apply div2_double.
  rewrite EQp in *. clear EQp.
  unfold double in *.
  destruct p as [|p].
  omega. clear EQ.
  remember (mergesortc_worst_time (S p)) as M.
  clear HeqM.

  replace (S p + S p) with (p + 1 + p + 1); try omega.
  rewrite <- cl_log_even.
  replace (p + 1 + p + 1) with (S p + S p); try omega.
  replace (p + 1) with (S p); try omega.
  rewrite mult_plus_distr_r.
  replace (S p + S p) with (2 * S p); try omega.
  replace (3 * (2 * S p)) with (6 * S p); try omega.
  replace (2 * S p + 2 + M + M + (6 * S p + 1) + 2) with
    (2 * M + 8 * S p + 5); try omega.

  replace (S p * (cl_log (S p) + 1) + S p * (cl_log (S p) + 1) + 1) with
    ((2 * (S p * (cl_log (S p) + 1))) + 1); try omega.
  rewrite mult_plus_distr_l.
  rewrite mult_plus_distr_l.
  replace (S p * 1) with (S p); try omega.
  rewrite mult_plus_distr_l in LEd.
  replace (4 * 1) with 4 in *; try omega.
  rewrite mult_plus_distr_l.
  rewrite mult_plus_distr_l.
  rewrite (mult_assoc 4 2).
  rewrite (mult_assoc 4 2).
  replace (4 * 2) with 8; try omega.
  remember (S p * cl_log (S p)) as Q.
  
  cut (2 * 4 + 5 <= 4). intros LE. omega. clear n p M Q HeqQ LEd.

  (* XXX The Each M includes a 4 and the 5 comes from the RHS. The 4
  is the one from the right. The only value that can be put here is
  -5, which isn't a nat *)
  admit.

  erewrite mergesortc_worst_time_Sn_odd; eauto.
  assert (n < S n) as LEd; eauto.
  apply IH in LEd. clear IH.
  remember (mergesortc_worst_time n) as M.
  clear HeqM.
  unfold insert_worst_time.
  apply odd_S2n in O.
  destruct O as [p EQp].
  unfold double in EQp.
  replace (S n) with (p + p +1); try omega.
  rewrite cl_log_odd.
  replace n with (p + p) in *; try omega.
  clear EQp n.

  destruct p as [|p].
  simpl in *. omega.

  replace (S p + S p) with (p + 1 + p + 1) in LEd; try omega.
  rewrite <- cl_log_even in LEd.
  replace (p + 1 + p + 1) with (S p + S p) in LEd; try omega.
  replace (p + 1) with (S p) in LEd; try omega.
  remember (S p) as SP. clear HeqSP p.

  remember (SP + SP) as SPSP.
  replace (M + (2 * SPSP + 1) + 2) with (M + 2 * SPSP + 3); try omega.  
  rewrite mult_plus_distr_r.
  rewrite mult_1_l.
  replace (SPSP * (cl_log SP + 1) + (cl_log SP + 1) + 1) with
    ((SPSP * (cl_log SP + 1) + 1) + (cl_log SP + 1)); try omega.
  rewrite mult_plus_distr_l.
  remember (SPSP * (cl_log SP + 1) + 1) as Q.
  rewrite mult_plus_distr_l.
  rewrite mult_1_r.
  rewrite <- plus_assoc.  
  apply le_add. auto.
  clear M LEd Q HeqQ.
  subst SPSP.

  (* xxx This is definitely false (look at a graph) *)
  admit.

Admitted.

Theorem mergesortc_best:
  big_omega mergesortc_best_time (fun n => n * cl_log n).
Proof.
Admitted.

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

Lemma big_oh_n_nlogn:
  big_oh (fun n : nat => n) (fun n : nat => n * cl_log n).
Proof.
Admitted.

Lemma mergesort_worst_step:
  forall f,
    big_oh (fun n : nat => n + 1) f ->
    big_oh mergesortc_worst_time f ->
    big_oh mergesort_worst_time f.
Proof.
  intros f LINf mergesortc_worst.
  unfold mergesort_worst_time.
  apply big_oh_plus.
  unfold clength_time.
  auto. auto.
Qed.

Corollary mergesort_worst:
  big_oh mergesort_worst_time (fun n : nat => n * cl_log n + 1).
Proof.
  apply mergesort_worst_step.
  apply big_oh_add_k_both.
  apply big_oh_n_nlogn.
  apply mergesortc_worst.
Qed.

Corollary mergesort_best:
  big_omega mergesort_best_time (fun n => n * cl_log n).
Proof.
Admitted.
