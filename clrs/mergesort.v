Require Import Braun.common.util Braun.common.le_util Braun.common.same_structure.
Require Import Braun.common.log Braun.common.big_oh Braun.common.le_util.
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
Require Import Coq.Program.Wf Arith.Even Arith.Div2 Arith Init.Wf.

Include WfExtensionality.

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

Program Fixpoint mergesortc_worst_time1 n {measure n} :=
  match n with
    | 0 => 1
    | S n' => 
      if (even_odd_dec n)
      then (split_at_time (div2 n) +
            mergesortc_worst_time1 (div2 n) +
            mergesortc_worst_time1 (div2 n) +
            merge_worst_time (div2 n) (div2 n) + 2)
      else  (mergesortc_worst_time1 n' +
             insert_worst_time n' + 2)
  end.
Next Obligation. intros. subst n. auto. Defined.
Next Obligation. intros. subst n. auto. Defined.
Next Obligation. intros. subst n. auto. Defined.
Next Obligation. apply lt_wf. Defined.

Lemma worst_01 : forall n, mergesortc_worst_time n = mergesortc_worst_time1 n.
Proof.
  apply (well_founded_induction 
           lt_wf
           (fun n => mergesortc_worst_time n = mergesortc_worst_time1 n)).
  intros n INDn.
  destruct n.
  rewrite mergesortc_worst_time_O.
  unfold_sub mergesortc_worst_time1 (mergesortc_worst_time1 0).
  omega.
  unfold_sub mergesortc_worst_time1 (mergesortc_worst_time1 (S n)).
  fold mergesortc_worst_time1.
  destruct (even_odd_dec (S n)).
  rewrite mergesortc_worst_time_Sn_even; try (exists n; auto); auto.
  destruct n.
  inversion e as [|n ODD_ZERO WHATEVER].
  inversion ODD_ZERO.
  replace (div2 (S (S n))) with (S (div2 n));[|auto].
  rewrite (INDn (S (div2 n))).
  omega.
  replace (S (div2 n)) with (div2 n + 1);[|omega].
  replace (S (S n)) with (S n + 1);[|omega].
  apply plus_lt_compat_r.
  auto.
  rewrite (mergesortc_worst_time_Sn_odd (S n) n); auto.
Qed.


Program Fixpoint mergesortc_worst_time2 n {measure n} :=
  match n with
    | 0 => 1
    | S n' => 
      if (even_odd_dec n)
      then (split_at_time (div2 n) +
            mergesortc_worst_time2 (div2 n) +
            mergesortc_worst_time2 (div2 n) +
            merge_worst_time (div2 n) (div2 n) + 2)
      else  ((match n' with
                | 0 => 1
                | S n'' => 
                  (split_at_time (div2 n') +
                   mergesortc_worst_time2 (div2 n') +
                   mergesortc_worst_time2 (div2 n') +
                   merge_worst_time (div2 n') (div2 n') + 2)
              end) +
             insert_worst_time n' + 2)
  end.
Next Obligation. intros. subst n. auto. Defined.
Next Obligation. intros. subst n. auto. Defined.
Next Obligation. intros. subst n. auto. Defined.
Next Obligation. intros. subst n. auto. Defined.
Next Obligation. apply lt_wf. Defined.

Lemma worst_12 : forall n, mergesortc_worst_time1 n = mergesortc_worst_time2 n.
Proof.
  apply (well_founded_induction 
           lt_wf
           (fun n => mergesortc_worst_time1 n = mergesortc_worst_time2 n)).
  intros n INDn.
  destruct n.
  unfold_sub mergesortc_worst_time1 (mergesortc_worst_time1 0).
  unfold_sub mergesortc_worst_time2 (mergesortc_worst_time2 0).
  auto.
  unfold_sub mergesortc_worst_time1 (mergesortc_worst_time1 (S n)).
  fold mergesortc_worst_time1.
  unfold_sub mergesortc_worst_time2 (mergesortc_worst_time2 (S n)).
  fold mergesortc_worst_time2.
  destruct (even_odd_dec (S n)).
  rewrite INDn; auto.
  destruct n; auto.
  apply lt_n_S; auto.
  destruct n.
  unfold insert_worst_time.
  unfold_sub mergesortc_worst_time1 (mergesortc_worst_time1 0).
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
    | 0 => 1
    | S n' => 
      if (even_odd_dec n)
      then (split_at_time (div2 n) +
            mergesortc_worst_time3 (div2 n) +
            mergesortc_worst_time3 (div2 n) +
            merge_worst_time (div2 n) (div2 n) + 2)
      else match n' with
             | 0 => 1 + insert_worst_time n' + 2
             | S n'' => 
               (split_at_time (div2 n') +
                mergesortc_worst_time3 (div2 n') +
                mergesortc_worst_time3 (div2 n') +
                merge_worst_time (div2 n') (div2 n') + 2
                + insert_worst_time n' + 2)
           end
  end.
Next Obligation. intros. subst n. auto. Defined.
Next Obligation. intros. subst n. auto. Defined.
Next Obligation. intros. subst n. auto. Defined.
Next Obligation. intros. subst n. auto. Defined.
Next Obligation. apply lt_wf. Defined.

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
    | 0 => 1
    | S n' => 
      match n' with
        | 0 => if (even_odd_dec n)
               then (split_at_time (div2 n) +
                     mergesortc_worst_time4 (div2 n) +
                     mergesortc_worst_time4 (div2 n) +
                     merge_worst_time (div2 n) (div2 n) + 2)
               else 1 + insert_worst_time n' + 2
        | S n'' => 
          if (even_odd_dec n)
          then (split_at_time (div2 n) +
                mergesortc_worst_time4 (div2 n) +
                mergesortc_worst_time4 (div2 n) +
                merge_worst_time (div2 n) (div2 n) + 2)
          else 
            (split_at_time (div2 n') +
             mergesortc_worst_time4 (div2 n') +
             mergesortc_worst_time4 (div2 n') +
             merge_worst_time (div2 n') (div2 n') + 2
             + insert_worst_time n' + 2)
      end
  end.
Next Obligation. intros. subst n. auto. Defined.
Next Obligation. intros. subst n. auto. Defined.
Next Obligation. intros. subst n. auto. Defined.
Next Obligation. intros. subst n. auto. Defined.
Next Obligation. intros. subst n. auto. Defined.
Next Obligation. intros. subst n. auto. Defined.
Next Obligation. apply lt_wf. Defined.

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
    | 0 => 1
    | S n' => 
      match n' with
        | 0 => 4
        | S _ => 
          if (even_odd_dec n)
          then (split_at_time (div2 n) +
                mergesortc_worst_time5 (div2 n) +
                mergesortc_worst_time5 (div2 n) +
                merge_worst_time (div2 n) (div2 n) + 2)
          else 
            (split_at_time (div2 n') +
             mergesortc_worst_time5 (div2 n') +
             mergesortc_worst_time5 (div2 n') +
             merge_worst_time (div2 n') (div2 n') + 2
             + insert_worst_time n' + 2)
      end
  end.
Next Obligation. intros. subst n. auto. Defined.
Next Obligation. intros. subst n. auto. Defined.
Next Obligation. intros. subst n. auto. Defined.
Next Obligation. intros. subst n. auto. Defined.
Next Obligation. apply lt_wf. Defined.

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
    | 0 => 1
    | S n' => 
      match n' with
        | 0 => 4
        | S _ => 
          split_at_time (div2 n) +
          mergesortc_worst_time6 (div2 n) +
          mergesortc_worst_time6 (div2 n) +
          merge_worst_time (div2 n) (div2 n) + 2
          + insert_worst_time n' + 2
      end
  end.
Next Obligation. intros. subst n. auto. Defined.
Next Obligation. intros. subst n. auto. Defined.
Next Obligation. apply lt_wf. Defined.

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
  apply plus_le_compat_r.
  apply le_plus_trans.
  apply le_plus_trans.
  apply plus_le_compat_r.
  apply plus_le_compat; auto.
  apply plus_le_compat; auto.
  apply INDn.
  apply lt_n_S; auto.
  apply INDn.
  apply lt_n_S; auto.

  apply plus_le_compat_r.
  apply plus_le_compat_r.
  apply plus_le_compat_r.
  apply plus_le_compat.
  rewrite odd_div2.
  apply plus_le_compat.
  apply plus_le_compat.
  unfold split_at_time.
  apply plus_le_compat; auto.
  apply le_mult_right.
  auto.
  apply INDn; auto.
  apply INDn; auto.
  inversion o as [X Y Z].
  inversion Y; auto.
  unfold merge_worst_time.
  apply plus_le_compat_r.
  apply plus_le_compat.
  apply plus_le_compat.
  apply div2_monotone; auto.
  apply div2_monotone; auto.
  assert (div2 (S n) <= div2 (S (S n))).
  apply div2_monotone;auto.
  omega.
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
Next Obligation. intros. subst n. auto. Defined.
Next Obligation. intros. subst n. auto. Defined.
Next Obligation. apply lt_wf. Defined.

Lemma worst_67 : big_oh mergesortc_worst_time6 mergesortc_worst_time7.
Proof.
  exists 1.
  exists 8.
  intros n LT.
  destruct n.
  intuition.
  clear LT.
  apply (well_founded_induction 
           lt_wf
           (fun n => mergesortc_worst_time6 (S n) <=
                     8 * mergesortc_worst_time7 (S n))).
  clear n.
  intros n INDn.
  unfold_sub mergesortc_worst_time6 (mergesortc_worst_time6 (S n)).
  fold mergesortc_worst_time6.
  unfold_sub mergesortc_worst_time7 (mergesortc_worst_time7 (S n)).
  fold mergesortc_worst_time7.
  destruct n; [omega|].
  unfold split_at_time.
  unfold merge_worst_time.
  unfold insert_worst_time.
  replace (2 * div2 (S (S n)) + 1 + mergesortc_worst_time6 (S (div2 n)) +
           mergesortc_worst_time6 (S (div2 n)) +
           (3 * (div2 (S (S n)) + div2 (S (S n))) + 1) + 2 + 
           (2 * S n + 1) + 2)
  with (8 * div2 (S (S n)) + (2 * n + 9) + mergesortc_worst_time6 (S (div2 n)) +
        mergesortc_worst_time6 (S (div2 n))); [|omega].
  rewrite mult_plus_distr_l.
  rewrite mult_plus_distr_l.
  rewrite mult_plus_distr_l.
  apply plus_le_compat.
  apply plus_le_compat.
  apply plus_le_compat.
  omega.
  omega.
  apply INDn; auto.
  apply INDn; auto.
Qed.

Program Fixpoint mergesortc_worst_time8 n {measure n} :=
  match n with
    | 0 => 0
    | S _ => 
      n +
      mergesortc_worst_time8 (div2 n) +
      mergesortc_worst_time8 (div2 n)
  end.
Next Obligation. intros. subst n. auto. Defined.
Next Obligation. intros. subst n. auto. Defined.
Next Obligation. apply something_I_dont_understand. Defined.

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

Definition mergesortc_worst_time9 n := n * cl_log n.

Lemma worst_89 : big_oh mergesortc_worst_time8 mergesortc_worst_time9.
Proof.
  exists 2.
  exists 4.
  intros n LT.
  destruct n. intuition.
  destruct n. intuition.
  clear LT.
  apply (well_founded_induction 
           lt_wf
           (fun n => mergesortc_worst_time8 (S n) <=
                     4 * mergesortc_worst_time9 (S n))).
  clear n; intros n IND.
  unfold_sub mergesortc_worst_time8 (mergesortc_worst_time8 (S n)).
  unfold mergesortc_worst_time9.
  destruct n.
  unfold_sub mergesortc_worst_time8 (mergesortc_worst_time8 0).
  unfold_sub cl_log (cl_log 1).
  unfold_sub cl_log (cl_log 0).
  omega.
  unfold mergesortc_worst_time9 in IND.
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

Theorem mergesortc_worst:
  big_oh mergesortc_worst_time (fun n => n * cl_log n).
Proof.
  apply (big_oh_trans mergesortc_worst_time
                      mergesortc_worst_time5
                      (fun n => n * cl_log n)).
  exists 0.
  exists 1.
  intros n _.
  unfold mult; rewrite plus_0_r.
  rewrite worst_01.
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
  apply (big_oh_trans mergesortc_worst_time8
                      mergesortc_worst_time9
                      (fun n => n * cl_log n)).
  apply worst_89.
  exists 0. exists 1. intros n _. unfold mult at 1; rewrite plus_0_r.
  unfold mergesortc_worst_time9.
  omega.
Qed.

Theorem mergesortc_best:
  big_omega mergesortc_best_time (fun n => n * cl_log n).
Proof.
  unfold mergesortc_best_time.
  unfold mergesortc_best_time_c.

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

Program Fixpoint mergesortc_best_time1 n {measure n} :=
  match n with
    | 0 => 1
    | S n' =>
      if even_odd_dec n'
      then (mergesortc_best_time1 n' +
            insert_best_time n' + 2)
      else (split_at_time (div2 n) +
            mergesortc_best_time1 (div2 n) +
            mergesortc_best_time1 (div2 n) +
            merge_best_time (div2 n) (div2 n) + 2)
    end.
Next Obligation. intros. subst n. auto. Defined.
Next Obligation. intros. subst n. auto. Defined.
Next Obligation. intros. subst n. auto. Defined.
Next Obligation. apply lt_wf. Defined.

Corollary mergesort_best:
  big_omega mergesort_best_time (fun n => n * cl_log n).
Proof.
Admitted.
