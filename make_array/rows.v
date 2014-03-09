Require Import Braun.tmonad.monad Braun.common.util Braun.common.le_util.
Require Import Braun.common.big_oh.
Require Import Arith Arith.Le Arith.Lt Peano Arith.Min.
Require Import Coq.Arith.Compare_dec.
Require Import Program.Wf Init.Wf.

Include WfExtensionality.

Definition take_time n len := 
  if le_lt_dec len n 
  then 10 * len + 3
  else 10 * n + 5.

Definition take_result (A:Set) n (xs:list A) (res:list A) c := 
  c = take_time n (length xs).

Load "take_gen.v".

Next Obligation.
  unfold take_result.
  simpl.
  unfold take_time.
  dispatch_if REL REL'.
  omega.
  simpl in REL'.
  inversion REL'.
Qed.

Next Obligation.
  unfold take_result.
  simpl.
  unfold take_time.
  dispatch_if REL REL'.
  inversion REL.
  omega.
Qed.

Next Obligation.
  clear am H1.
  rename H0 into RC.

  unfold take_result in *.
  unfold take_time in *.
  subst an.

  dispatch_if COND1 COND1'; dispatch_if COND2 COND2'.

  simpl; omega.

  simpl in COND2'.
  omega.

  simpl in COND2.
  apply le_S_n in COND2.
  omega.

  omega.
Qed.

Definition drop_time n len :=
  if le_lt_dec n len
  then 8 * n + 3
  else 8 * len + 5.

Definition drop_result (A:Set) n (xs:list A) (res:list A) c := 
  c = drop_time n (length xs) /\
  ((length xs) < n -> length res = 0) /\
  (n <= (length xs)  -> length res = (length xs) - n).

Load "drop_gen.v".

Next Obligation.
  unfold drop_result.
  split.
  unfold drop_time.
  dispatch_if COND COND'; omega.

  split; intros REL.
  inversion REL.
  omega.
Qed.

Next Obligation.
  unfold drop_result.
  split.
  simpl.
  unfold drop_time.
  dispatch_if COND COND'; omega.

  split; intros REL.
  simpl.
  omega.
  simpl in REL.
  inversion REL.
Qed.

Next Obligation.
  clear am H1.
  rename H0 into RC.

  unfold drop_result in *.
  destruct RC as [ANEQ [SHORT LONG]].

  split.
  subst an.
  simpl.
  unfold drop_time.
  dispatch_if COND COND'; dispatch_if COND2 COND2'; omega.

  split; intros REL.
  simpl in REL.
  apply lt_S_n in REL.
  apply SHORT in REL.
  omega.
  
  simpl in REL.
  apply le_S_n in REL.
  apply LONG in REL.
  simpl; omega.
Qed.

Program Fixpoint rows_time (k:nat) (len:nat) {measure len} :=
  match k with
    | 0 => 3
    | S _ =>
      match len with
        | 0 => 5
        | S _ => take_time k len +
                 drop_time k len +
                 rows_time (2*k) (len - k) +
                 20
      end
  end.
Next Obligation.
  omega.
Qed.

Definition rows_result (A:Set) (k:nat) (xs:list A) (res:list (nat * list A)) c :=
  c = rows_time k (length xs).

Load "rows_gen.v".

Lemma rows_time_0n : forall n, rows_time 0 n = 3.
Proof.
  intros n.
  unfold rows_time.
  unfold_sub rows_time_func (rows_time_func (existT (fun _ : nat => nat) 0 n)).
  simpl.
  omega.
Qed.

Lemma rows_time_S0 : forall n, rows_time (S n) 0 = 5.
Proof.
  intros n.
  unfold rows_time.
  unfold_sub rows_time_func (rows_time_func (existT (fun _ : nat => nat) (S n) 0)).
  simpl.
  omega.
Qed.

Lemma rows_time_SS : 
  forall k len,
    rows_time (S k) (S len) = 
    take_time (S k) (S len) +
    drop_time (S k) (S len) +
    rows_time (2*(S k)) ((S len) - (S k)) +
    20.
Proof.
  intros k' len'.
  unfold rows_time.
  unfold_sub rows_time_func (rows_time_func (existT (fun _ : nat => nat) (S k') (S len'))).
  simpl.
  fold_sub rows_time_func.
  reflexivity.
Qed.

Next Obligation.
Proof.
  unfold rows_result.
  rewrite rows_time_0n.
  omega.
Qed.

Next Obligation.
Proof.
  unfold rows_result.
  simpl.
  rewrite rows_time_S0.
  reflexivity.
Qed.

Next Obligation.
Proof.
  rename H into DROP_RES.

  unfold drop_result in DROP_RES.

  replace (length (wildcard' :: wildcard'0)) with (S (length wildcard'0)) in *;
    [|simpl;omega].
  remember (length dropped) as l1.
  remember (length wildcard'0) as l2.
  destruct DROP_RES as [AMEQ [L2SMALL L2BIG]].

  destruct (le_lt_dec (S n) (S l2)); rename l into LT.
  
  apply L2BIG in LT.
  rewrite LT.
  omega.

  apply L2SMALL in LT.
  rewrite LT.
  omega.
Qed.

Next Obligation.
  clear am1 H3.
  clear am H5.
  clear am0 H4.
  rename H0 into ROWSR.
  rename H1 into DROPR.
  rename H2 into TAKER.
  clear rows.

  unfold rows_result.
  simpl.
  rewrite rows_time_SS.
  unfold rows_result in *.
  unfold drop_result in *.
  unfold take_result in *.
  simpl in DROPR.
  destruct DROPR as [AN0EQ [SHORT LONG]].
  simpl in TAKER.

  replace (2 * (S n)) with (S n + (S n + 0));[|omega].

  destruct (le_lt_dec (S n) (S (length wildcard'0)));
    rename l into THING.
  apply LONG in THING; clear SHORT LONG.
  
  replace (S (length wildcard'0) - S n) with ((length wildcard'0) - n);[|omega].
  rewrite <- THING.
  omega.

  replace (S (length wildcard'0) - S n) with 0; [|omega].
  apply SHORT in THING;clear SHORT LONG.
  rewrite THING in ROWSR.
  omega.
Qed.

Program Fixpoint rows_time2 (k:nat) (len:nat) {measure len} :=
  match k with
    | 0 => 1
    | S _ =>
      match len with
        | 0 => 1
        | S _ => (min k len) + rows_time2 (2*k) (len - k)
      end
  end.
Next Obligation.
  omega.
Qed.

Lemma rows_time2_0n : forall n, rows_time2 0 n = 1.
Proof.
  intros n.
  unfold rows_time2.
  unfold_sub rows_time2_func (rows_time2_func (existT (fun _ : nat => nat) 0 n)).
  simpl.
  omega.
Qed.

Lemma rows_time2_S0 : forall n, rows_time2 (S n) 0 = 1.
Proof.
  intros n.
  unfold rows_time2.
  unfold_sub rows_time2_func (rows_time2_func (existT (fun _ : nat => nat) (S n) 0)).
  simpl.
  omega.
Qed.

Lemma rows_time2_SS : 
  forall k len,
    rows_time2 (S k) (S len) = min (S k) (S len) + rows_time2 (2*(S k)) ((S len) - (S k)).
Proof.
  intros k' len'.
  unfold rows_time2.
  unfold_sub rows_time2_func (rows_time2_func (existT (fun _ : nat => nat) (S k') (S len'))).
  simpl.
  fold_sub rows_time2_func.
  reflexivity.
Qed.

Lemma rows_time12 : forall k, big_oh (fun n => rows_time k n) (fun n => rows_time2 k n).
  exists 0.
  exists 48.
  intros n LT; clear LT.
  generalize dependent k.

  apply (well_founded_induction 
           lt_wf
           (fun n => 
              forall k,  rows_time k n <= 48 * rows_time2 k n)).
  clear n; intros n IND.
  intros k.
  destruct k.

  rewrite rows_time2_0n.
  rewrite rows_time_0n.
  omega.

  destruct n.

  rewrite rows_time2_S0.
  rewrite rows_time_S0.
  omega.

  rewrite rows_time2_SS.
  rewrite rows_time_SS.
  rewrite mult_plus_distr_l.

  apply (le_trans (take_time (S k) (S n) + drop_time (S k) (S n) +
                   rows_time (2 * S k) (S n - S k) + 20)
                  (take_time (S k) (S n) + drop_time (S k) (S n) +
                   48 * rows_time2 (2 * S k) (S n - S k) + 20)
                  (48 * min (S k) (S n) + 48 * rows_time2 (2 * S k) (S n - S k))).
  apply le_plus_left.
  apply le_plus_right.
  apply IND.
  omega.
  rewrite plus_comm.
  rewrite plus_assoc.
  apply le_plus_left.
  unfold take_time.
  unfold drop_time.
  dispatch_if COND1 COND1'; dispatch_if COND2 COND2'.
  assert (k = n);[omega|].
  subst.
  rewrite min_idempotent.
  omega.
  rewrite min_r; auto.
  omega.
  rewrite min_l; auto.
  omega.
  intuition.
Qed.

Lemma rows_time2_linear : forall k, (big_oh (fun n => rows_time2 k n) (fun n => n+1)).
  exists 0.
  exists 1.
  intros n.
  intros LT.
  clear LT.
  unfold mult; rewrite plus_0_r.
  generalize dependent k.
  apply (well_founded_induction 
           lt_wf
           (fun n =>
              forall k,
                rows_time2 k n <= n + 1)).
  clear n; intros n IND k.
  destruct k.
  rewrite rows_time2_0n.
  omega.
  
  destruct n.
  rewrite rows_time2_S0.
  omega.

  rewrite rows_time2_SS.

  apply (le_trans (min (S k) (S n) + rows_time2 (2 * S k) (S n - S k))
                  (min (S k) (S n) + ((S n - S k)+1))
                  (S n + 1)).
  apply le_plus_right.
  apply IND; omega.
  
  destruct (le_lt_dec (S k) (S n)).
  rewrite min_l;auto.
  omega.
  rewrite min_r;omega.
Qed.

Lemma rows_time_linear : forall k, big_oh (fun n => rows_time k n) (fun n => n).
  intros k.
  apply (big_oh_trans (fun n => rows_time k n)
                      (fun n => rows_time2 k n)
                      (fun n => n)).
  apply rows_time12.
  apply (big_oh_trans (fun n : nat => rows_time2 k n) 
                      (fun n : nat => n+1)
                      (fun n : nat => n)).
  apply rows_time2_linear.
  exists 1.
  exists 2.
  intros.
  destruct n; omega.
Qed.

Definition rows1_time (len:nat) := rows_time 1 len + 4.

Definition rows1_result (A:Set) (xs:list A) (res:list (nat * list A)) c :=
  c = rows1_time (length xs).

Load "rows1_gen.v".

Next Obligation.
  clear am H1.
  unfold rows1_result.
  unfold rows_result in *.
  unfold rows1_time.
  omega.
Qed.

Theorem rows1_time_linear : big_oh rows1_time (fun n => n).
Proof.
  apply (big_oh_trans rows1_time
                      (fun n => rows_time 1 n)
                      (fun n => n)).
  exists 1.
  exists 4.
  intros n LT.
  unfold rows1_time.
  destruct n.
  intuition.
  replace 1 with (S 0);[|auto].
  rewrite rows_time_SS.
  omega.

  apply rows_time_linear.
Qed.
