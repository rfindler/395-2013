Require Import Braun.tmonad.monad Braun.common.util.
Require Import Arith.Le Arith.Lt.
Require Import Coq.Arith.Compare_dec.
Require Import Program.Wf Init.Wf.
Require Import Braun.common.big_oh.

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

Theorem rows_time_linear : big_oh (fun n => rows_time 1 n) (fun n => n).
Proof.
  admit.
Qed.
