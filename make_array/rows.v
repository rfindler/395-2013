Require Import Braun.tmonad.monad Braun.common.util Braun.common.le_util.
Require Import Braun.common.big_oh Braun.make_array.take_drop_split.
Require Import Arith Arith.Le Arith.Lt Peano Arith.Min.
Require Import Coq.Arith.Compare_dec List.
Require Import Program.Wf Init.Wf.

Include WfExtensionality.

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
Next Obligation. omega. Qed.

Program Fixpoint rows_sizes k len {measure len} :=
  match k with
    | 0 => nil
    | S _ =>
      match len with
        | 0 => nil
        | S _ => 
          (cons (pair k (min k len)) (rows_sizes (2*k) (len - k)))
      end
  end.
Next Obligation. omega. Qed.

Definition rows_result (A:Set) (k:nat) (xs:list A) (res:list (nat * list A)) c :=
  c = rows_time k (length xs) /\
  (forall n lst, In (n,lst) res -> length lst <= n) /\
  (map (fun x : nat * list A => (fst x, length (snd x))) res) = 
  rows_sizes k (length xs).

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

Lemma rows_sizes_0n : forall n, rows_sizes 0 n = nil.
Proof.
  intros n.
  unfold rows_sizes.
  unfold_sub rows_sizes_func (rows_sizes_func (existT (fun _ : nat => nat) 0 n)).
  simpl.
  reflexivity.
Qed.

Lemma rows_sizes_S0 : forall k, rows_sizes (S k) 0 = nil.
Proof.
  intros k.
  unfold rows_sizes.
  unfold_sub rows_sizes_func (rows_sizes_func (existT (fun _ : nat => nat) (S k) 0)).
  simpl.
  reflexivity.
Qed.

Lemma rows_sizes_SS : forall k len, 
                        rows_sizes (S k) (S len) = 
                        (cons (pair (S k) (min (S k) (S len)))
                              (rows_sizes (2*(S k)) ((S len) - (S k)))).
Proof.
  intros k len.
  unfold rows_sizes at 1.
  unfold_sub rows_sizes_func (rows_sizes_func (existT (fun _ : nat => nat) (S k) (S len))).
  simpl.
  fold_sub rows_sizes_func.
  unfold rows_sizes.
  reflexivity.
Qed.

Next Obligation.
Proof.
  unfold rows_result.
  split.
  rewrite rows_time_0n.
  omega.
  split.
  intros n lst IN.
  destruct IN.
  simpl.
  rewrite rows_sizes_0n.
  reflexivity.
Qed.

Next Obligation.
Proof.
  unfold rows_result.
  split.
  simpl.
  rewrite rows_time_S0.
  reflexivity.
  split.
  intros n0 lst IN.
  destruct IN.
  simpl.
  rewrite rows_sizes_S0.
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
Proof.
  clear am1 H3.
  clear am H5.
  clear am0 H4.
  rename H0 into ROWSR.
  rename H1 into DROPR.
  rename H2 into TAKER.
  clear rows.

  unfold rows_result.

  split.

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

  split.

  intros n0 lst IN.
  unfold rows_result in *.
  inversion IN.
  inversion H.
  subst n0 lst.
  clear IN H.
  destruct TAKER as [AN1eq [SHORT LONG]].
  destruct (le_lt_dec (S n) (length (wildcard' :: wildcard'0))); omega.
  intuition.

  simpl.
  unfold rows_result in *.
  destruct ROWSR as [ANeq [IN MAP]].
  rewrite MAP.
  rewrite rows_sizes_SS.
  unfold mult.

  unfold drop_result in *.
  unfold take_result in *.
  simpl in DROPR.
  simpl in TAKER.

  destruct DROPR as [AN0eq [SHORT1 LONG1]].
  destruct TAKER as [AN1eq [SHORT2 LONG2]].

  destruct (le_lt_dec (S n) (S (length wildcard'0))).

  remember (LONG1 l) as L1.
  remember (LONG2 l) as L2.
  
  rewrite L1. rewrite L2.
  rewrite min_l; auto.

  remember (SHORT1 l) as S1.
  remember (SHORT2 l) as S2.
  rewrite S1. rewrite S2.
  rewrite min_r; try omega.
  replace (S (length wildcard'0) - S n) with 0.
  reflexivity.
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
Proof.
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
  unfold_sub rows_time2_func
             (rows_time2_func (existT (fun _ : nat => nat) (S k') (S len'))).
  simpl.
  fold_sub rows_time2_func.
  reflexivity.
Qed.

Lemma rows_time12 : forall k, big_oh (fun n => rows_time k n) (fun n => rows_time2 k n).
Proof.
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
Proof.
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
Proof.
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
  c = rows1_time (length xs) /\
  (forall n lst, In (n,lst) res -> length lst <= n) /\
  (map (fun x : nat * list A => (fst x, length (snd x))) res) = 
  rows_sizes 1 (length xs).

Load "rows1_gen.v".

Next Obligation.
Proof.
  clear am H1.
  rename H0 into RR.
  unfold rows1_result.
  unfold rows_result in *.
  unfold rows1_time.
  split.
  omega.
  destruct RR as [ANeq [INSTUFF MAPEQ]].
  split; assumption.
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
