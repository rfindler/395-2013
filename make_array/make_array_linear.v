Require Import Braun.tmonad.monad Braun.common.util Braun.common.le_util.
Require Import Braun.common.big_oh Braun.common.braun Braun.fold.fold.
Require Import Braun.make_array.rows Braun.make_array.take_drop_split.
Require Import Braun.make_array.build.
Require Import Arith Arith.Le Arith.Lt Peano Arith.Min.
Require Import Coq.Arith.Compare_dec List.
Require Import Program.Wf Init.Wf.

Include WfExtensionality.

Fixpoint foldr_build_time (l : list (nat * nat)) := 
  match l with
    | nil => 3
    | cons (pair k len) rst => 
      build_time k len + 
      9 + 
      foldr_build_time rst
  end.
Hint Unfold foldr_build_time.

Definition foldr_build_result 
           (A:Set) 
           (base : list (@bin_tree A))
           (l : list (nat * (list A)))
           (res : list (@bin_tree A))
           c := 
  (forall k l2, In (pair k l2) l -> length l2 <= k)
  -> c = foldr_build_time 
           (map (fun x => (pair (fst x) (length (snd x))))
                l).
Hint Unfold foldr_build_result.

Load "foldr_build_gen.v".

Next Obligation.
  clear am H3 am0 H2.
  rename H0 into BR.
  rename H1 into FBR.

  unfold build_result in *.
  unfold foldr_build_result in *.
  intros LES.
  simpl.
  simpl in BR.
  assert (length l0 <= n) as L0N.
  remember (LES n l0).
  apply l.
  constructor.
  reflexivity.
  apply BR in L0N.
  assert (an0 = foldr_build_time (map (fun x => (fst x, length (snd x))) xs)).
  apply FBR.
  intros k l2.
  remember (LES k l2).
  intros IN.
  apply l.
  right; auto.
  omega.
Qed.

Definition make_array_linear_time len := 
  rows1_time len +
  foldr_build_time (rows_sizes 1 len) +
  10.

Definition make_array_linear_result (A:Set) (xs:list A) (res:@bin_tree A) c := 
  c = make_array_linear_time (length xs).
Hint Unfold make_array_linear_result.

Load "make_array_linear_gen.v".

Lemma make_array_linear_time_helper : 
  forall (A : Set)
         (xs : list A)
         (the_rows : list (nat * list A))
         (an : nat)
         (FBR : foldr_build_result A (bt_mt :: nil) the_rows nil an)
         (an0 : nat)
         (RR : rows1_result A xs the_rows an0),
    make_array_linear_result A xs bt_mt (an0 + (an + 10)).
  intros.
  
  unfold foldr_build_result in *.
  unfold rows1_result in *.
  unfold make_array_linear_result.
  unfold make_array_linear_time.
  destruct RR as [AN0 [INSTUFF MAPEQ]].
  rewrite MAPEQ in FBR.
  assert (an = foldr_build_time (rows_sizes 1 (length xs))) as ANEQ.
  apply FBR; auto.
  omega.
Qed.

Next Obligation. 
  clear am0 am H2 H3.
  rename H0 into FBR.
  rename H1 into RR.
  apply (make_array_linear_time_helper A xs the_rows an FBR an0 RR).
Qed.

Next Obligation.
  clear am0 am H2 H3.
  rename H0 into FBR.
  rename H1 into RR.
  apply (make_array_linear_time_helper A xs the_rows an FBR an0 RR).
Qed.

Program Fixpoint fbt_rs_1 k len {measure len} :=
  match k with 
    | 0 => 3
    | S _ => 
      match len with
        | 0 => 3
        | S _ =>
          build_time k (min k len) +
          9 +
          fbt_rs_1 (2*k) (len-k)
      end
  end.
Next Obligation. omega. Qed.

Lemma fbt_rs_1_0n : 
  forall n,
    fbt_rs_1 0 n = 3.
Proof.
  intros n.
  unfold fbt_rs_1.
  unfold_sub fbt_rs_1_func
             (fbt_rs_1_func
                (existT (fun _ : nat => nat) 0 n)).
  simpl.
  reflexivity.
Qed.

Lemma fbt_rs_1_S0 :
  forall k',
    fbt_rs_1 (S k') 0 = 3.
  intros k'.
  unfold fbt_rs_1.
  unfold_sub fbt_rs_1_func
             (fbt_rs_1_func
                (existT (fun _ : nat => nat) (S k') 0) = 3).
  simpl.
  reflexivity.
Qed.

Lemma fbt_rs_1_SS :
  forall k' len',
    fbt_rs_1 (S k') (S len') = 
    build_time (S k') (min (S k') (S len')) +
    9 +
    fbt_rs_1 (2*(S k')) ((S len')-(S k')).
Proof.
  intros k' len'.
  unfold fbt_rs_1 at 1.
  unfold_sub fbt_rs_1_func
             (fbt_rs_1_func
                (existT (fun _ : nat => nat) (S k') (S len'))).
  simpl.
  fold_sub fbt_rs_1_func.
  reflexivity.
Qed.

Lemma fbt_rs_01 : 
  forall k,
    big_oh (fun n => foldr_build_time (rows_sizes k n))
           (fun n => fbt_rs_1 k n).
Proof.
  intros k.
  exists 0.
  exists 1.
  intros n LT; clear LT.
  unfold mult; rewrite plus_0_r.
  replace (foldr_build_time (rows_sizes k n)) 
  with (fbt_rs_1 k n).
  omega.
  generalize dependent k.
  apply (well_founded_induction 
           lt_wf
           (fun n => 
              forall k,
                fbt_rs_1 k n =
                foldr_build_time (rows_sizes k n))).
  clear n; intros n IND.

  intros k.
  destruct k.
  rewrite fbt_rs_1_0n.
  simpl.
  reflexivity.

  destruct n.
  rewrite fbt_rs_1_S0.
  simpl.
  reflexivity.

  rewrite fbt_rs_1_SS.
  rewrite IND; try omega.
  rewrite rows_sizes_SS.
  simpl.
  omega.
Qed.

Program Fixpoint fbt_rs_2 k len {measure len} :=
  match k with 
    | 0 => 3
    | S _ => 
      match len with
        | 0 => 3
        | S _ =>
          build_time k k +
          9 +
          fbt_rs_2 (2*k) (len-k)
      end
  end.
Next Obligation. omega. Qed.

Lemma fbt_rs_2_0n : 
  forall n,
    fbt_rs_2 0 n = 3.
Proof.
  intros n.
  unfold fbt_rs_2.
  unfold_sub fbt_rs_2_func
             (fbt_rs_2_func
                (existT (fun _ : nat => nat) 0 n)).
  simpl.
  reflexivity.
Qed.

Lemma fbt_rs_2_S0 :
  forall k',
    fbt_rs_2 (S k') 0 = 3.
  intros k'.
  unfold fbt_rs_2.
  unfold_sub fbt_rs_2_func
             (fbt_rs_2_func
                (existT (fun _ : nat => nat) (S k') 0) = 3).
  simpl.
  reflexivity.
Qed.

Lemma fbt_rs_2_SS :
  forall k' len',
    fbt_rs_2 (S k') (S len') = 
    build_time (S k') (S k') +
    9 +
    fbt_rs_2 (2*(S k')) ((S len')-(S k')).
Proof.
  intros k' len'.
  unfold fbt_rs_2 at 1.
  unfold_sub fbt_rs_2_func
             (fbt_rs_2_func
                (existT (fun _ : nat => nat) (S k') (S len'))).
  simpl.
  fold_sub fbt_rs_2_func.
  reflexivity.
Qed.

Lemma fbt_rs_12 : 
  forall k,
    big_oh (fun n => fbt_rs_1 k n)
           (fun n => fbt_rs_2 k n).
Proof.
  intros k.
  exists 0.
  exists 2.
  intros n LT.
  clear LT.
  generalize dependent k.
  apply (well_founded_induction
           lt_wf
           (fun n => 
              forall k,
                fbt_rs_1 k n <= 2 * fbt_rs_2 k n)).
  clear n; intros n IND k.

  destruct k.
  rewrite fbt_rs_1_0n.
  rewrite fbt_rs_2_0n.
  omega.

  destruct n.
  rewrite fbt_rs_1_S0.
  rewrite fbt_rs_2_S0.
  omega.

  rewrite fbt_rs_1_SS.
  rewrite fbt_rs_2_SS.

  apply (le_trans (build_time (S k) (min (S k) (S n)) + 9 + fbt_rs_1 (2 * S k) (S n - S k))
                  (build_time (S k) (min (S k) (S n)) + 9 + 2* (fbt_rs_2 (2 * S k) (S n - S k)))
                  (2 * (build_time (S k) (S k) + 9 + fbt_rs_2 (2 * S k) (S n - S k)))).
  apply le_plus_right.
  apply IND.
  omega.
  rewrite mult_plus_distr_l.
  apply le_plus_left.
  rewrite mult_plus_distr_l.
  replace (2*9) with (9+9);[|omega].
  rewrite plus_assoc.
  apply le_plus_left.
  unfold mult.
  rewrite plus_0_r.
  unfold build_time.
  repeat (rewrite <- plus_assoc).
  repeat (apply le_plus_right).
  unfold zip_with_3_bt_node_time.
  destruct (le_lt_dec k n).
  rewrite min_l.
  omega.
  omega.
  rewrite min_r; try omega.
Qed.  

Lemma foldr_build_linear : 
  big_oh (fun n : nat => foldr_build_time (rows_sizes 1 n))
         (fun n : nat => n).
Proof.
  apply (big_oh_trans (fun n : nat => foldr_build_time (rows_sizes 1 n))
                      (fun n => fbt_rs_1 1 n)
                      (fun n : nat => n)).
  apply fbt_rs_01.
  apply (big_oh_trans (fun n => fbt_rs_1 1 n)
                      (fun n => fbt_rs_2 1 n)
                      (fun n : nat => n)).
  apply fbt_rs_12.
  admit.
Qed.

Theorem make_array_linear_linear : big_oh make_array_linear_time (fun n => n).
  unfold make_array_linear_time.
  apply big_oh_plus;auto.
  apply big_oh_plus.
  apply rows1_time_linear.
  apply foldr_build_linear.
Qed.

