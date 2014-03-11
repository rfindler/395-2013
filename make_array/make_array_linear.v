Require Import Braun.tmonad.monad Braun.common.util Braun.common.le_util.
Require Import Braun.common.big_oh Braun.common.braun Braun.fold.fold.
Require Import Braun.make_array.rows Braun.make_array.take_drop_split.
Require Import Braun.make_array.build.
Require Import Arith Arith.Le Arith.Lt Peano Arith.Min.
Require Import Coq.Arith.Compare_dec List.

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

Lemma foldr_build_linear : 
  big_oh (fun n : nat => foldr_build_time (rows_sizes 1 n))
         (fun n : nat => n).
  admit.
Qed.

Theorem make_array_linear_linear : big_oh make_array_linear_time (fun n => n).
  unfold make_array_linear_time.
  apply big_oh_plus;auto.
  apply big_oh_plus.
  apply rows1_time_linear.
  apply foldr_build_linear.
Qed.
