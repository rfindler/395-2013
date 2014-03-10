Require Import Braun.tmonad.monad Braun.common.util Braun.common.le_util.
Require Import Braun.common.big_oh Braun.common.braun.
Require Import Braun.make_array.take_drop_split.
Require Import Arith Arith.Le Arith.Lt Peano Arith.Min.
Require Import Coq.Arith.Compare_dec.
Require Import Program.Wf Init.Wf.

Include WfExtensionality.

Definition zip_with_3_bt_node_time len := 16 * len + 3.
Hint Unfold zip_with_3_bt_node_time.

Definition zip_with_3_bt_node_result
           (A:Set) (xs:list A)
           (ts1:list (@bin_tree A)) (ts2:list (@bin_tree A))
           (res:list (@bin_tree A)) c := 
  length xs <= length ts1 /\ length xs <= length ts2 ->
  c = zip_with_3_bt_node_time (length xs).
Hint Unfold zip_with_3_bt_node_result.

Load "zip_with_3_bt_node_gen.v".

Next Obligation.
  unfold zip_with_3_bt_node_result.
  intros LENS.
  destruct LENS as [L1 L2].
  simpl in L1.
  intuition.
Qed.

Next Obligation.
  unfold zip_with_3_bt_node_result.
  intros LENS.
  destruct LENS as [L1 L2].
  simpl in L2.
  intuition.
Qed.

Next Obligation.
  clear am H1.
  rename H0 into ZWRES.

  unfold zip_with_3_bt_node_result in *.
  unfold zip_with_3_bt_node_time in *.
  simpl.
  omega.
Qed.

Lemma zip_with_3_bt_node_linear : big_oh zip_with_3_bt_node_time (fun n => n).
  unfold zip_with_3_bt_node_time.
  apply big_oh_plus; auto.
  exists 0. exists 16. intros; omega.
Qed.

Definition build_time k len := 
  pad_drop_time (2*k) +
  split_time (2*k) k +
  zip_with_3_bt_node_time len +
  16.
Hint Unfold build_time.

Definition build_result 
           (A:Set)
           (pr:nat * list A) 
           (ts : list (@bin_tree A))
           (res : list (@bin_tree A))
           c := 
  (length (snd pr) <= fst pr) -> 
  c = build_time (fst pr) (length (snd pr)).

Hint Unfold build_result.

Load "build_gen.v".

Next Obligation.
  clear am am0 am1 H3 H4 H5.
  rename H0 into ZWres.
  rename H2 into PDres.
  rename H1 into SPLITres.
  unfold build_result.
  unfold build_time.
  unfold zip_with_3_bt_node_result in *.
  unfold pad_drop_result in *.
  unfold split_result in *.
  simpl in SPLITres.
  simpl.
  destruct SPLITres as [AN0eq [SHORT LONG]].
  clear SHORT.
  destruct PDres as [AN1eq LENpadded].
  rewrite LENpadded in *.
  replace (n + (n+0)-n) with n in LONG;[|omega].
  assert (length l = n /\ length l0 = n) as LENS;[apply LONG; omega|clear LONG].
  destruct LENS as [LENl LENl0].
  rewrite LENl in *.
  rewrite LENl0 in *.
  clear LENl LENl0.
  intros LENl1.
  assert (an = zip_with_3_bt_node_time (length l1));[apply ZWres; auto|].
  subst an1 an0 an.
  omega.
Qed.

