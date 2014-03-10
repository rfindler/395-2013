Require Import Braun.tmonad.monad Braun.common.util Braun.common.le_util.
Require Import Braun.common.big_oh Braun.common.braun.
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
  length xs = length ts1 /\ length xs = length ts2 ->
  c = zip_with_3_bt_node_time (length xs).
Hint Unfold zip_with_3_bt_node_result.

Load "zip_with_3_bt_node_gen.v".

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
