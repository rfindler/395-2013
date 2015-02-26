Require Import Braun.common.util Braun.common.le_util Braun.common.same_structure.
Require Import Braun.common.log Braun.common.big_oh Braun.common.pow.
Require Import Braun.monad.monad.
Require Import Program.
Require Import Omega.
Require Import Max.
Require Import Div2.
Require Import Relations_1.
Require Import Braun.clrs.rbtree.
Require Import Braun.clrs.rbtree_admit.
Require Import Braun.clrs.rbt_insert.

Corollary rbt_insert_time_bound_count:
  forall A (ct:CTree A) bh,
    IsRB ct bh ->
    rbt_insert_worst (height ct) <= 138 * cl_log (count ct + 1) + 99.
Proof.
  intros A ct bh IR.
  eapply le_trans.
  apply IsRB_impl_height_no_color in IR.
  unfold rbt_insert_worst, rbt_blacken_worst, rbt_insert_inner_worst, rbt_balance_worst.
  simpl (27 + 42).
  rewrite <- plus_assoc.
  simpl (8 + 14).
  rewrite <- plus_assoc.
  simpl (8 + 22).
  apply le_add.
  apply le_mult.
  apply le_refl.
  apply IR.
  apply le_refl.
  replace (69 * (2 * bh + 1)) with (138 * bh + 69); try omega.
  rewrite <- plus_assoc.
  simpl (69+30).
  apply le_add; auto.
  apply le_mult; auto.
  apply rb_black_height_impl_count.
  auto.
Qed.
