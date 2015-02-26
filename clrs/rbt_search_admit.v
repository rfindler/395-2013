Require Import Braun.clrs.rbt_search.

Corollary rbbst_search_time_bound_count:
  forall A (ct:CTree A) bh,
    IsRB ct bh ->
    bst_search_time (height ct) <= 38 * cl_log (count ct + 1) + 22.
Proof.
  intros A ct bh IR.
  eapply le_trans.
  apply rbbst_search_time_bound_black_height.
  apply IR.
  apply le_add; auto.
  apply le_mult; auto.
  apply rb_black_height_impl_count.
  auto.
Qed.
