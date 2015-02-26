Require Import Braun.common.util Braun.common.le_util Braun.common.same_structure.
Require Import Braun.common.log Braun.common.big_oh Braun.common.pow.
Require Import Braun.monad.monad.
Require Import Program.
Require Import Omega.
Require Import Max.
Require Import Div2.
Require Import Relations_1.
Require Import Braun.clrs.rbtree.

Definition bst_search_time (n:nat) :=
  19 * n + 3.

Definition bst_search_result (A:Set)
  (A_cmp:A -> A -> Prop)
  (A_asym:forall x y, A_cmp x y -> ~ A_cmp y x)
  (A_trans:Transitive A A_cmp)
  (A_cmp_dec:
    forall (x y:A),
      { A_cmp x y } + { A_cmp y x })
  (A_eq_dec:
    forall (x y:A),
      { x = y } + { x <> y })
  (x:A) (ct:CTree A) (res:bool) (c:nat) :=
  forall (min_a max_a:A)
         (MIN:A_cmp min_a x)
         (MAX:A_cmp x max_a)
         (BST:IsBST A_cmp ct min_a max_a),
    (res = true -> IsMember x ct) /\
    (res = false -> ~ IsMember x ct) /\
    1 <= c <= bst_search_time (height ct).

Load "bst_search_gen.v".

Next Obligation.
 unfold bst_search_result, bst_search_time.
 intros min_a max_a CMPax CMPxa BST.
 split.
 intros EQ. inversion EQ.
 simpl.
 split; try omega.
 intros _ IM.
 inversion IM.
Qed.

Next Obligation.
 unfold bst_search_result, bst_search_time.
 intros min_a max_a CMPax CMPxa BST.
 split.
 intros _. eauto.
 split.
 intros EQ. congruence.
 simpl (height (CT_node A l c v r)).
 rewrite mult_succ_r.
 omega.
Qed.

Obligation Tactic := idtac.
Next Obligation.
  unfold bst_search_result, bst_search_time.
  intros A A_cmp A_asym A_trans A_cmp_dec A_eq_dec x ct.
  intros l c v r EQ. subst ct.
  intros NEQ _ CMPxv _.
  intros res.
  intros _.
  intros xm EQ. simpl in EQ. subst xm.
  intros an REC.
  intros min_a max_a CMPax CMPxa BST.
  edestruct REC as [IMt [IMf AN]].
   apply CMPax.
   apply CMPxv.
   inversion BST. subst. auto.
  clear REC.

  split.
  intros EQ. apply IMt in EQ. eauto.
  split.
  intros EQ. apply IMf in EQ.
  intros IM. inversion IM; subst; auto.
  rename H0 into IMr.
  inversion BST.
  subst.
  rename H3 into BSTl.
  rename H6 into CMPav.
  rename H7 into CMPva.
  rename H8 into BSTr.
  
  edestruct IsMember_impl_bounds.
  apply A_trans.
  apply BSTr.
  apply IMr.
  rename H into CMPvx.
  clear H0.
  eapply A_asym.
  apply CMPvx.
  auto.

  simpl (height (CT_node A l c v r)).
  remember (height l) as L.
  remember (height r) as R.
  clear HeqR HeqL IMf IMt CMPxv NEQ BST r v c l CMPxa CMPax max_a min_a x A_eq_dec
    A_cmp_dec A_trans A_asym A_cmp A res.
  rewrite mult_succ_r.
  rewrite <- plus_assoc.
  replace (19 + 3) with 22; try omega.
  apply max_case_strong.
  intros LE. clear LE R. omega.
  intros LE. omega.
Qed.
Obligation Tactic := program_simpl.

Obligation Tactic := idtac.
Next Obligation.
  unfold bst_search_result, bst_search_time.
  intros A A_cmp A_asym A_trans A_cmp_dec A_eq_dec x ct.
  intros l c v r EQ. subst ct.
  intros NEQ _ CMPvx _.
  intros res.
  intros _.
  intros xm EQ. simpl in EQ. subst xm.
  intros an REC.
  intros min_a max_a CMPax CMPxa BST.
  edestruct REC as [IMt [IMf AN]].
   apply CMPvx.
   apply CMPxa.
   inversion BST. subst. auto.
  clear REC.
  split.
  intros EQ. apply IMt in EQ. eauto.
  split.
  intros EQ. apply IMf in EQ.
  intros IM. inversion IM; subst; auto.
  rename H0 into IMl.
  inversion BST.
  subst.
  rename H3 into BSTl.
  rename H6 into CMPav.
  rename H7 into CMPva.
  rename H8 into BSTr.
  
  edestruct IsMember_impl_bounds.
  apply A_trans.
  apply BSTl.
  apply IMl.
  clear H.
  rename H0 into CMPxv.
  eapply A_asym.
  apply CMPvx.
  auto.

  simpl (height (CT_node A l c v r)).
  remember (height l) as L.
  remember (height r) as R.
  clear HeqR HeqL IMf IMt CMPvx NEQ BST r v c l CMPxa CMPax max_a min_a x A_eq_dec
    A_cmp_dec A_trans A_asym A_cmp A res.
  apply max_case_strong.
  intros LE. omega.
  intros LE. clear LE L. omega.
Qed.
Obligation Tactic := program_simpl.

Corollary rbbst_search_time_bound_black_height:
  forall A (ct:CTree A) n,
    IsRB ct n ->
    bst_search_time (height ct) <= 38 * n + 22.
Proof.
  intros A ct n IR.
  unfold bst_search_time.
  apply IsRB_impl_height_no_color in IR.
  omega.
Qed.

Corollary bst_search_time_theta:
  big_theta bst_search_time (fun n => n).
Proof.
  unfold bst_search_time.
  unfold big_theta. split.
  unfold big_oh.
  exists 3 20.
  intros n LE.
  destruct n as [|[|[|n]]]; try omega.

  apply big_oh_rev.
  exists 0 1.
  intros n LE. omega.
Qed.
