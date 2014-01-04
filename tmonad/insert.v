Require Import Braun.common.braun Braun.common.util Braun.common.same_structure.
Require Import Braun.common.log.
Require Import Braun.tmonad.monad.
Require Import Program.
Require Import Omega.

Program Fixpoint insert {A:Set} (i:A) (b:@bin_tree A)
: { b' !:! (@bin_tree A) !<! c !>!
       (forall n,
          Braun b n ->
          (Braun b' (S n) /\
           c = fl_log n + 1)) } :=
  match b with
    | bt_mt =>
      (++ ; (<== (bt_node i bt_mt bt_mt)))
    | bt_node j s t =>
      (st <- (insert j t) ;
       (++ ; (<== (bt_node i st s))))
  end.

Next Obligation.
  rename H into B.

  invclr B.
  split; auto.
  replace 1 with (0 + 0 + 1); try omega.
  eapply B_node; auto; try omega.
Qed.

Lemma same_tree_same_size :
  forall A (s:@bin_tree A) n m,
    Braun s n ->
    Braun s m ->
    n = m.
Proof.
  intros A s n m Bn Bm.
  apply (@same_structure_same_size _ s s); eauto.
Qed.
Hint Rewrite same_tree_same_size.

Next Obligation.
  rename H into IH.
  rename H0 into B.

  invclr B.
  rename H2 into BP.
  rename H4 into Bs.
  rename H5 into Bt.

  apply IH in Bt.
  destruct Bt as [Bst EQ].
  subst xn.
  replace (fl_log t_size + 1) with (S (fl_log t_size)); try omega.
  rewrite fl_log_cl_log_relationship.
  replace (fl_log (s_size + t_size + 1) + 1) with (S (fl_log (s_size + t_size + 1)));
    try omega.
  rewrite fl_log_cl_log_relationship.
  replace (S (s_size + t_size + 1)) with ((S t_size) + s_size + 1); try omega.

  split.
  eapply B_node; auto; try omega.
  apply braun_invariant_implies_cl_log_property.
  replace (S t_size) with (t_size + 1); try omega.
Qed.
