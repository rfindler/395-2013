Require Import Braun.common.braun Braun.common.util Braun.common.same_structure.
Require Import Braun.common.log Braun.logical.sequence Braun.logical.list_util.
Require Import Braun.tmonad.monad.
Require Import Program.
Require Import Omega.

Program Fixpoint insert {A:Set} (i:A) (b:@bin_tree A)
: {! b' !:! (@bin_tree A) !<! c !>!
        (forall n,
           Braun b n ->
           (Braun b' (S n) /\
            (forall xs, SequenceR b xs -> SequenceR b' (i::xs)) /\
            c = fl_log n + 1)) !} :=
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
  repeat constructor; auto.

  (* correctness *)
  intros xs SR.
  invclr SR.
  apply SR_singleton.
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
  rename H3 into BP.
  rename H5 into Bs.
  rename H6 into Bt.

  apply IH in Bt.
  destruct Bt as [Bst [SRst EQ]].
  subst xn.
  replace (fl_log t_size + 1) with (S (fl_log t_size)); try omega.
  rewrite fl_log_cl_log_relationship.
  replace (fl_log (s_size + t_size + 1) + 1) with (S (fl_log (s_size + t_size + 1)));
    try omega.
  rewrite fl_log_cl_log_relationship.
  replace (S (s_size + t_size + 1)) with ((S t_size) + s_size + 1); try omega.

  split.
  (* braun *)
  eapply B_node; auto; try omega.

  split.
  (* correctness *)
  intros xs SR.
  invclr SR. 
  rename H4 into SRs.
  rename H5 into SRt.
  rewrite interleave_case2.
  eapply SR_node; eauto.

  (* running time*)
  apply braun_invariant_implies_cl_log_property.
  replace (S t_size) with (t_size + 1); try omega.
Qed.
