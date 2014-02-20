Require Import Braun.common.braun Braun.common.util Braun.common.same_structure.
Require Import Braun.common.log Braun.common.big_oh.
Require Import Braun.logical.sequence Braun.logical.list_util.
Require Import Braun.tmonad.monad.
Require Import Program.
Require Import Omega.

Definition insert_time n := 9 * fl_log n + 6.

Definition insert_result (A : Set) (i : A) (b:@bin_tree A)
           (b':@bin_tree A) c :=
     (forall n,
        Braun b n ->
        (Braun b' (S n) /\
         (forall xs, SequenceR b xs -> SequenceR b' (i::xs)) /\
         c = insert_time n)).

Load "insert_gen.v".

Next Obligation.
  unfold insert_result.
  intros n B.
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
  clear H1 am.
  rename H0 into IH.
  unfold insert_result in *.

  intros n B.

  invclr B.
  rename H2 into BP.
  rename H4 into Bs.
  rename H5 into Bt.

  apply IH in Bt.
  destruct Bt as [Bst [SRst EQ]].
  subst an.

  repeat constructor.

  (* braun *)
  replace (S (s_size + t_size + 1)) with ((S t_size) + s_size + 1); try omega.
  eapply B_node; auto; try omega.

  (* correctness *)
  intros xs SR.
  invclr SR.
  rename H3 into SRs.
  rename H4 into SRt.
  rewrite interleave_case2.
  eapply SR_node; eauto.

  (* running time*)
  unfold insert_time.
  rewrite <- braun_invariant_implies_fl_log_property; auto.
  omega.
Qed.

Theorem insert_time_log:
  big_oh insert_time fl_log.
Proof.
  apply (big_oh_trans insert_time
                      (fun n => fl_log n + 6)
                      fl_log).
  exists 0.
  exists 9.
  intros n LE.
  unfold insert_time.
  omega.

  exists 1.
  exists 7.
  intros n LE.
  destruct n; intuition.
  clear LE.
  rewrite <- fl_log_div2.
  unfold mult.
  omega.
Qed.
