(*

This file shows a simplified version of insert, where the correctness
condition is omitted and the "automatically insert the +="
transformation is not used. It is here to aid the exposition in the
paper.

*)

Require Import Braun.common.braun Braun.common.util.
Require Import Braun.common.log Braun.common.big_oh.
Require Import Braun.monad.monad.
Require Import Program.
Require Import Omega.

(* START: insert *)
Program Fixpoint insert {A:Set} (i:A) (b:@bin_tree A)
: {! res !:! @bin_tree A !<! c !>!
     (forall n, Braun b n -> (Braun res (n+1) /\ c = fl_log n + 1)) !} :=
  match b with
    | bt_mt         => += 1; <== (bt_node i bt_mt bt_mt)
    | bt_node j s t => t' <- insert j t;
                       += 1; <== (bt_node i t' s)
  end.
(* STOP: insert *)

Next Obligation.
  rename H0 into B.

  invclr B.
  simpl.
  repeat constructor; auto.
Qed.

Next Obligation.
  clear H2 am.
  rename H0 into IH.
  rename H1 into B.

  invclr B.
  rename H2 into BP.
  rename H4 into Bs.
  rename H5 into Bt.

  apply IH in Bt.
  destruct Bt as [Bst EQ].
  subst an.

  split.

  (* braun *)
  replace (t_size + 1) with (S t_size) in Bst; try omega.
  replace (s_size + t_size + 1 + 1) with ((S t_size) + s_size + 1); try omega.
  eapply B_node; auto; try omega.

  (* running time*)
  rewrite <- braun_invariant_implies_fl_log_property; auto.
Qed.
