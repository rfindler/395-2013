Require Import Braun.tmonad.monad.
Require Import Braun.common.util.
Require Import Arith Arith.Even Arith.Div2.
Require Import Coq.Program.Wf.

(* This file exists only to check that
   the rkt version of sub1 really does
   compute n-1. The running time aspects
   of this function are complex. *)

Definition sub1_result (n:nat) (res:nat) (c:nat) := n-1 = res.
Hint Unfold sub1_result.

Load "sub1_gen.v".

Next Obligation.
  clear H2 am.
  rename H into EW.
  unfold sub1_result in *.
  subst sd2.
  rewrite (even_double (S wildcard')) at 1; auto.
  unfold double.
  remember (div2 (S wildcard')) as x.
  destruct x; try omega.

  destruct wildcard'.
  inversion EW.
  inversion H0.
  simpl in Heqx.
  inversion Heqx.
Qed.
