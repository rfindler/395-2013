Require Import Braun.monad.monad Braun.common.log.
Require Import Braun.common.util Braun.common.big_oh Braun.common.le_util.
Require Import Arith Arith.Even Arith.Div2.
Require Import Coq.Program.Wf Arith.Even Arith.Div2 Arith Init.Wf.
Require Import Braun.arith.sub1.

Include WfExtensionality.

Fixpoint sub1_linear_time n :=
  match n with
    | 0 => 3
    | S n' => sub1_time n + sub1_linear_time n' + 7
  end.

Definition sub1_linear_loop_result (n:nat) (res:nat) (c:nat) :=
  c = sub1_linear_time n.
Hint Unfold sub1_linear_loop_result.

Load "sub1_linear_loop_gen.v".

Next Obligation.
  rename H into SUB1R.
  destruct SUB1R.
  omega.
Qed.

Next Obligation.
  clear H2 am0 am H3 sub1_linear_loop.
  rename H1 into SUB1_RESULT.
  
  unfold sub1_linear_loop_result in *.
  destruct SUB1_RESULT.
  subst an an0 n'.
  unfold sub1_linear_time; fold sub1_linear_time.
  replace (S wildcard' - 1) with wildcard'; omega.
Qed.

