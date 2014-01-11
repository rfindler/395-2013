Require Import Arith Arith.Even Arith.Div2.
Require Import Braun.common.util.
Set Implicit Arguments.

Inductive bin_tree {A:Set} : Set :=
| bt_mt : bin_tree
| bt_node : A -> bin_tree -> bin_tree -> bin_tree.
Hint Constructors bin_tree.

Inductive Braun {A:Set} : (@bin_tree A) -> nat -> Prop :=
| B_mt :
    Braun bt_mt 0
| B_node :
    forall (x:A) s s_size t t_size,
      t_size <= s_size <= t_size+1 ->
      Braun s s_size ->
      Braun t t_size ->
      Braun (bt_node x s t) (s_size+t_size+1).
Hint Constructors Braun.

Lemma braun_node_construction:
  forall (A:Set) (x:A) n s t,
    Braun s (div2 (n+1)) ->
    Braun t (div2 n) ->
    Braun (bt_node x s t) (S n).
Proof.
  intros.
  replace (S n) with (div2 (n+1) + div2 n + 1).
  constructor; auto.
  apply (ind_0_1_SS (fun n => div2 n <= div2 (n+1) <= div2 n + 1));
    try (intros;simpl;omega).
  rewrite div_ceil_floor_sum. 
  replace (S n + 1) with (S (S n));[|omega].
  replace (div2 (S (S n))) with (S (div2 n));[|simpl;reflexivity].
  replace (n+1) with (S n);[|omega].
  omega.
Qed.
Hint Resolve braun_node_construction.
