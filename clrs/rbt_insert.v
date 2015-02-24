Require Import Braun.common.util Braun.common.le_util Braun.common.same_structure.
Require Import Braun.common.log Braun.common.big_oh Braun.common.pow.
Require Import Braun.monad.monad.
Require Import Program.
Require Import Omega.
Require Import Max.
Require Import Div2.
Require Import Relations_1.
Require Import Braun.clrs.rbtree.

Definition SameMembers {A:Set} (x:CTree A) (y:CTree A) :=
  forall e,
    IsMember e x <-> IsMember e y.

Lemma SameMembers_refl:
  forall A (x:CTree A),
    SameMembers x x.
Proof.
  intros A x e. intuition.
Qed.

Lemma SameMembers_child:
  forall A (l r:CTree A) v c1 c2,
    SameMembers (CT_node A l c1 v r) (CT_node A l c2 v r).
Proof.
  intros. split; intros IM; inversion IM; subst; eauto.
Qed.

Definition rbt_blacken_worst := 8.
Definition rbt_blacken_best := 3.

Definition rbt_blacken_result (A:Set) (ct:CTree A) (res:CTree A) (c:nat) :=
  (forall n,
    IsRB ct n ->
    IsRB res n \/ IsRB res (S n)) /\
  (IsColor res BLACK) /\
  (forall A_cmp min max,
    IsBST A_cmp ct min max ->
    IsBST A_cmp res min max) /\
  (SameMembers ct res) /\
  (rbt_blacken_best <= c <= rbt_blacken_worst).

Load "rbt_blacken_gen.v".

Next Obligation.
  unfold rbt_blacken_result.
  split. intuition.
  split. auto.
  split. intuition.
  split. apply SameMembers_refl.
  unfold rbt_blacken_best, rbt_blacken_worst.
  omega.
Qed.

Next Obligation.
  unfold rbt_blacken_result.
  split. apply blacken_okay.
  split. auto.
  split.
   intros A_cmp min max BST.
   inversion BST. subst. eauto.
  split. apply SameMembers_child.
  unfold rbt_blacken_best, rbt_blacken_worst.
  omega.
Qed.

Definition rbt_balance_worst := 42.
Definition rbt_balance_best := 8.

Definition rbt_balance_result (A:Set) (tl:CTree A) (tc:Color) (tv:A) (tr:CTree A)
  (res:CTree A) (c:nat) :=
  True /\
  (rbt_balance_best <= c <= rbt_balance_worst).

Load "rbt_balance_gen.v".

Solve Obligations using
  unfold rbt_balance_result, rbt_balance_best, rbt_balance_worst;
    split; [ auto | omega ].

Solve Obligations using program_simpl.

(* 115 obligations later! *)

Definition rbt_insert_time (n:nat) :=
  19 * n + 3.

Definition rbt_insert_result (A:Set)
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
    1 <= c <= rbt_insert_time (height ct).

(*  *)
(* Load "rbt_insert_inner_gen.v". *)
(* Load "rbt_insert_gen.v". *)

(* Admit Obligations. *)
