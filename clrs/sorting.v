Require Import List.
Require Import Sorting.Sorted Sorting.Permutation.

Definition IsSorted {A:Set} (A_cmp:A -> A -> Prop) (l:list A) :=
  (@StronglySorted A A_cmp l).

Definition SortedOf {A:Set} (A_cmp:A -> A -> Prop) (l l':list A) :=
  (@Permutation A l l') /\
  (@IsSorted A A_cmp l').

Definition DecCmp {A:Set} (A_cmp:A -> A -> Prop) :=
  forall x y,
    {A_cmp x y} + {~ A_cmp x y}.

Definition Total {A:Set} (A_cmp:A -> A -> Prop) :=
  forall x y,
    (~ A_cmp x y) ->
    A_cmp y x.

Lemma Permutation_cons_step:
  forall A (a a':A) x y,
    Permutation (a :: x) y ->
    Permutation (a :: a' :: x) (a' :: y).
Proof.
  intros. rename H into PM.
  eapply Permutation_trans.
  apply perm_swap.
  apply perm_skip.
  auto.
Qed.

