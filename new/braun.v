Set Implicit Arguments.

Section braun.
  Variable A : Set.

  Inductive bin_tree : Set :=
  | bt_mt : bin_tree
  | bt_node : A -> bin_tree -> bin_tree -> bin_tree.
  Hint Constructors bin_tree.
  
  Inductive Braun : bin_tree -> nat -> Prop :=
  | B_mt :
      Braun bt_mt 0
  | B_node :
      forall (x:A) s s_size t t_size,
        t_size <= s_size <= t_size+1 ->
        Braun s s_size ->
        Braun t t_size ->
        Braun (bt_node x s t) (s_size+t_size+1).
  Hint Constructors Braun.
  
End braun.
