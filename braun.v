Set Implicit Arguments.

Section braun_tree.

Variable A : Type.

Inductive braun_tree : nat -> Type :=
  | Empty : braun_tree 0
  | Node : forall (x:A) s_size t_size, 
             t_size <= s_size <= t_size+1 ->
             braun_tree s_size -> braun_tree t_size ->
             braun_tree (s_size+t_size+1).

End braun_tree.

Implicit Arguments Empty [A].
Implicit Arguments Node [A].

