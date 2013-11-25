Require Import braun Omega Coq.Logic.JMeq.
Set Implicit Arguments.

Program Fixpoint insert A n (x:A)
        (b : braun_tree A n)
: braun_tree A (n+1) :=
  match b with
    | Empty => Node x 0 0 _ Empty Empty
    | Node y s_size t_size p s t => 
      Node x (t_size+1) s_size _ (insert y t) s
  end.

Solve Obligations using (intros;omega).
