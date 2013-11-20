Require Import braun CpdtTactics.
Set Implicit Arguments.

Program Fixpoint insert A n (x:A)
        (b : braun_tree A n)
: braun_tree A (n+1) :=
  match b with
    | Empty => Node x 0 0 _ Empty Empty
    | Node y s_size t_size p s t => 
      Node x (t_size+1) s_size _ (insert y t) s
  end.

Obligation 2. omega. Qed.
Obligation 3. omega. Qed.

