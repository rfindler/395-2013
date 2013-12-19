Require Import braun util monad2.
Set Implicit Arguments.

Program Fixpoint size_linear A n (b : braun_tree A n) : C nat n :=
  match b with
    | Empty => ret 0
    | Node y s_size t_size p s t =>
      (++ 1;
       s_sz <- size_linear s;
       t_sz <- size_linear t;
       ret (s_sz + t_sz + 1))
  end.
