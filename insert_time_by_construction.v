Set Implicit Arguments.

Require Import braun util monad2 fl_log.
Require Import Coq.Logic.JMeq Coq.Program.Wf.
Require Import Arith Arith.Even Arith.Div2.
Require Import Omega.

Program Fixpoint insert (A:Set) n (x:A) (b : braun_tree A n)
: C (braun_tree A (n+1)) (S (fl_log n)) :=
  match b with
    | Empty =>
      ++1 ;
        ret (Node x 0 0 _ Empty Empty)
    | Node y s_size t_size p s t =>
      st <- (insert y t);
        ++ 1;
        ret (Node x
                  (t_size+1) s_size
                  _
                  st s)
  end.

Solve Obligations using (intros;omega).

Obligation 4.
  assert (s_size = t_size \/ s_size = t_size + 1) as TwoCases;
    [ omega | ].

  inversion TwoCases; subst; clear.
  
  rewrite fl_log_odd.
  reflexivity.

  replace (t_size + 1 + t_size + 1) with ((t_size+1) + (t_size+1)); [| omega].
  rewrite fl_log_even.
  reflexivity.
Qed.
