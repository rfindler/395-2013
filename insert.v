Set Implicit Arguments.

Require Import braun util monad fl_log.
Require Import Coq.Logic.JMeq Coq.Program.Wf.
Require Import Arith Arith.Even Arith.Div2.
Require Import Omega.

Program Fixpoint insert (A:Set) n (x:A) (b : braun_tree A n)
: C (braun_tree A (n+1)) (fl_log n + 1) :=
  match b with
    | Empty =>
      (++1 ;
       ret (Node x 0 0 _ Empty Empty))
    | Node y s_size t_size p s t =>
      (st <- (insert y t);
       ++ 1;
       ret (Node x
                 (t_size+1) s_size
                 _
                 st s))
  end.

Solve Obligations using (intros;omega).

Obligation 2.
apply braun_invariant_implies_fl_log_property.
omega.
Qed.
