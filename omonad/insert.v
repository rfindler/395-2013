Set Implicit Arguments.

Require Import Braun.common.log Braun.common.util.
Require Import Braun.omonad.braun Braun.omonad.monad.
Require Import Coq.Logic.JMeq Coq.Program.Wf.
Require Import Arith Arith.Even Arith.Div2.
Require Import Omega.

Program Fixpoint insert (A:Set) n (x:A) (b : braun_tree A n)
: C (braun_tree A (n+1)) (cl_log (n+1)) :=
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

Obligation 4.
replace (t_size+1) with (S t_size);[|omega].
replace (s_size+t_size+1+1) with (S (s_size+t_size+1));[|omega].
rewrite <- fl_log_cl_log_relationship.
rewrite <- fl_log_cl_log_relationship.
rewrite <- braun_invariant_implies_fl_log_property; [|omega].
omega.
Qed.
