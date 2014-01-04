Require Import Braun.omonad.braun Braun.omonad.monad Braun.omonad.log 
        Braun.omonad.insert Braun.omonad.le_util.
Require Import Program.Equality Omega.
Require Import Div2 List.
Set Implicit Arguments.

Section ilist.
  Variable A : Set.
  Variable P : nat -> Set.

  Inductive ilist : nat -> Set :=
  | Nil  : ilist 0
  | Cons : forall n, A -> ilist n -> ilist (S n).
End ilist.

Section ifoldr.
  Variables A : Set.
  Variable B : nat -> Set.
  Variable f : forall n, A -> B n -> B (S n).
  Variable i : B 0.

  Fixpoint ifoldr n (ls : ilist A n) : B n :=
    match ls with
      | Nil => i
      | Cons _ x ls' => f x (ifoldr ls')
    end.
End ifoldr.

Section make_array_naive.
  Variable A : Set.

  (* Not sure how to prove this is O(nlogn) *)
  Fixpoint rt_naive n : nat :=
    match n with
      | 0 => 0
      | S n' => rt_naive n' + (cl_log n)
    end.

  Example rt_naive_ex :
    map rt_naive (1 :: 2 :: 3 :: 4 ::  5 ::  6 ::  7 ::  8 ::  9 :: 10 :: nil)
               = (1 :: 3 :: 5 :: 8 :: 11 :: 14 :: 17 :: 21 :: 25 :: 29 :: nil).
  compute; reflexivity. Qed.
  
  Program Definition make_array_naive n (s : ilist A n)
  : C (braun_tree A n) (rt_naive n) :=
    ifoldr (fun n => C (braun_tree A n) (rt_naive n))
           (fun n x ct => ct >>= insert x)
           (ret Empty)
           s.
  Obligation 1. omega. Qed.
  Obligation 2. 
  replace (n0 + 1) with (S n0);[reflexivity|omega]. 
  Qed.

  Lemma rt_naive_is_nlogn : forall n, rt_naive n <= n * cl_log n.
    apply (well_founded_ind 
             lt_wf 
             (fun n => rt_naive n <= n * cl_log n)).
    intros x IND.
    destruct x.
    compute; constructor.
    replace (rt_naive (S x)) with (rt_naive x + cl_log (S x));[|simpl;reflexivity].
    replace (S x * cl_log (S x)) with (cl_log (S x) + x * cl_log (S x));[|simpl;omega].
    rewrite plus_comm.
    apply le_plus_right.
    apply (le_trans (rt_naive x) 
                    (x * cl_log x)
                    (x * cl_log (S x))).
    apply IND.
    constructor.
    apply le_mult_right.
    apply cl_log_monotone.
  Qed.

End make_array_naive.
