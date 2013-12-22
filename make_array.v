Require Import braun monad fl_log insert.
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
      | S n' => rt_naive n' + (fl_log n' + 1)
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

End make_array_naive.
