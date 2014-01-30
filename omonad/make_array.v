Require Import Braun.common.le_util Braun.common.log.
Require Import Braun.omonad.braun Braun.omonad.monad Braun.omonad.insert.
Require Import Braun.common.array.
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

Fixpoint man_time n : nat :=
  match n with
    | 0 => 0
    | S n' => man_time n' + (cl_log n)
  end.

Section make_array_naive.
  Variable A : Set.
  
  Program Definition make_array_naive n (s : ilist A n)
  : C (braun_tree A n) (man_time n) :=
    ifoldr (fun n => C (braun_tree A n) (man_time n))
           (fun n x ct => ct >>= insert x)
           (ret Empty)
           s.
  Obligation 1. omega. Qed.
  Obligation 2.
  replace (n0 + 1) with (S n0);[reflexivity|omega]. 
  Qed.

End make_array_naive.
