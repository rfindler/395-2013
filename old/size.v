Require Import braun util monad.
Require Import Coq.Logic.JMeq Coq.Program.Wf.
Require Import Arith Arith.Even Arith.Div2.
Require Import Omega.
Require Import Program.Syntax.
Set Implicit Arguments.

(*size implemented with the implementation of braun_trees from braun.v*)

(*size without monads*)
Program Fixpoint size A n (b : braun_tree A n) : nat :=
  match b with
    |Empty => 0
    |Node y s_size t_size p s t => 
     1 + size s + size t
  end.

Program Example size_example1 :
  size (Node 1 0 0 _ Empty Empty)
       = 1.
compute;reflexivity.

Program Example size_example2 :
  size (Node 1 2 1 _ 
             (Node 2 1 0 _ 
                   (Node 3 0 0 _ Empty Empty) 
                   Empty)
             (Node 4 0 0 _ Empty Empty))
       = 4.
compute;reflexivity.

(*size done with counting monad*)
Program Fixpoint sizem A n (b : braun_tree A n):
  C (nat) :=
  match b with
    |Empty => ret 0
    |Node y s_size t_size p s t =>
     s_sz <- sizem s;
       t_sz <- sizem t;
       ++ 1;
       ret (S (s_sz + t_sz))
  end.

Program Example sizem_ex1 :
  time(sizem (Node 1 2 1 _ 
                   (Node 2 1 0 _ 
                         (Node 3 0 0 _ Empty Empty) 
                         Empty)
                   (Node 4 0 0 _ Empty Empty)))
  =4.
compute;reflexivity.

Program Example sizem_ex2 :
  fst(sizem (Node 1 2 1 _ 
                  (Node 2 1 0 _ 
                        (Node 3 0 0 _ Empty Empty) 
                        Empty)
                  (Node 4 0 0 _ Empty Empty)))
  =4.
compute;reflexivity.

Theorem size_runtime_linear: forall (A:Set) n (x:A)
                             (b : braun_tree A n),
                        time (sizem b) = 
                        fst (sizem b).
  intros.
  induction b;intros;simpl.
  reflexivity.
  unfold bind.
  remember (sizem b2) as t eqn:TEQ.
  destruct t.
  remember (sizem b1) as t2 eqn:T2EQ.
  destruct t2.

  compute.
  fold plus.
  assert (n = n0) as H2; auto.
  assert (n1 = n2) as H3; auto.
  rewrite H2,H3.
  omega.
Qed.

(*This is the diff function we developed in class 12/3*)

Definition diff : forall A n (b : braun_tree A n) (m : nat) (P : m <= n <= m+1), nat .
  refine (fun A => fix diff n (b : braun_tree A n) (m : nat) (P : m <= n <= m+1) : nat  :=
            match b as b in braun_tree _ n with
              |Empty => 0
              |Node _ s1_size t1_size _ s1 t1 => 
               match m with
                 |0 => 1
                 |S m'  => 
                  match even_odd_dec m with
                    |right H => 
                     let k := (div2 (m - 1)) in
                     diff s1_size s1 k _
                    |left H =>
                     let k := (div2 (m - 2)) in
                     diff t1_size t1 k _
                  end
               end
            end).
inversion b.
