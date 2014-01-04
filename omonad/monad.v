Set Implicit Arguments.

Require Import Braun.omonad.braun Braun.common.util.
Require Import Coq.Logic.JMeq Coq.Program.Wf.
Require Import Arith Arith.Even Arith.Div2.
Require Import Omega.
Require Import Program.Syntax.

Inductive time_of : nat -> Type := 
  Time : forall n, time_of n.

Definition C (s: Set) (n:nat) : Set := (s * time_of n)%type. 

Definition bind A B n n' (xn: C A n) (y: A -> C B n'): C B (n+n') :=
  match xn with
    | (x,tn) =>
      match tn in time_of n with
        | Time n =>
          match y x with
            | (r,tn') =>
              match tn' in time_of n' with
                | Time n' =>
                  (r,Time (n+n'))
              end
          end
      end
  end.

Definition ret (A: Set) (x: A): C A 0 := (x,Time 0).

Definition inc (A : Set) n (k : nat) (x : C A n) : C A (n+k) :=
  match x with
    | (v,tn) =>
      match tn in time_of n with
        | Time n =>
          (v, Time (n+k))
      end
  end.

Notation "x >>= y" := (bind x y) (at level 55).
Notation "x >> y" := (bind x (fun _ => y)) (at level 30, right associativity).
Notation "x <- y ; z" := (bind y (fun x : _ => z)) (at level 30, right associativity).
Notation "++ k ; c" := (inc k c) (at level 30, right associativity).
