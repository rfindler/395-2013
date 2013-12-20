(*
Following the ideas from
  Coq-Formalized Proofs of Quicksort's Average-case Complexity
  By Eelis van der Weegen and James McKinna, TYPES 2008
  paper:
  http://github.com/Eelis/qs-avg/raw/f0535088e7f1b7d7fc0d5ac06867a09a1c282f94/papers/TYPES08/published.pdf

  code: https://github.com/Eelis/qs-avg
*)


Set Implicit Arguments.

Require Import Arith Omega Coq.Logic.JMeq.

Definition C (s: Set): Set := (s * nat)%type. 

Definition bind A B (xn: C A) (y: A -> C B): C B :=
  match xn with
    | (x,n) =>
      match y x with
        | (r,n') => (r,n+n')
      end
  end.
Definition ret (A: Set) (x: A): C A := (x,0).

Definition inc (A : Set) (k : nat) (x : C A) : C A :=
  match x with
    | (v,n) => (v, n+k)
  end.

Definition time := snd.

Module MonadLaws.

  (* (return x >>= f) = (f x) *)
  Theorem mon_lunit: 
    forall (a b: Set) (x: a)
           (f: a -> C b), 
      bind (ret x) f = f x.

    intros; unfold bind; unfold ret.
    destruct (f x).
    simpl.
    reflexivity.
  Qed.

  (* (f >>= return) = f *)
  Theorem mon_runit: forall (a: Set) (f: C a), bind f (@ret a) = f.
    intros; unfold bind; unfold ret.
    destruct f.
    rewrite plus_0_r; reflexivity.
  Qed.

  (* ((n >>= f) >>= g) = n >>= (\x -> f x >>= g) *)
  Theorem mon_assoc: forall a b c (n: C a) (f: a -> C b) (g: b -> C c),
      bind (bind n f) g =
      bind n (fun x => bind (f x) g).
    intros; unfold bind.
    destruct n; destruct (f a0); destruct (g b0).
    rewrite plus_assoc; reflexivity.
  Qed.

End MonadLaws.

Notation "x >>= y" := (bind x y) (at level 55).
Notation "x >> y" := (bind x (fun _ => y)) (at level 30, right associativity).
Notation "x <- y ; z" := (bind y (fun x : _ => z)) (at level 30, right associativity).
Notation "++ k ; c" := (inc k c) (at level 30, right associativity).
