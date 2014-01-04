Set Implicit Arguments.
Require Import Arith Arith.Even Arith.Div2.
Require Import Omega.

Section btree.
  Variable T : Type.

  Inductive btree : Type :=
    |Empty : btree
    |Node : T -> btree -> btree -> btree.

  Program Fixpoint size (b : btree) : nat :=
    match b with
      |Empty => 0
      |Node x s t => S (plus (size s) (size t))
    end.

  Inductive Braun : btree -> Prop :=
    |EmptyBraun : Braun Empty
    |NodeBraun : forall (s t : btree) (x : T) ,
                   (size t) <= (size s) <= S( size t) ->
                   Braun s -> Braun t ->
                   Braun (Node x s t).

  Fixpoint diff (b : btree) (m : nat) : option nat :=
    match b, m with
      |Empty, 0 => Some 0
      |Node x Empty Empty, 0 => Some 1
      |Node x s1 t1 , S _ => 
       match even_odd_dec m with
         |right H => 
          diff s1 (div2 (m - 1))
         |left H =>
          diff t1 (div2 (m - 2))
       end
      |_ , _ => None
    end.


(*My previous failed attempt at dsize calling diff
  Program Fixpoint dsize (b : btree) (P : Braun(b)) : nat :=
    match b with
      |Empty => 0
      |Node x s t => 
       let m := (dsize _(t)) in
       (1 + 2 * m + (diff s m))
    end.
*)


End btree.

Implicit Arguments Empty [T].
Implicit Arguments Node [T].

Program Example diff1 :
  (diff (Node 1 
              (Node 2 
                    (Node 3 Empty Empty) 
                    Empty)
              (Node 4 Empty Empty))
        3)
  = Some 1.
compute;reflexivity.
Qed.

Program Example diff2 :
  (diff (Node 1 
              (Node 2 Empty Empty)
              (Node 3 Empty Empty))
        3)
  = Some 0.
compute;reflexivity.
Qed.
