Require Import Braun.common.braun Braun.common.util Braun.common.same_structure.
Require Import Braun.common.log Braun.logical.sequence Braun.logical.list_util.
Require Import Braun.tmonad.monad.
Require Import Program List.
Require Import Omega.

(* Note: adds a ++ to every recursive call, but not for the base case. Should the base case have a ++ too? *)
Section foldr.
  Variables A B : Set.
  Variable P : B -> (list A) -> nat -> Prop.
  Variable f : forall (x:A) (acc:B),
                 {! acc' !:! B !<! c !>!
                    forall xs accC,
                      P acc         xs           accC -> 
                      P acc' (x :: xs) (c + accC + 1) !}.
  Variable base : B.
  Variable PFbase : P base nil 0.
  Program Fixpoint foldr (l : list A) : {! b' !:! B !<! c !>! P b' l c !} :=
    match l with
      | nil => 
        <== base
      | cons x xs =>
        ++ ;
        acc <- foldr xs;
        out <- f x acc;
        <== out
    end.

  Next Obligation.
    (* I suck at coq :( *)
    assert ((xn0 + (xn + 0) + 1) = xn + xn0 + 1) as Dumb; [omega | rewrite Dumb; clear Dumb].
    auto.
  Defined.

End foldr.

Program Definition sum (l:list nat)
: {! n !:! nat !<! c !>! 
     (forall x, In x l -> x <= n)
     /\ c = length l !} 
  :=
    n <- (foldr nat nat 
                (fun b al n => 
                   (forall x, In x al -> x <= b)
                   /\ n = length al)
                plus 0 _ l) ;
    <== n.

Next Obligation.
  rename l into al.
  rename x into sum.
  rename x0 into c.
  exists 0.
  intros al' bn PF.
  destruct PF as [PF EQ]. subst.
  split; try omega.
  intros x [EQ | IN].
  omega.
  apply PF in IN. omega.
Qed.

Next Obligation.
  tauto.
Qed.

Recursive Extraction sum.

Program Definition list_id (A : Set) (l : list A) : {! l' !:! list A !<! c !>!
                                                       l' = l !} :=
  foldr A
        (list A)
        (fun xs ys n => xs = ys)
        cons
        nil 
        _
        l.
Next Obligation.
  exists 0.
  intros ys _ H.
  rewrite H.
  auto.
Qed.
