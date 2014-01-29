Require Import Braun.common.braun Braun.common.util Braun.common.same_structure.
Require Import Braun.common.log Braun.logical.sequence Braun.logical.list_util.
Require Import Braun.tmonad.monad.
Require Import Program List.
Require Import Omega.

Section foldr.
  Variables A B : Set.
  Variable P : B -> (list A) -> nat -> Prop.

  Definition f_type := forall (x:A) (acc:B),
                    {! acc' !:! B !<! c !>!
                       forall xs accC,
                         P acc         xs       accC -> 
                         P acc' (x :: xs) (c + accC + 11) !}.

  Definition foldr_result 
             (f : f_type)
             (base : B)
             (PFbase : P base nil 3)
             l
             (res:B)
             (c : nat) := P res l c.

  Load "fold_gen.v".

  Next Obligation.
    unfold foldr_result.
    replace (xn0 + (xn + 11)) with (xn + xn0 + 11); try omega.
    auto.
  Defined.

End foldr.

Hint Unfold foldr_result.

Arguments foldr [A] [B] P f base PFbase l.

Program Definition sum (l:list nat)
: {! n !:! nat !<! c !>! 
     (forall x, In x l -> x <= n)
     /\ c = 12 * length l + 3 !} 
  :=
    n <- (foldr (fun b al n => 
                   (forall x, In x al -> x <= b)
                   /\ n = 12 * length al + 3)
                (fun x y => ++; <== plus x y)
                0 _ l) ;
    <== n.

Next Obligation.
  split; [| omega].
  intros; destruct H0; try omega.
  remember (H x0 H0).
  omega.
Qed.
Next Obligation.
  tauto.
Qed.

Next Obligation.
  unfold foldr_result in *.
  split.
  tauto.
  omega.
Qed.

(* example use of foldr *)
Program Definition list_id (A : Set) (l : list A) : {! l' !:! list A !<! c !>!
                                                       l' = l !} :=
  foldr (fun xs ys n => xs = ys)
        (fun x ys => <== (cons x ys))
        nil 
        _
        l.
