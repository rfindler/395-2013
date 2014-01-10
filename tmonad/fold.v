Require Import Braun.common.braun Braun.common.util Braun.common.same_structure.
Require Import Braun.common.log Braun.logical.sequence Braun.logical.list_util.
Require Import Braun.tmonad.monad.
Require Import Program List.
Require Import Omega.

Program Fixpoint foldr (A:Set) (B:Set) (PF:B -> (list A) -> nat -> Prop)
  (f:forall (a:A) (b:B),
       C B 
         (fun b' b'n => 
            forall al bn,
              PF b al bn ->
              PF b' (a :: al) (bn+b'n)))
  (b:B) (PFb0:PF b nil 0) (al:list A) : 
  {! b' !:! B !<! c !>! PF b' al c !} :=
  match al with
    | nil =>
      <== b
    | cons a al =>
      ++ ; 
      b'  <- (f a b) ;
      b'' <- foldr A B (fun b al n => exists b'n, PF b (cons a al) (n+b'n)) f b' _ al ;
      <== b''
  end.

Next Obligation.
  rename H into IH.
  rename x into a'.
  rename x0 into b''.
  apply IH in PFb0.
  exists xm.
  intros al bn.
  intros [b'n PFb''].
  exists b'n.

  (* XXX broken *)
  admit.
Qed.
  
Admit Obligations.

Program Fixpoint sum (l:list nat)
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
  exists 1.
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
