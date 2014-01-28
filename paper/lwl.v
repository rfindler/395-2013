Require Import Arith Omega Braun.common.util.
Require Import Coq.Logic.JMeq Coq.Program.Wf.

Section sl.

  Variable A:Set.

  (* START: list_with_len *)
  Inductive list_with_len : nat -> Type :=
  | empty : list_with_len 0
  | cons (tl_len : nat) 
         (hd : A)
         (tl : list_with_len tl_len) 
    : (list_with_len (tl_len+1)).
  (* STOP: list_with_len *)

  (* START: drop *)
  Program Fixpoint drop (n : nat)
                        (len : nat)
                        (l : list_with_len len)
  : list_with_len (if (le_dec n len)
                   then (len - n)
                   else 0) 
    := if zerop n
       then l
       else match l with
              | empty => empty
              | (cons _ hd tl) => 
                drop (n-1) (len-1) tl
            end.
  (* STOP: drop *)
  
  Next Obligation.
    dispatch_if x x';[omega|intuition].
  Qed.
  
  Next Obligation.
  Proof.
    dispatch_if x x'; omega.
  Qed.

  Next Obligation.
  Proof.
    omega.
  Qed.

  Next Obligation.
  Proof.
    dispatch_if x x'; dispatch_if y y'; omega.
  Qed.  
End sl.

(*
(* START: obligation2 *)
   forall len n, 
     len = 0 -> 
     0 = (if (le_dec n len)
          then (len - n)
          else 0)
(* STOP: obligation2 *)
*)


(*
(* START: obligation4 *)
   forall tl len n, 
     (length tl)+1 = len ->
     (if le_dec (n - 1) (len - 1) 
      then len - 1 - (n - 1) 
      else 0) 
     =
     (if le_dec n ((length tl) + 1) 
      then (length tl) + 1 - n
      else 0)
(* STOP: obligation4 *)
*)

(*
Extraction Implicit drop [len].
Extraction Implicit cons [tl_len].
Recursive Extraction drop.

signals the error:

Error: The 3rd argument (len) of drop still occurs after extraction.
Please check the Extraction Implicit declarations.
*)
