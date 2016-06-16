Require Import Braun.monad.monad.

(* START: bind1 *)
Definition bind1 (A:Set) (PA:A -> nat -> Prop)
                 (B:Set) (PB:B -> nat -> Prop)
                 (am:C A PA) (bf:A -> C B PB)
: C B PB.
(* STOP: bind1 *)
Abort.

(* START: bind2 *)
Definition bind2 (A:Set) (PA:A -> nat -> Prop)
                 (B:Set) (PB:B -> nat -> Prop)
                 (am:C A PA) 
                 (bf:A -> C B (fun b bn => forall an, PB b (bn+an)))
: C B PB.
(* STOP: bind2 *)
Abort.

(* START: bind3 *)
Definition bind3 (A:Set) (PA:A -> nat -> Prop)
                 (B:Set) (PB:B -> nat -> Prop)
                 (am:C A PA) 
                 (bf:forall (a:A),
                   C B (fun b bn => forall an, PA a an -> PB b (bn+an)))
: C B PB.
(* STOP: bind3 *)
Abort.
