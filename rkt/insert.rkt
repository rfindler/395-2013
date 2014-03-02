#reader "tmonad-coq.rkt"

Provide insert.

(*

This language contains 'Fixpoint' 'Provide' and
expressions of the shape below.

It implicitly defines a main module that emits
the corresponding Coq code and the functions, when
used back in regular racket (say 'insert') return two
values: the result of the function and the step count.

;; An exp is one of:
;;  (match (<exp> ...) (<pat> <pat> ... => <exp) ...)
;;  (if <exp> <exp> <exp>)
;;  (bind ([<id> <exp>]) <exp>) -- bind in the monad
;;  (<mnid> <exp> ...)   -- call to a function that doesn't return something in the monad
;;  (<id> <exp> ...)     -- call to a function that returns        something in the monad
;;  (<== <exp>)
;;  <id>
;;  <constant>

;; A pat is either:
;;  <id>
;;  (<id> <id> ...)

*)

(* START: insert *)
Program Fixpoint insert {A:Set} (i:A) 
                        (b:@bin_tree A) 
: @bin_tree A :=
match b with
 | bt_mt => 
   <== bt_node i bt_mt bt_mt
 | bt_node j s t => 
   bt <- insert j t;
   <== bt_node i bt s
end.
(* STOP: insert *)
