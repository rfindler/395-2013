#reader "tmonad-coq.rkt"

Provide insert.

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
