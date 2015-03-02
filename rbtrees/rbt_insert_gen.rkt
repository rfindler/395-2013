#lang at-exp s-exp tmonad/overly-specific
(require "rbt_insert_inner_gen.rkt" "rbt_blacken_gen.rkt")

(Fixpoint
 rbt_insert
 @A{Set}
 @A_cmp{A -> A -> Prop}
 @A_refl{forall x, A_cmp x x}
 @A_asym{forall x y, A_cmp x y -> ~ A_cmp y x}
 @A_trans{Transitive A A_cmp}
 @A_cmp_dec{forall (x y:A),
            { A_cmp x y } + { A_cmp y x }}
 @A_eq_dec{forall (x y:A), { x = y } + { x <> y }}
 @ct{CTree A} @x{A}
 #:returns @{CTree A}
 (bind 
  ((ctp (rbt_insert_inner A A_cmp A_refl A_asym A_trans A_cmp_dec A_eq_dec ct x)))
  (bind 
   ((res (rbt_blacken A ctp)))
   (<== res))))
