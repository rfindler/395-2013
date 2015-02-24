#lang at-exp s-exp tmonad
(provide rbt_insert_inner)
(require "rbt_balance_gen.rkt")

(Fixpoint
 rbt_insert_inner #:implicit @A{Set}
 @A_cmp{A -> A -> Prop}
 @A_asym{forall x y, A_cmp x y -> ~ A_cmp y x}
 @A_trans{Transitive A A_cmp}
 @A_cmp_dec{forall (x y:A),
            { A_cmp x y } + { A_cmp y x }}
 @A_eq_dec{forall (x y:A), { x = y } + { x <> y }}
 @ct{CTree A} @x{A}
 #:returns @{CTree A}
 (match (ct)
   [(CT_leaf)
    =>
    (<== (CT_node ct RED x ct))]
   [(CT_node l c v r)
    =>
    (match ((A_eq_dec x v))
      [(left _)
       =>
       (<== ct)]
      [(right _)
       =>
       (match ((A_cmp_dec x v))
         [(left _)
          =>
          (bind 
           ((lp (rbt_insert_inner A_cmp A_asym A_trans A_cmp_dec A_eq_dec l x)))
           (bind 
            ((res (rbt_balance lp c x r)))
            (<== res)))]
         [(right _)
          =>
          (bind 
           ((rp (rbt_insert_inner A_cmp A_asym A_trans A_cmp_dec A_eq_dec r x)))
           (bind 
            ((res (rbt_balance l c x rp)))
            (<== res)))])])]))
