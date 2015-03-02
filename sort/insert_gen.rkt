#lang at-exp s-exp tmonad/overly-specific

(provide insert)

(Fixpoint
 insert #:implicit @A{Set} #:implicit @A_cmp{A -> A -> Prop}
 @A_cmp_trans{Transitive A_cmp} @A_cmp_total{Total A_cmp}
 @A_cmp_dec{DecCmp A_cmp} @a{A} @l{list A}
 #:returns @{list A}
 (match (l)
   [(nil) => (<== (cons a nil))]
   [(cons a′ l′)
    => 
    (match ((A_cmp_dec a a′))
      [(left _) => (<== (cons a l))]
      [(right _) 
       => 
       (bind ((res′ (insert A_cmp_trans A_cmp_total A_cmp_dec a l′)))
             (<== (cons a′ res′)))])]))
