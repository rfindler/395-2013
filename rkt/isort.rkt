#lang at-exp s-exp "tmonad.rkt"

(require "isort_insert.rkt")

(Fixpoint
 isort #:implicit @A{Set} #:implicit @A_cmp{A -> A -> Prop}
 @A_cmp_trans{Transitive A_cmp} @A_cmp_total{Total A_cmp}
 @A_cmp_dec{DecCmp A_cmp} @l{list A}
 #:returns @{list A}
 (match (l) 
   [(nil) => (<== nil)]
   [(cons a d)
    =>
    (bind ((d′ (isort A_cmp_trans A_cmp_total A_cmp_dec d)))
          (bind ((r′ (insert A_cmp_trans A_cmp_total A_cmp_dec a d′)))
                (<== r′)))]))
