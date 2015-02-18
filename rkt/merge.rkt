#lang at-exp s-exp "tmonad.rkt"

(provide merge)

(Fixpoint
 merge #:implicit @A{Set}
 #:implicit @A_cmp{A -> A -> Prop}
 @A_cmp_trans{Transitive A_cmp} @A_cmp_total{Total A_cmp} @A_cmp_dec{DecCmp A_cmp}
 @xs{list A} @ys{list A}
 #:measure "(length (xs ++ ys))"
 #:returns @{list A}
 (match (xs)
   [(nil) => (<== ys)]
   [(cons x xs′)
    =>
    (match (ys)
      [(nil) => (<== xs)]
      [(cons y ys′)
       =>
       (match ((A_cmp_dec x y))
         [(left _) 
          => 
          (bind ((res (merge A_cmp_trans A_cmp_total A_cmp_dec xs′ ys)))
                (<== (cons x res)))]
         [(right _) 
          => 
          (bind ((res (merge A_cmp_trans A_cmp_total A_cmp_dec xs ys′)))
                (<== (cons y res)))])])]))
