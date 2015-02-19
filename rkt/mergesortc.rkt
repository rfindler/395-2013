#lang at-exp s-exp "tmonad.rkt"

(require "split2.rkt"
         "merge.rkt"
         "isort_insert.rkt")

(provide mergesortc)

(Fixpoint
 mergesortc #:implicit @A{Set} #:implicit @A_cmp{A -> A -> Prop}
 @A_cmp_trans{Transitive A_cmp} @A_cmp_total{Total A_cmp}
 @A_cmp_dec{DecCmp A_cmp} @l{list A} @len{nat} @EQlen{len = length l}
 #:measure "(length l)"
 #:returns @{list A}
 (match (l)
   [(nil) => (<== nil)]
   [(cons x l′)
    => 
    (if (even_odd_dec len)
        (bind ([xs12 (split2 (div2 len) l _)])
              (bind ([xs1′ (mergesortc A_cmp_trans A_cmp_total A_cmp_dec
                                       (fst xs12) (div2 len) _)])
                    (bind ([xs2′ (mergesortc A_cmp_trans A_cmp_total A_cmp_dec
                                             (snd xs12) (div2 len) _)])
                          (bind ([res (merge A_cmp_trans A_cmp_total A_cmp_dec xs1′ xs2′)])
                                (<== res)))))
        (bind ([res′ (mergesortc A_cmp_trans A_cmp_total A_cmp_dec
                                 l′ (pred len) _)])
              (bind ([res (insert A_cmp_trans A_cmp_total A_cmp_dec x res′)])
                    (<== res))))]))
