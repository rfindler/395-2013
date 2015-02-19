#lang at-exp s-exp "tmonad.rkt"

(require "mergesortc.rkt" "clength.rkt")

(Fixpoint
 mergesort #:implicit @A{Set} #:implicit @A_cmp{A -> A -> Prop}
 @A_cmp_trans{Transitive A_cmp} @A_cmp_total{Total A_cmp}
 @A_cmp_dec{DecCmp A_cmp} @l{list A}
 #:returns @{list A}
 (bind ((len (clength l)))
       (bind ((res (mergesortc A_cmp_trans A_cmp_total A_cmp_dec l len _)))
             (<== res))))
