#lang at-exp s-exp tmonad/overly-specific
(require "diff_gen.rkt")
(provide size)

(Fixpoint
 size #:implicit @A{Set} @b{@"@"bin_tree A}
 #:returns @{nat}
 (match (b)
   [(bt_mt) => (<== 0)]
   [(bt_node _ s t) 
    =>
    (bind ((m (size t)))
          (bind ((zo (diff s m)))
                (<== (+ 1 (* 2 m) zo))))]))

