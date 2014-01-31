#lang at-exp s-exp "tmonad.rkt"

(provide diff)

(Fixpoint
 diff #:implicit @A{Set} @b{@"@"bin_tree A} @m{nat}
 #:measure m
 #:returns @{nat}
 (match (b m)
   [(bt_mt) _ => (<== 0)]
   [(bt_node x _ _) 0 => (<== 1)]
   [(bt_node x s t) 
    (S m′) 
    =>
    (if (even_odd_dec m)
        (bind ((o (diff t (div2 (- m′ 1)))))
              (<== o))
        (bind ((o (diff s (div2 m′))))
              (<== o)))]))
