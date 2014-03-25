#lang at-exp s-exp "tmonad.rkt"

(provide diff_sub1)
(require "sub1.rkt")

(Fixpoint
 diff_sub1 @n{nat} @m{nat}
 #:measure m
 #:returns @{nat}
 (match (n m)
   [0     _ => (<== 0)]
   [(S _) 0 => (<== 1)]
   [(S _) (S _) 
    =>
    (if (even_odd_dec m)
        (bind ([mm (sub1 m)])
              (bind ([mmm (sub1 mm)])
                    (bind ((o (diff_sub1 (div2 n) (div2 mmm))))
                          (<== o))))
        (bind ([mm (sub1 m)])
              (bind ((o (diff_sub1 (div2 (- n 1)) (div2 mm))))
              (<== o))))]))
