#lang at-exp s-exp "tmonad.rkt"

(require "sub1.rkt")
(provide copy_linear_sub1)
(Fixpoint
 copy_linear_sub1 @n{nat}
 #:measure n
 #:returns @{nat}
 (match (n)
   [0 => (<== 0)]
   [(S _)
    => 
    (bind ((l (copy_linear_sub1 (div2 n))))
          (bind ((nn (sub1 n)))
                (bind ((r (copy_linear_sub1 (div2 nn))))
                      (<== 0))))]))
