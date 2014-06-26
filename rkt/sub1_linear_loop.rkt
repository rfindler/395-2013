#lang at-exp s-exp "tmonad.rkt"
(require "sub1.rkt")
(provide sub1_linear_loop)

(Fixpoint
 sub1_linear_loop @n{nat}
 #:measure n
 #:returns @{nat}
 (match (n)
   [0 => (<== 0)]
   [(S _)
    =>
    (bind ([n′ (sub1 n)])
          (bind ([res (sub1_linear_loop n′)])
                (<== res)))]))